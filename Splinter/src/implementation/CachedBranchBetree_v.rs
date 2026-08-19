// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::{map::*, multiset::*, set::*};

use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationBranchBetree_v::{
    CompactorInput, read_ref_aus, seq_addrs_to_aus, summary_aus,
};
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::allocation_layer::Likes_v::{AULikes, Likes, to_au_likes};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferOffsets_v::BufferOffsets;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Buffer_v::Buffer;
use crate::betree::Domain_v::total_domain;
use crate::betree::LinkedBetree_v::{
    Addrs, BetreeNode, PathAddrs, SplitAddrs, TwoAddrs,
};
use crate::betree::LinkedBranch_v::SplitArg;
use crate::betree::LinkedBranch_v::{
    DiskView as BranchDiskView, LinkedBranch,
};
use crate::betree::LinkedSeq_v::LinkedSeq;
use crate::betree::Memtable_v::Memtable;
use crate::betree::PivotTable_v::domain_to_pivots;
use crate::betree::SplitRequest_v::SplitRequest;
use crate::disk::GenericDisk_v::{
    AU, Address, Pointer, seq_addrs_disjoint_aus, to_aus,
};
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::CachedBranch_v::{
    CachedBranch, LoadedBranch, LoadedPathReceipt,
};
use crate::implementation::CachedBulkBranch_v::{
    CachedBulkBranch, CachedBulkBranchEvent,
    cached_bulk_branch_alloc_aus,
    cached_bulk_branch_alloc_aus_push_subset,
    cached_bulk_branch_alloc_aus_remove_subset,
    cached_bulk_branch_alloc_aus_update_subset,
    cached_bulk_branch_build_all_aus, cached_bulk_branch_fill_all_aus,
};
use crate::spec::KeyType_t::{Key, to_element};
use crate::spec::Messages_t::{Message, Value, default_value, nop_delta};

verus! {

pub type LoadedBetree = Map<Address, BetreeNode>;

pub open spec fn loaded_sealed_branch(
    root: Address,
    reads: LoadedBranch,
) -> LinkedBranch<Summary> {
    LinkedBranch {
        root,
        disk_view: BranchDiskView { entries: reads },
    }
}

pub open spec fn valid_loaded_sealed_branch(
    root: Address,
    summary: Summary,
    reads: LoadedBranch,
) -> bool {
    let branch = loaded_sealed_branch(
        root,
        reads.restrict(addresses_in_aus(summary)),
    );
    &&& branch.valid_sealed_branch()
    &&& branch.get_summary() == summary
}

pub open spec fn valid_loaded_sealed_branches(
    roots: Set<Address>,
    summaries: Map<AU, Summary>,
    reads: LoadedBranch,
) -> bool {
    &&& forall |root: Address| #[trigger] roots.contains(root) ==> {
        &&& summaries.contains_key(root.au)
        &&& valid_loaded_sealed_branch(
            root,
            summaries[root.au],
            reads.restrict(addresses_in_aus(summaries[root.au])),
        )
    }
    &&& reads.dom() == Set::new(|addr: Address| exists |root: Address|
        roots.contains(root)
        && loaded_sealed_branch(
            root,
            reads.restrict(addresses_in_aus(summaries[root.au])),
        ).disk_view.entries.contains_key(addr))
}

pub open spec fn loaded_branch_reads_for_roots(
    roots: Set<Address>,
    summaries: Map<AU, Summary>,
    reads: LoadedBranch,
) -> LoadedBranch {
    reads.restrict(addresses_in_aus(summary_aus(
        summaries.restrict(to_aus(roots)),
    )))
}

pub struct LoadedBetreePathLine {
    pub addr: Address,
    pub node: BetreeNode,
}

impl LoadedBetreePathLine {
    pub open spec fn wf(self) -> bool {
        self.node.wf()
    }
}

pub struct LoadedBetreePath {
    pub key: Key,
    pub root: Address,
    pub lines: Seq<LoadedBetreePathLine>,
}

impl LoadedBetreePath {
    pub open spec fn wf(self) -> bool {
        &&& self.lines.len() > 0
        &&& self.lines[0].addr == self.root
        &&& forall |i: int| 0 <= i < self.lines.len()
            ==> (#[trigger] self.lines[i]).wf()
        &&& forall |i: int| 0 <= i < self.lines.len()
            ==> (#[trigger] self.lines[i]).node.key_in_domain(self.key)
        &&& forall |i: int| 0 <= i < self.lines.len() - 1
            ==> (#[trigger] self.lines[i]).node.is_index()
        &&& forall |i: int| 0 <= i < self.lines.len() - 1 ==> {
            let line = self.lines[i];
            &&& line.node.child_ptr(self.key) is Some
            &&& line.node.child_ptr(self.key).unwrap()
                == (#[trigger] self.lines[i + 1]).addr
        }
    }

    pub open spec fn needed_addrs(self) -> Set<Address> {
        Set::new(|addr: Address| exists |i: int|
            0 <= i < self.lines.len() && #[trigger] self.lines[i].addr == addr)
    }

    pub open spec fn valid_for(self, root: Pointer, reads: LoadedBetree) -> bool {
        &&& root is Some
        &&& self.root == root.unwrap()
        &&& self.wf()
        &&& self.needed_addrs() <= reads.dom()
        &&& forall |i: int| 0 <= i < self.lines.len() ==> {
            &&& reads.contains_key(self.lines[i].addr)
            &&& #[trigger] reads[self.lines[i].addr] == self.lines[i].node
        }
    }

    pub open spec fn depth(self) -> nat
        recommends self.lines.len() > 0
    {
        (self.lines.len() - 1) as nat
    }

    pub open spec fn target(self) -> LoadedBetreePathLine
        recommends self.lines.len() > 0
    {
        self.lines.last()
    }

    pub open spec fn tail(self) -> LoadedBetreePath
        recommends self.lines.len() > 1
    {
        LoadedBetreePath {
            key: self.key,
            root: self.lines[1].addr,
            lines: self.lines.skip(1),
        }
    }

    pub open spec fn path_addrs(self) -> Seq<Address> {
        Seq::new(self.lines.len(), |i: int| self.lines[i].addr)
    }

    pub open spec fn child_addr(self, child_idx: nat) -> Address
        recommends
            self.lines.len() > 0,
            self.target().node.valid_child_index(child_idx),
            self.target().node.children[child_idx as int] is Some,
    {
        self.target().node.children[child_idx as int].unwrap()
    }
}

pub struct LoadedBetreeQueryReceipt {
    pub path: LoadedBetreePath,
    pub buffer_receipts: Seq<Seq<LoadedPathReceipt>>,
}

pub open spec fn branch_receipts_valid(
    roots: LinkedSeq,
    start: nat,
    receipts: Seq<LoadedPathReceipt>,
    key: Key,
    branch_reads: LoadedBranch,
) -> bool {
    &&& start <= roots.len()
    &&& receipts.len() == roots.len() - start
    &&& forall |i: int| 0 <= i < receipts.len() ==> {
        let receipt = #[trigger] receipts[i];
        let root = roots[start as int + i];
        &&& receipt.key == key
        &&& receipt.valid_for(root, branch_reads)
        &&& receipt.target().node is Leaf
    }
}

pub open spec fn branch_receipts_result(
    receipts: Seq<LoadedPathReceipt>,
    start: int,
) -> Message
    recommends 0 <= start <= receipts.len()
    decreases receipts.len() - start when start <= receipts.len()
{
    if start == receipts.len() {
        Message::Update{delta: nop_delta()}
    } else {
        receipts[start].result().merge(branch_receipts_result(receipts, start + 1))
    }
}

impl LoadedBetreeQueryReceipt {
    pub open spec fn empty_for(key: Key) -> LoadedBetreeQueryReceipt {
        LoadedBetreeQueryReceipt {
            path: LoadedBetreePath {
                key,
                root: Address { au: 0, page: 0 },
                lines: Seq::empty(),
            },
            buffer_receipts: Seq::empty(),
        }
    }

    pub open spec fn valid_for(
        self,
        root: Pointer,
        key: Key,
        betree_reads: LoadedBetree,
        branch_reads: LoadedBranch,
    ) -> bool {
        &&& self.path.key == key
        &&& match root {
            None => {
                &&& self.path.lines.len() == 0
                &&& self.buffer_receipts.len() == 0
            },
            Some(_) => {
                &&& self.path.valid_for(root, betree_reads)
                &&& self.path.target().node.child_ptr(key) is None
                &&& self.buffer_receipts.len() == self.path.lines.len()
                &&& forall |i: int| 0 <= i < self.path.lines.len() ==> {
                    let node = (#[trigger] self.path.lines[i]).node;
                    &&& branch_receipts_valid(
                        node.buffers,
                        node.flushed_ofs(key),
                        self.buffer_receipts[i],
                        key,
                        branch_reads,
                    )
                }
            },
        }
    }

    pub open spec fn result_at(self, i: int) -> Message
        recommends
            self.path.wf(),
            self.buffer_receipts.len() == self.path.lines.len(),
            0 <= i < self.path.lines.len(),
        decreases self.path.lines.len() - i when i < self.path.lines.len()
    {
        let buffered = branch_receipts_result(self.buffer_receipts[i], 0);
        if i == self.path.lines.len() - 1 {
            Message::Define{value: default_value()}.merge(buffered)
        } else {
            self.result_at(i + 1).merge(buffered)
        }
    }

    pub open spec fn result(self) -> Message {
        if self.path.lines.len() == 0 {
            Message::Define { value: default_value() }
        } else {
            self.result_at(0)
        }
    }
}

pub open spec fn replacement_root(
    path: LoadedBetreePath,
    replacement: Address,
    path_addrs: PathAddrs,
) -> Address
    recommends path.lines.len() > 0, path_addrs.len() == path.depth()
{
    if path.depth() == 0 { replacement } else { path_addrs[0] }
}

pub open spec fn substitute_writes(
    path: LoadedBetreePath,
    new_subtree_root: Address,
    replacement_writes: LoadedBetree,
    path_addrs: PathAddrs,
) -> LoadedBetree
    recommends path.lines.len() > 0, path_addrs.len() == path.depth()
    decreases path.lines.len() when path.lines.len() > 0
{
    if path.depth() == 0 {
        replacement_writes
    } else {
        let tail = path.tail();
        let tail_addrs = path_addrs.skip(1);
        let child_root = replacement_root(tail, new_subtree_root, tail_addrs);
        let child_idx = path.lines[0].node.pivots.route(path.key);
        let new_node = BetreeNode {
            children: path.lines[0].node.children.update(child_idx, Some(child_root)),
            ..path.lines[0].node
        };
        substitute_writes(tail, new_subtree_root, replacement_writes, tail_addrs)
            .insert(path_addrs[0], new_node)
    }
}

pub proof fn substitute_writes_dom_subset(
    path: LoadedBetreePath,
    new_subtree_root: Address,
    replacement_writes: LoadedBetree,
    path_addrs: PathAddrs,
)
    requires
        path.lines.len() > 0,
        path_addrs.len() == path.depth(),
    ensures
        substitute_writes(
            path,
            new_subtree_root,
            replacement_writes,
            path_addrs,
        ).dom()
            <= replacement_writes.dom() + path_addrs.to_set(),
    decreases path.depth(),
{
    if path.depth() == 0 {
        assert(path_addrs == Seq::<Address>::empty());
    } else {
        let tail = path.tail();
        let tail_addrs = path_addrs.skip(1);
        substitute_writes_dom_subset(
            tail,
            new_subtree_root,
            replacement_writes,
            tail_addrs,
        );
        assert(path_addrs
            == seq![path_addrs[0]] + tail_addrs);
        crate::betree::Utils_v::
            lemma_to_set_distributes_over_plus(
                seq![path_addrs[0]],
                tail_addrs,
            );
        assert(path_addrs.to_set()
            == set![path_addrs[0]] + tail_addrs.to_set());
    }
}

pub open spec fn path_discard_likes(path: LoadedBetreePath) -> Likes
    recommends path.lines.len() > 0
{
    path.path_addrs().to_multiset()
}

pub open spec fn added_path_likes<A: Addrs>(addrs: A, path_addrs: PathAddrs) -> Likes {
    addrs.repr().to_multiset().add(path_addrs.to_multiset())
}

pub open spec fn direct_buffer_likes(node: BetreeNode) -> Likes {
    node.buffers.addrs.to_multiset()
}

pub open spec fn flush_memtable_writes(
    root: Pointer,
    sealed_root: Address,
    new_root_addr: Address,
    reads: LoadedBetree,
) -> LoadedBetree {
    let memtable_buffer = LinkedSeq{addrs: seq![sealed_root]};
    let new_root = if root is Some {
        reads[root.unwrap()].extend_buffer_seq(memtable_buffer)
    } else {
        BetreeNode::empty_root(total_domain()).extend_buffer_seq(memtable_buffer)
    };
    map![new_root_addr => new_root]
}

pub open spec fn grow_writes(root: Pointer, new_root_addr: Address) -> LoadedBetree {
    map![new_root_addr => BetreeNode {
        buffers: LinkedSeq::empty(),
        pivots: domain_to_pivots(total_domain()),
        children: seq![root],
        flushed: BufferOffsets{offsets: seq![0]},
    }]
}

pub open spec fn split_replacement(
    path: LoadedBetreePath,
    reads: LoadedBetree,
    request: SplitRequest,
    new_addrs: SplitAddrs,
) -> LoadedBetree
    recommends
        path.lines.len() > 0,
        path.target().node.valid_child_index(request.get_child_idx()),
        path.target().node.children[request.get_child_idx() as int] is Some,
        reads.contains_key(path.child_addr(request.get_child_idx())),
{
    let parent = path.target().node;
    let child_idx = request.get_child_idx();
    let child = reads[path.child_addr(child_idx)];
    let (left, right, pivot) = match request {
        SplitRequest::SplitLeaf{child_idx: _, split_key} => {
            let pair = child.split_leaf(split_key);
            (pair.0, pair.1, to_element(split_key))
        }
        SplitRequest::SplitIndex{child_idx: _, child_pivot_idx} => {
            let pair = child.split_index(child_pivot_idx);
            (pair.0, pair.1, child.pivots[child_pivot_idx as int])
        }
    };
    let new_parent = BetreeNode {
        pivots: parent.pivots.insert(child_idx as int + 1, pivot),
        children: parent.children.update(child_idx as int, Some(new_addrs.left))
            .insert(child_idx as int + 1, Some(new_addrs.right)),
        flushed: parent.flushed.dup(child_idx as int),
        ..parent
    };
    map![
        new_addrs.left => left,
        new_addrs.right => right,
        new_addrs.parent => new_parent,
    ]
}

pub open spec fn flush_replacement(
    path: LoadedBetreePath,
    reads: LoadedBetree,
    child_idx: nat,
    buffer_gc: nat,
    new_addrs: TwoAddrs,
) -> LoadedBetree
    recommends
        path.lines.len() > 0,
        path.target().node.valid_child_index(child_idx),
        path.target().node.children[child_idx as int] is Some,
        reads.contains_key(path.child_addr(child_idx)),
{
    let root = path.target().node;
    let child = reads[path.child_addr(child_idx)];
    let flush_upto = root.buffers.len();
    let flushed_ofs = root.flushed.offsets[child_idx as int];
    let flushed_buffers = root.buffers.slice(flushed_ofs as int, flush_upto as int);
    let new_child = child.extend_buffer_seq(flushed_buffers);
    let new_root = BetreeNode {
        buffers: root.buffers.slice(buffer_gc as int, flush_upto as int),
        children: root.children.update(child_idx as int, Some(new_addrs.addr2)),
        flushed: root.flushed.update(child_idx as int, flush_upto).shift_left(buffer_gc),
        ..root
    };
    map![new_addrs.addr1 => new_root, new_addrs.addr2 => new_child]
}

pub open spec fn compact_replacement(
    path: LoadedBetreePath,
    start: nat,
    end: nat,
    sealed_root: Address,
    new_addrs: TwoAddrs,
) -> LoadedBetree
    recommends path.lines.len() > 0
{
    let root = path.target().node;
    let new_root = BetreeNode {
        buffers: root.buffers.update_subrange(start as int, end as int, sealed_root),
        flushed: root.flushed.adjust_compact(start as int, end as int),
        ..root
    };
    map![new_addrs.addr1 => new_root]
}

pub struct CachedAllocationBranch {
    pub branch: CachedBranch::State,
    pub staged_nodes: LoadedBranch,
    pub mini_allocator: MiniAllocator,
    pub sealed: bool,
}

pub enum CachedAllocationBranchEvent {
    Append{
        receipt: LoadedPathReceipt,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    },
    Initialize{
        init_root: Address,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        write_nodes: LoadedBranch,
    },
    StagePage{
        addr: Address,
        write_nodes: LoadedBranch,
    },
    BulkSeal{
        root: Address,
        aux_ptr: Pointer,
        write_nodes: LoadedBranch,
    },
    Grow{
        new_root_addr: Address,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    },
    Split{
        new_child_addr: Address,
        receipt: LoadedPathReceipt,
        split_arg: SplitArg,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    },
    Seal{
        aux_ptr: Pointer,
        read_nodes: LoadedBranch,
        write_nodes: LoadedBranch,
    },
    AllocFill{},
}

impl CachedAllocationBranch {
    pub open spec fn new(aus: Set<AU>) -> Self {
        CachedAllocationBranch {
            branch: CachedBranch::State::empty_active(),
            staged_nodes: Map::empty(),
            mini_allocator: MiniAllocator::empty().add_aus(aus),
            sealed: false,
        }
    }

    pub open spec fn can_fill(self, allocs: Set<AU>) -> bool {
        &&& !self.sealed
        &&& self.mini_allocator.all_aus().disjoint(allocs)
    }

    pub open spec fn fill_aus(self, allocs: Set<AU>) -> Self
        recommends self.can_fill(allocs)
    {
        CachedAllocationBranch {
            mini_allocator: self.mini_allocator.add_aus(allocs),
            ..self
        }
    }

    pub open spec fn staged_branch(
        self,
        root: Address,
        write_nodes: LoadedBranch,
    ) -> LinkedBranch<Summary> {
        LinkedBranch {
            root,
            disk_view: BranchDiskView {
                entries: self.staged_nodes.union_prefer_right(write_nodes),
            },
        }
    }

    pub open spec fn bulk_allocator(
        self,
        root: Address,
        aux_ptr: Pointer,
    ) -> MiniAllocator {
        let with_root = self.mini_allocator.allocate(root);
        if aux_ptr is Some {
            with_root.allocate(aux_ptr.unwrap())
        } else {
            with_root
        }
    }

    pub open spec fn build_next(
        pre: Self,
        post: Self,
        event: CachedAllocationBranchEvent,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    ) -> bool {
        match event {
            CachedAllocationBranchEvent::AllocFill{} => {
                &&& deallocs.is_empty()
                &&& pre.can_fill(allocs)
                &&& post == pre.fill_aus(allocs)
            }
            CachedAllocationBranchEvent::StagePage{addr, write_nodes} => {
                &&& !pre.sealed
                &&& pre.branch.root is None
                &&& allocs.is_empty()
                &&& deallocs.is_empty()
                &&& pre.mini_allocator.can_allocate(addr)
                &&& !pre.staged_nodes.contains_key(addr)
                &&& write_nodes.dom() == set![addr]
                &&& write_nodes[addr].wf()
                &&& write_nodes[addr].keys_strictly_sorted()
                &&& !(write_nodes[addr] is Auxiliary)
                &&& post == CachedAllocationBranch {
                    branch: pre.branch,
                    staged_nodes: pre.staged_nodes.insert(
                        addr,
                        write_nodes[addr],
                    ),
                    mini_allocator: pre.mini_allocator.allocate(addr),
                    sealed: false,
                }
            }
            CachedAllocationBranchEvent::BulkSeal{
                root,
                aux_ptr,
                write_nodes,
            } => {
                let allocator = pre.bulk_allocator(root, aux_ptr);
                let branch = pre.staged_branch(root, write_nodes);
                &&& !pre.sealed
                &&& pre.branch.root is None
                &&& allocs.is_empty()
                &&& pre.mini_allocator.can_allocate(root)
                &&& !pre.staged_nodes.contains_key(root)
                &&& if aux_ptr is Some {
                    &&& root != aux_ptr.unwrap()
                    &&& pre.mini_allocator.allocate(root)
                        .can_allocate(aux_ptr.unwrap())
                    &&& !pre.staged_nodes.contains_key(aux_ptr.unwrap())
                    &&& write_nodes.dom() == set![root, aux_ptr.unwrap()]
                } else {
                    write_nodes.dom() == set![root]
                }
                &&& deallocs == allocator.removable_aus()
                &&& branch.valid_sealed_branch()
                &&& branch.tight_disk_view_with_summary()
                &&& branch.get_summary()
                    == allocator.all_aus() - deallocs
                &&& post == CachedAllocationBranch {
                    branch: CachedBranch::State { root: Some(root) },
                    staged_nodes: Map::empty(),
                    mini_allocator: allocator.prune(deallocs),
                    sealed: true,
                }
            }
            _ => {
                &&& !pre.sealed
                &&& allocs.is_empty()
                &&& (!(event is Seal) ==> deallocs.is_empty())
                &&& (!(event is Seal) ==> post.sealed == pre.sealed)
                &&& post.staged_nodes == pre.staged_nodes
                &&& match event {
                    CachedAllocationBranchEvent::Append{receipt, keys, msgs, read_nodes, write_nodes} => {
                        let branch_lbl = CachedBranch::Label::Append{
                            mini_allocator: pre.mini_allocator,
                            receipt,
                            keys,
                            msgs,
                            read_nodes,
                            write_nodes,
                        };
                        &&& CachedBranch::State::next(pre.branch, post.branch, branch_lbl)
                        &&& post.mini_allocator == pre.mini_allocator
                    }
                    CachedAllocationBranchEvent::Initialize{init_root, keys, msgs, write_nodes} => {
                        let branch_lbl = CachedBranch::Label::Initialize{
                            mini_allocator: pre.mini_allocator,
                            init_root,
                            keys,
                            msgs,
                            write_nodes,
                        };
                        &&& CachedBranch::State::next(pre.branch, post.branch, branch_lbl)
                        &&& post.mini_allocator == pre.mini_allocator.allocate(init_root)
                    }
                    CachedAllocationBranchEvent::Grow{new_root_addr, read_nodes, write_nodes} => {
                        let branch_lbl = CachedBranch::Label::Grow{
                            mini_allocator: pre.mini_allocator,
                            new_root_addr,
                            read_nodes,
                            write_nodes,
                        };
                        &&& CachedBranch::State::next(pre.branch, post.branch, branch_lbl)
                        &&& post.mini_allocator == pre.mini_allocator.allocate(new_root_addr)
                    }
                    CachedAllocationBranchEvent::Split{new_child_addr, receipt, split_arg, read_nodes, write_nodes} => {
                        let branch_lbl = CachedBranch::Label::Split{
                            mini_allocator: pre.mini_allocator,
                            new_child_addr,
                            receipt,
                            split_arg,
                            read_nodes,
                            write_nodes,
                        };
                        &&& CachedBranch::State::next(pre.branch, post.branch, branch_lbl)
                        &&& post.mini_allocator == pre.mini_allocator.allocate(new_child_addr)
                    }
                    CachedAllocationBranchEvent::Seal{aux_ptr, read_nodes, write_nodes} => {
                        let branch_lbl = CachedBranch::Label::Seal{
                            mini_allocator: pre.mini_allocator,
                            aux_ptr,
                            read_nodes,
                            write_nodes,
                        };
                        let with_aux = if aux_ptr is Some {
                            pre.mini_allocator.allocate(aux_ptr.unwrap())
                        } else {
                            pre.mini_allocator
                        };
                        &&& CachedBranch::State::next(pre.branch, post.branch, branch_lbl)
                        &&& deallocs == pre.mini_allocator.removable_aus()
                        &&& post.mini_allocator == with_aux.prune(deallocs)
                        &&& post.sealed
                    }
                    _ => false,
                }
            }
        }
    }

    pub open spec fn summary(self) -> Summary {
        self.mini_allocator.all_aus()
    }

    pub open spec fn sealed_root(self) -> Pointer
        recommends self.sealed
    {
        self.branch.root
    }
}

pub open spec fn cached_branch_alloc_aus(branches: Seq<CachedAllocationBranch>) -> Set<AU> {
    let aus = Seq::new(branches.len(), |i: int| branches[i].mini_allocator.all_aus());
    crate::betree::Utils_v::union_seq_of_sets(aus)
}

pub proof fn cached_branch_alloc_aus_contains(
    branches: Seq<CachedAllocationBranch>,
    au: AU,
) -> (idx: int)
    requires cached_branch_alloc_aus(branches).contains(au)
    ensures
        0 <= idx < branches.len(),
        branches[idx].mini_allocator.all_aus().contains(au),
{
    let sets = Seq::new(
        branches.len(),
        |i: int| branches[i].mini_allocator.all_aus(),
    );
    crate::betree::Utils_v::lemma_union_seq_of_sets_contains(
        sets,
        au,
    );
    let idx = choose |idx: int|
        0 <= idx < sets.len() && sets[idx].contains(au);
    idx
}

pub proof fn cached_branch_alloc_aus_update_subset(
    branches: Seq<CachedAllocationBranch>,
    idx: int,
    update: CachedAllocationBranch,
    extra: Set<AU>,
)
    requires
        0 <= idx < branches.len(),
        update.mini_allocator.all_aus()
            <= branches[idx].mini_allocator.all_aus() + extra,
    ensures
        cached_branch_alloc_aus(branches.update(idx, update))
            <= cached_branch_alloc_aus(branches) + extra,
{
    let updated = branches.update(idx, update);
    assert forall |au: AU|
        #[trigger] cached_branch_alloc_aus(updated).contains(au)
        implies (cached_branch_alloc_aus(branches) + extra).contains(au)
    by {
        let source_idx = cached_branch_alloc_aus_contains(updated, au);
        if source_idx == idx {
            if !extra.contains(au) {
                let sets = Seq::new(
                    branches.len(),
                    |i: int| branches[i].mini_allocator.all_aus(),
                );
                assert(sets[idx].contains(au));
                crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                    sets,
                    au,
                );
            }
        } else {
            let sets = Seq::new(
                branches.len(),
                |i: int| branches[i].mini_allocator.all_aus(),
            );
            assert(updated[source_idx] == branches[source_idx]);
            assert(sets[source_idx].contains(au));
            crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                sets,
                au,
            );
        }
    };
}

pub proof fn cached_branch_alloc_aus_update_remove_exact(
    branches: Seq<CachedAllocationBranch>,
    idx: int,
    update: CachedAllocationBranch,
    removed: Set<AU>,
)
    requires
        0 <= idx < branches.len(),
        update.mini_allocator.all_aus()
            == branches[idx].mini_allocator.all_aus()
                - removed,
        removed
            <= branches[idx].mini_allocator.all_aus(),
        forall |left: int, right: int|
            0 <= left < right < branches.len()
            ==> (#[trigger] branches[left])
                .mini_allocator.all_aus().disjoint(
                    (#[trigger] branches[right])
                        .mini_allocator.all_aus(),
                ),
    ensures
        cached_branch_alloc_aus(
            branches.update(idx, update),
        ) == cached_branch_alloc_aus(branches) - removed,
{
    let updated = branches.update(idx, update);
    cached_branch_alloc_aus_update_subset(
        branches,
        idx,
        update,
        Set::empty(),
    );
    assert forall |au: AU|
        #[trigger] cached_branch_alloc_aus(updated)
            .contains(au)
        <==> (cached_branch_alloc_aus(branches)
            - removed).contains(au)
    by {
        if cached_branch_alloc_aus(updated).contains(au) {
            let source_idx =
                cached_branch_alloc_aus_contains(
                    updated,
                    au,
                );
            if source_idx == idx {
                assert(update.mini_allocator.all_aus()
                    .contains(au));
                assert(branches[idx].mini_allocator
                    .all_aus().contains(au));
                assert(!removed.contains(au));
            } else {
                assert(updated[source_idx]
                    == branches[source_idx]);
                assert(branches[source_idx]
                    .mini_allocator.all_aus().contains(au));
                if branches[idx].mini_allocator
                    .all_aus().contains(au)
                {
                    let (left, right) =
                        if source_idx < idx {
                            (source_idx, idx)
                        } else {
                            (idx, source_idx)
                        };
                    assert(branches[left]
                        .mini_allocator.all_aus().disjoint(
                            branches[right]
                                .mini_allocator.all_aus(),
                        ));
                    assert(false);
                }
                assert(!removed.contains(au));
            }
        } else if cached_branch_alloc_aus(branches)
            .contains(au) && !removed.contains(au)
        {
            let source_idx =
                cached_branch_alloc_aus_contains(
                    branches,
                    au,
                );
            if source_idx == idx {
                assert(update.mini_allocator.all_aus()
                    .contains(au));
                let sets = Seq::new(
                    updated.len(),
                    |i: int| updated[i]
                        .mini_allocator.all_aus(),
                );
                assert(sets[idx].contains(au));
                crate::betree::Utils_v::
                    lemma_set_subset_of_union_seq_of_sets(
                        sets,
                        au,
                    );
            } else {
                assert(updated[source_idx]
                    == branches[source_idx]);
                let sets = Seq::new(
                    updated.len(),
                    |i: int| updated[i]
                        .mini_allocator.all_aus(),
                );
                assert(sets[source_idx].contains(au));
                crate::betree::Utils_v::
                    lemma_set_subset_of_union_seq_of_sets(
                        sets,
                        au,
                    );
            }
        }
    }
}

pub proof fn cached_branch_alloc_aus_remove_subset(
    branches: Seq<CachedAllocationBranch>,
    idx: int,
)
    requires 0 <= idx < branches.len()
    ensures
        cached_branch_alloc_aus(branches.remove(idx))
            <= cached_branch_alloc_aus(branches),
{
    let removed = branches.remove(idx);
    assert forall |au: AU|
        #[trigger] cached_branch_alloc_aus(removed).contains(au)
        implies cached_branch_alloc_aus(branches).contains(au)
    by {
        let removed_idx = cached_branch_alloc_aus_contains(removed, au);
        let source_idx = if removed_idx < idx {
            removed_idx
        } else {
            removed_idx + 1
        };
        assert(0 <= source_idx < branches.len());
        assert(branches[source_idx] == removed[removed_idx]);
        let sets = Seq::new(
            branches.len(),
            |i: int| branches[i].mini_allocator.all_aus(),
        );
        assert(sets[source_idx].contains(au));
        crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
            sets,
            au,
        );
    };
}

pub proof fn cached_branch_alloc_aus_remove_exact(
    branches: Seq<CachedAllocationBranch>,
    idx: int,
)
    requires
        0 <= idx < branches.len(),
        forall |left: int, right: int|
            0 <= left < right < branches.len()
            ==> (#[trigger] branches[left])
                .mini_allocator.all_aus().disjoint(
                    (#[trigger] branches[right])
                        .mini_allocator.all_aus(),
                ),
    ensures
        cached_branch_alloc_aus(branches.remove(idx))
            == cached_branch_alloc_aus(branches)
                - branches[idx].mini_allocator.all_aus(),
{
    let removed = branches.remove(idx);
    cached_branch_alloc_aus_remove_subset(branches, idx);
    assert forall |au: AU|
        #[trigger] cached_branch_alloc_aus(removed)
            .contains(au)
        <==> (cached_branch_alloc_aus(branches)
            - branches[idx].mini_allocator.all_aus())
            .contains(au)
    by {
        if cached_branch_alloc_aus(removed)
            .contains(au)
        {
            let removed_idx =
                cached_branch_alloc_aus_contains(
                    removed,
                    au,
                );
            let source_idx = if removed_idx < idx {
                removed_idx
            } else {
                removed_idx + 1
            };
            assert(branches[source_idx]
                .mini_allocator.all_aus().contains(au));
            assert(source_idx != idx);
            let (left, right) = if source_idx < idx {
                (source_idx, idx)
            } else {
                (idx, source_idx)
            };
            assert(branches[left].mini_allocator
                .all_aus().disjoint(
                    branches[right].mini_allocator
                        .all_aus(),
                ));
            assert(!branches[idx].mini_allocator
                .all_aus().contains(au));
        } else if cached_branch_alloc_aus(branches)
            .contains(au)
            && !branches[idx].mini_allocator
                .all_aus().contains(au)
        {
            let source_idx =
                cached_branch_alloc_aus_contains(
                    branches,
                    au,
                );
            assert(source_idx != idx);
            let removed_idx = if source_idx < idx {
                source_idx
            } else {
                source_idx - 1
            };
            assert(0 <= removed_idx < removed.len());
            assert(removed[removed_idx]
                == branches[source_idx]);
            let sets = Seq::new(
                removed.len(),
                |i: int| removed[i]
                    .mini_allocator.all_aus(),
            );
            assert(sets[removed_idx].contains(au));
            crate::betree::Utils_v::
                lemma_set_subset_of_union_seq_of_sets(
                    sets,
                    au,
                );
        }
    }
}

pub proof fn cached_branch_alloc_aus_push_subset(
    branches: Seq<CachedAllocationBranch>,
    append: CachedAllocationBranch,
    extra: Set<AU>,
)
    requires append.mini_allocator.all_aus() <= extra
    ensures
        cached_branch_alloc_aus(branches.push(append))
            <= cached_branch_alloc_aus(branches) + extra,
{
    let pushed = branches.push(append);
    assert forall |au: AU|
        #[trigger] cached_branch_alloc_aus(pushed).contains(au)
        implies (cached_branch_alloc_aus(branches) + extra).contains(au)
    by {
        let pushed_idx = cached_branch_alloc_aus_contains(pushed, au);
        if pushed_idx < branches.len() {
            assert(pushed[pushed_idx] == branches[pushed_idx]);
            let sets = Seq::new(
                branches.len(),
                |i: int| branches[i].mini_allocator.all_aus(),
            );
            assert(sets[pushed_idx].contains(au));
            crate::betree::Utils_v::lemma_set_subset_of_union_seq_of_sets(
                sets,
                au,
            );
        } else {
            assert(pushed_idx == branches.len());
            assert(pushed[pushed_idx] == append);
        }
    };
}

pub proof fn cached_allocation_branch_build_all_aus_subset(
    pre: CachedAllocationBranch,
    post: CachedAllocationBranch,
    event: CachedAllocationBranchEvent,
    allocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        pre.mini_allocator.wf(),
        CachedAllocationBranch::build_next(
            pre,
            post,
            event,
            allocs,
            deallocs,
        ),
    ensures
        post.mini_allocator.all_aus()
            <= pre.mini_allocator.all_aus() + allocs,
        post.mini_allocator.all_aus()
            == (pre.mini_allocator.all_aus() + allocs) - deallocs,
{
    match event {
        CachedAllocationBranchEvent::AllocFill{} => {
            crate::implementation::BranchProofUtils_v::
                mini_allocator_add_aus_preserves_all_aus(
                    pre.mini_allocator,
                    allocs,
                );
        }
        CachedAllocationBranchEvent::StagePage{addr, ..} => {
            crate::implementation::BranchProofUtils_v::
                mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    addr,
                );
        }
        CachedAllocationBranchEvent::BulkSeal{root, aux_ptr, ..} => {
            let with_root = pre.mini_allocator.allocate(root);
            crate::implementation::BranchProofUtils_v::
                mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    root,
                );
            let allocator = if aux_ptr is Some {
                crate::implementation::BranchProofUtils_v::
                    mini_allocator_allocate_preserves_all_aus(
                        with_root,
                        aux_ptr.unwrap(),
                    );
                with_root.allocate(aux_ptr.unwrap())
            } else {
                with_root
            };
            allocator.prune_preserves_wf(deallocs);
        }
        CachedAllocationBranchEvent::Append{..} => {}
        CachedAllocationBranchEvent::Initialize{init_root, ..} => {
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre.branch,
                    post.branch,
                    CachedBranch::Label::Initialize{
                        mini_allocator: pre.mini_allocator,
                        init_root,
                        keys: event.arrow_Initialize_keys(),
                        msgs: event.arrow_Initialize_msgs(),
                        write_nodes: event.arrow_Initialize_write_nodes(),
                    },
                    step,
                );
            match step {
                CachedBranch::Step::initialize_branch() => {
                }
                _ => {
                    assert(false);
                }
            }
            crate::implementation::BranchProofUtils_v::
                mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    init_root,
                );
        }
        CachedAllocationBranchEvent::Grow{new_root_addr, ..} => {
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre.branch,
                    post.branch,
                    CachedBranch::Label::Grow{
                        mini_allocator: pre.mini_allocator,
                        new_root_addr,
                        read_nodes: event.arrow_Grow_read_nodes(),
                        write_nodes: event.arrow_Grow_write_nodes(),
                    },
                    step,
                );
            match step {
                CachedBranch::Step::grow_step() => {
                }
                _ => {
                    assert(false);
                }
            }
            crate::implementation::BranchProofUtils_v::
                mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    new_root_addr,
                );
        }
        CachedAllocationBranchEvent::Split{new_child_addr, ..} => {
            reveal(CachedBranch::State::next);
            reveal(CachedBranch::State::next_by);
            let step = choose |step: CachedBranch::Step|
                CachedBranch::State::next_by(
                    pre.branch,
                    post.branch,
                    CachedBranch::Label::Split{
                        mini_allocator: pre.mini_allocator,
                        new_child_addr,
                        receipt: event.arrow_Split_receipt(),
                        split_arg: event.arrow_Split_split_arg(),
                        read_nodes: event.arrow_Split_read_nodes(),
                        write_nodes: event.arrow_Split_write_nodes(),
                    },
                    step,
                );
            match step {
                CachedBranch::Step::split_step() => {
                }
                _ => {
                    assert(false);
                }
            }
            crate::implementation::BranchProofUtils_v::
                mini_allocator_allocate_preserves_all_aus(
                    pre.mini_allocator,
                    new_child_addr,
                );
        }
        CachedAllocationBranchEvent::Seal{aux_ptr, ..} => {
            let with_aux = if aux_ptr is Some {
                pre.mini_allocator.allocate(aux_ptr.unwrap())
            } else {
                pre.mini_allocator
            };
            if aux_ptr is Some {
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                let step = choose |step: CachedBranch::Step|
                    CachedBranch::State::next_by(
                        pre.branch,
                        post.branch,
                        CachedBranch::Label::Seal{
                            mini_allocator: pre.mini_allocator,
                            aux_ptr,
                            read_nodes: event.arrow_Seal_read_nodes(),
                            write_nodes: event.arrow_Seal_write_nodes(),
                        },
                        step,
                    );
                match step {
                    CachedBranch::Step::seal_step() => {
                    }
                    _ => {
                        assert(false);
                    }
                }
                crate::implementation::BranchProofUtils_v::
                    mini_allocator_allocate_preserves_all_aus(
                        pre.mini_allocator,
                        aux_ptr.unwrap(),
                    );
            }
            with_aux.prune_preserves_wf(deallocs);
        }
    }
    assert(post.mini_allocator.all_aus()
        == (pre.mini_allocator.all_aus() + allocs) - deallocs);
}

pub struct FrozenBranchBetree {
    pub root: Pointer,
    pub seq_end: LSN,
}

pub struct CachedBranchBetreeAccess {
    pub betree_reads: LoadedBetree,
    pub branch_reads: LoadedBranch,
    pub betree_writes: LoadedBetree,
    pub branch_writes: LoadedBranch,
}

impl CachedBranchBetreeAccess {
    pub open spec fn empty() -> Self {
        Self {
            betree_reads: Map::empty(),
            branch_reads: Map::empty(),
            betree_writes: Map::empty(),
            branch_writes: Map::empty(),
        }
    }

    pub open spec fn from_bulk_event(
        event: CachedBulkBranchEvent,
    ) -> Self {
        let branch_writes = event.write_nodes();
        Self {
            branch_writes,
            ..Self::empty()
        }
    }

    pub open spec fn wf(self) -> bool {
        &&& self.betree_reads.dom().disjoint(self.branch_reads.dom())
        &&& self.betree_writes.dom().disjoint(self.branch_writes.dom())
    }

    pub open spec fn read_only(self) -> bool {
        self.betree_writes.is_empty() && self.branch_writes.is_empty()
    }

    pub open spec fn only_betree(self) -> bool {
        self.branch_reads.is_empty() && self.branch_writes.is_empty()
    }

    pub open spec fn only_branch(self) -> bool {
        self.betree_reads.is_empty() && self.betree_writes.is_empty()
    }
}

impl CachedBulkBranchEvent {
    pub open spec fn write_nodes(self) -> LoadedBranch {
        match self {
            CachedBulkBranchEvent::StagePage { write_nodes, .. }
            | CachedBulkBranchEvent::BulkSeal { write_nodes, .. } =>
                write_nodes,
        }
    }
}

state_machine! { CachedBranchBetree {
    fields {
        pub root: Pointer,
        pub memtable: Memtable,
        pub betree_aus: AULikes,
        pub branch_aus: AULikes,
        pub branch_summary: Map<AU, Summary>,
        pub compactors: Seq<CompactorInput>,
        pub compactor_receipts: Seq<LoadedBranch>,
        pub wip_branches: Seq<CachedBulkBranch>,
    }

    pub enum Label {
        Query{
            end_lsn: LSN,
            key: Key,
            value: Value,
            access: CachedBranchBetreeAccess,
        },
        Put{puts: MsgHistory},
        FreezeAs{image: FrozenBranchBetree},
        Internal,
        InternalAccess{access: CachedBranchBetreeAccess},
        InternalAllocAccess{
            allocs: Set<AU>,
            deallocs: Set<AU>,
            access: CachedBranchBetreeAccess,
        },
    }

    pub open spec fn is_fresh(self, aus: Set<AU>) -> bool {
        &&& self.betree_aus.dom().disjoint(aus)
        &&& summary_aus(self.branch_summary).disjoint(aus)
        &&& cached_bulk_branch_alloc_aus(self.wip_branches).disjoint(aus)
    }

    pub open spec fn owned_aus(self) -> Set<AU> {
        self.betree_aus.dom()
            + self.branch_aus.dom()
            + summary_aus(self.branch_summary)
            + cached_bulk_branch_alloc_aus(self.wip_branches)
    }

    pub open spec fn durable_aus(self) -> Set<AU> {
        self.betree_aus.dom()
            + self.branch_aus.dom()
            + summary_aus(self.branch_summary)
    }

    pub open spec fn compactor_input_aus(self, input_idx: int) -> Set<AU>
        recommends 0 <= input_idx < self.compactors.len()
    {
        let roots = self.compactors[input_idx].input_buffers.addrs.to_set();
        summary_aus(self.branch_summary.restrict(to_aus(roots)))
    }

    init! { initialize(
        root: Pointer,
        seq_end: LSN,
        betree_aus: AULikes,
        branch_aus: AULikes,
        branch_summary: Map<AU, Summary>,
    ) {
        init root = root;
        init memtable = Memtable::empty_memtable(seq_end);
        init betree_aus = betree_aus;
        init branch_aus = branch_aus;
        init branch_summary = branch_summary;
        init compactors = Seq::empty();
        init compactor_receipts = Seq::empty();
        init wip_branches = Seq::empty();
    }}

    transition! { query(
        lbl: Label,
        receipt: LoadedBetreeQueryReceipt,
        betree_reads: LoadedBetree,
        branch_reads: LoadedBranch,
    ) {
        require let Label::Query{end_lsn, key, value, access} = lbl;
        require access == CachedBranchBetreeAccess {
            betree_reads,
            branch_reads,
            betree_writes: Map::empty(),
            branch_writes: Map::empty(),
        };
        require access.wf();
        require end_lsn == pre.memtable.seq_end;
        require receipt.valid_for(pre.root, key, betree_reads, branch_reads);
        require Message::Define{value}
            == receipt.result().merge(pre.memtable.query(key));
    }}

    transition! { put(lbl: Label) {
        require let Label::Put{puts} = lbl;
        require puts.wf();
        require puts.can_follow(pre.memtable.seq_end);
        update memtable = pre.memtable.apply_puts(puts);
    }}

    transition! { freeze_as(lbl: Label) {
        require let Label::FreezeAs{image} = lbl;
        require pre.memtable.is_empty();
        require image == FrozenBranchBetree{root: pre.root, seq_end: pre.memtable.seq_end};
    }}

    transition! { branch_begin(lbl: Label) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require allocs.is_empty();
        require deallocs.is_empty();
        require access == CachedBranchBetreeAccess::empty();
        update wip_branches = pre.wip_branches.push(
            CachedBulkBranch::new(Set::empty()),
        );
    }}

    transition! { branch_fill(
        lbl: Label,
        idx: int,
        post_branch: CachedBulkBranch,
    ) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require access == CachedBranchBetreeAccess::empty();
        require pre.is_fresh(allocs);
        require 0 <= idx < pre.wip_branches.len();
        require CachedBulkBranch::fill_next(
            pre.wip_branches[idx], post_branch, allocs, deallocs,
        );
        update wip_branches = pre.wip_branches.update(idx, post_branch);
    }}

    transition! { branch_build(
        lbl: Label,
        idx: int,
        post_branch: CachedBulkBranch,
        event: CachedBulkBranchEvent,
    ) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require access.only_branch();
        require access.branch_writes == event.write_nodes();
        require pre.is_fresh(allocs);
        require 0 <= idx < pre.wip_branches.len();
        require CachedBulkBranch::build_next(
            pre.wip_branches[idx], post_branch, event, allocs, deallocs,
        );
        update wip_branches = pre.wip_branches.update(idx, post_branch);
    }}

    transition! { branch_abort(lbl: Label, idx: int) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require allocs.is_empty();
        require access == CachedBranchBetreeAccess::empty();
        require 0 <= idx < pre.wip_branches.len();
        require deallocs == pre.wip_branches[idx].mini_allocator.all_aus();
        update wip_branches = pre.wip_branches.remove(idx);
    }}

    transition! { flush_memtable(
        lbl: Label,
        branch_idx: int,
        new_root_addr: Address,
        betree_reads: LoadedBetree,
        betree_writes: LoadedBetree,
        branch_reads: LoadedBranch,
    ) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require access == CachedBranchBetreeAccess {
            betree_reads,
            branch_reads,
            betree_writes,
            branch_writes: Map::empty(),
        };
        require access.wf();
        require 0 <= branch_idx < pre.wip_branches.len();
        let branch = pre.wip_branches[branch_idx];
        require branch.is_sealed();
        let branch_root = branch.sealed_root();
        require valid_loaded_sealed_branch(
            branch_root, branch.summary(), branch_reads,
        );
        require loaded_sealed_branch(
            branch_root,
            branch_reads.restrict(addresses_in_aus(branch.summary())),
        ).i().i()
            == pre.memtable.buffer;
        require pre.root is Some ==> betree_reads.contains_key(pre.root.unwrap());
        require betree_writes == flush_memtable_writes(
            pre.root, branch_root, new_root_addr, betree_reads,
        );
        require betree_writes.dom() <= Set::new(|addr: Address| addr.wf());
        let old_root_likes = if pre.root is Some {
            Multiset::singleton(pre.root.unwrap())
        } else {
            Multiset::empty()
        };
        let new_betree_aus = pre.betree_aus.sub(to_au_likes(old_root_likes))
            .insert(new_root_addr.au);
        let new_branch_aus = pre.branch_aus.insert(branch_root.au);
        require allocs == Set::empty().insert(new_root_addr.au);
        require pre.is_fresh(allocs);
        require deallocs == pre.betree_aus.dom() - new_betree_aus.dom();
        update root = Some(new_root_addr);
        update memtable = pre.memtable.drain();
        update betree_aus = new_betree_aus;
        update branch_aus = new_branch_aus;
        update branch_summary = pre.branch_summary.insert(
            branch_root.au, branch.summary(),
        );
        update wip_branches = pre.wip_branches.remove(branch_idx);
    }}

    transition! { grow(lbl: Label, new_root_addr: Address, betree_writes: LoadedBetree) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require access == CachedBranchBetreeAccess {
            betree_writes,
            ..CachedBranchBetreeAccess::empty()
        };
        require allocs == Set::empty().insert(new_root_addr.au);
        require deallocs.is_empty();
        require pre.is_fresh(allocs);
        require betree_writes == grow_writes(pre.root, new_root_addr);
        require betree_writes.dom() <= Set::new(|addr: Address| addr.wf());
        update root = Some(new_root_addr);
        update betree_aus = pre.betree_aus.insert(new_root_addr.au);
    }}

    transition! { split(
        lbl: Label,
        path: LoadedBetreePath,
        request: SplitRequest,
        new_addrs: SplitAddrs,
        path_addrs: PathAddrs,
        betree_reads: LoadedBetree,
        betree_writes: LoadedBetree,
    ) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require access == CachedBranchBetreeAccess {
            betree_reads,
            betree_writes,
            ..CachedBranchBetreeAccess::empty()
        };
        require pre.is_fresh(allocs);
        require new_addrs.addrs_in_disjoint_aus();
        require to_aus(new_addrs.repr()).disjoint(seq_addrs_to_aus(path_addrs));
        require seq_addrs_disjoint_aus(path_addrs);
        require path.valid_for(pre.root, betree_reads);
        require path_addrs.len() == path.depth();
        require path.target().node.valid_child_index(request.get_child_idx());
        require path.target().node.children[request.get_child_idx() as int] is Some;
        let child_addr = path.child_addr(request.get_child_idx());
        require betree_reads.contains_key(child_addr);
        let child = betree_reads[child_addr];
        require match request {
            SplitRequest::SplitLeaf{split_key, ..} => child.can_split_leaf(split_key),
            SplitRequest::SplitIndex{child_pivot_idx, ..} => child.can_split_index(child_pivot_idx),
        };
        let replacement = split_replacement(path, betree_reads, request, new_addrs);
        require betree_writes == substitute_writes(path, new_addrs.parent, replacement, path_addrs);
        require betree_writes.dom() <= Set::new(|addr: Address| addr.wf());
        let discarded = path_discard_likes(path).insert(child_addr);
        let added = added_path_likes(new_addrs, path_addrs);
        let new_betree_aus = pre.betree_aus.sub(to_au_likes(discarded)).add(to_au_likes(added));
        let new_branch_aus = pre.branch_aus.add(to_au_likes(direct_buffer_likes(child)));
        require allocs == to_aus(new_addrs.repr() + path_addrs.to_set());
        require deallocs == pre.betree_aus.dom() - new_betree_aus.dom();
        update root = Some(replacement_root(path, new_addrs.parent, path_addrs));
        update betree_aus = new_betree_aus;
        update branch_aus = new_branch_aus;
    }}

    transition! { flush(
        lbl: Label,
        path: LoadedBetreePath,
        child_idx: nat,
        buffer_gc: nat,
        new_addrs: TwoAddrs,
        path_addrs: PathAddrs,
        betree_reads: LoadedBetree,
        betree_writes: LoadedBetree,
    ) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require access == CachedBranchBetreeAccess {
            betree_reads,
            betree_writes,
            ..CachedBranchBetreeAccess::empty()
        };
        require pre.is_fresh(allocs);
        require new_addrs.addrs_in_disjoint_aus();
        require to_aus(new_addrs.repr()).disjoint(seq_addrs_to_aus(path_addrs));
        require seq_addrs_disjoint_aus(path_addrs);
        require path.valid_for(pre.root, betree_reads);
        require path_addrs.len() == path.depth();
        let target = path.target().node;
        require target.valid_child_index(child_idx);
        require target.children[child_idx as int] is Some;
        require buffer_gc <= target.buffers.len();
        require target.flushed.update(child_idx as int, target.buffers.len()).all_gte(buffer_gc);
        let child_addr = path.child_addr(child_idx);
        require betree_reads.contains_key(child_addr);
        let replacement = flush_replacement(path, betree_reads, child_idx, buffer_gc, new_addrs);
        require betree_writes == substitute_writes(path, new_addrs.addr1, replacement, path_addrs);
        require betree_writes.dom() <= Set::new(|addr: Address| addr.wf());
        let discarded = path_discard_likes(path).insert(child_addr);
        let added = added_path_likes(new_addrs, path_addrs);
        let new_betree_aus = pre.betree_aus.sub(to_au_likes(discarded)).add(to_au_likes(added));
        let discarded_branches = target.buffers.slice(0, buffer_gc as int).addrs.to_multiset();
        let flushed_ofs = target.flushed.offsets[child_idx as int];
        let added_branches = target.buffers.slice(
            flushed_ofs as int, target.buffers.len() as int,
        ).addrs.to_multiset();
        let new_branch_aus = pre.branch_aus.sub(to_au_likes(discarded_branches))
            .add(to_au_likes(added_branches));
        let branch_deallocs = pre.branch_aus.dom() - new_branch_aus.dom()
            - read_ref_aus(pre.compactors);
        let deallocated_summary = pre.branch_summary.restrict(branch_deallocs);
        require allocs == to_aus(new_addrs.repr() + path_addrs.to_set());
        require deallocs == (pre.betree_aus.dom() - new_betree_aus.dom())
            + summary_aus(deallocated_summary);
        update root = Some(replacement_root(path, new_addrs.addr1, path_addrs));
        update betree_aus = new_betree_aus;
        update branch_aus = new_branch_aus;
        update branch_summary = pre.branch_summary.remove_keys(branch_deallocs);
    }}

    transition! { compact_begin(
        lbl: Label,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        betree_reads: LoadedBetree,
    ) {
        require let Label::InternalAccess{access} = lbl;
        require access == CachedBranchBetreeAccess {
            betree_reads,
            ..CachedBranchBetreeAccess::empty()
        };
        require path.valid_for(pre.root, betree_reads);
        require start < end <= path.target().node.buffers.len();
        let input = CompactorInput {
            input_buffers: path.target().node.buffers.slice(start as int, end as int),
            offset_map: path.target().node.make_offset_map().decrement(start),
        };
        update compactors = pre.compactors.push(input);
        update compactor_receipts = pre.compactor_receipts.push(Map::empty());
    }}

    transition! { compact_scan_page(
        lbl: Label,
        input_idx: int,
        reads: LoadedBranch,
    ) {
        require let Label::InternalAccess{access} = lbl;
        require access == CachedBranchBetreeAccess {
            branch_reads: reads,
            ..CachedBranchBetreeAccess::empty()
        };
        require 0 <= input_idx < pre.compactors.len();
        require 0 <= input_idx < pre.compactor_receipts.len();
        require reads.len() == 1;
        require reads.dom() <= addresses_in_aus(
            pre.compactor_input_aus(input_idx),
        );
        update compactor_receipts = pre.compactor_receipts.update(
            input_idx,
            pre.compactor_receipts[input_idx].union_prefer_right(reads),
        );
    }}

    transition! { compact_abort(lbl: Label, input_idx: int) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require allocs.is_empty();
        require access == CachedBranchBetreeAccess::empty();
        require 0 <= input_idx < pre.compactors.len();
        let new_compactors = pre.compactors.remove(input_idx);
        let new_compactor_receipts = pre.compactor_receipts.remove(input_idx);
        let released = read_ref_aus(pre.compactors) - read_ref_aus(new_compactors);
        let branch_deallocs = released - pre.branch_aus.dom();
        let deallocated_summary = pre.branch_summary.restrict(branch_deallocs);
        require deallocs == summary_aus(deallocated_summary);
        update compactors = new_compactors;
        update compactor_receipts = new_compactor_receipts;
        update branch_summary = pre.branch_summary.remove_keys(branch_deallocs);
    }}

    transition! { compact_complete(
        lbl: Label,
        input_idx: int,
        branch_idx: int,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        new_node_addr: Address,
        path_addrs: PathAddrs,
        betree_reads: LoadedBetree,
        betree_writes: LoadedBetree,
    ) {
        require let Label::InternalAllocAccess{allocs, deallocs, access} = lbl;
        require access == CachedBranchBetreeAccess {
            betree_reads,
            betree_writes,
            ..CachedBranchBetreeAccess::empty()
        };
        require pre.is_fresh(allocs);
        require !seq_addrs_to_aus(path_addrs).contains(new_node_addr.au);
        require seq_addrs_disjoint_aus(path_addrs);
        require 0 <= input_idx < pre.compactors.len();
        require 0 <= branch_idx < pre.wip_branches.len();
        let branch = pre.wip_branches[branch_idx];
        require branch.is_sealed();
        let branch_root = branch.sealed_root();
        require path.valid_for(pre.root, betree_reads);
        require path_addrs.len() == path.depth();
        require start < end <= path.target().node.buffers.len();
        require pre.compactors[input_idx] == CompactorInput {
            input_buffers: path.target().node.buffers.slice(
                start as int,
                end as int,
            ),
            offset_map: path.target().node.make_offset_map().decrement(start),
        };
        let input_roots = pre.compactors[input_idx].input_buffers.addrs.to_set();
        require valid_loaded_sealed_branches(
            input_roots,
            pre.branch_summary,
            pre.compactor_receipts[input_idx],
        );
        let input_buffer_dv = BufferDisk {
            entries: pre.compactor_receipts[input_idx],
        };
        let compacted_branch = branch.sealed_branch();
        let compacted_buffer_dv = BufferDisk {
            entries: compacted_branch.disk_view.entries,
        };
        let target = path.target().node;
        require forall |key: Key|
            compacted_branch.root().linked_contains(
                compacted_buffer_dv, branch_root, key,
            ) <==> #[trigger] input_buffer_dv.valid_compact_key_domain(
                target, start, end, key,
            );
        require forall |key: Key|
            compacted_branch.root().linked_contains(
                compacted_buffer_dv, branch_root, key,
            ) ==> #[trigger] compacted_branch.root().linked_query(
                compacted_buffer_dv, branch_root, key,
            ) == input_buffer_dv.compact_key_value(
                target, start, end, key,
            );
        let new_addrs = TwoAddrs{addr1: new_node_addr, addr2: branch_root};
        let replacement = compact_replacement(
            path, start, end, branch_root, new_addrs,
        );
        require betree_writes == substitute_writes(path, new_node_addr, replacement, path_addrs);
        require betree_writes.dom() <= Set::new(|addr: Address| addr.wf());
        let new_compactors = pre.compactors.remove(input_idx);
        let new_compactor_receipts = pre.compactor_receipts.remove(input_idx);
        let discarded = path_discard_likes(path);
        let added = path_addrs.to_multiset().insert(new_node_addr);
        let new_betree_aus = pre.betree_aus.sub(to_au_likes(discarded)).add(to_au_likes(added));
        let discarded_branches = path.target().node.buffers
            .slice(start as int, end as int).addrs.to_multiset();
        let new_branch_aus = pre.branch_aus.sub(to_au_likes(discarded_branches))
            .insert(branch_root.au);
        let branch_deallocs = pre.branch_summary.dom() - new_branch_aus.dom()
            - read_ref_aus(new_compactors);
        let with_new_summary = pre.branch_summary.insert(
            branch_root.au, branch.summary(),
        );
        let new_branch_summary = with_new_summary.remove_keys(branch_deallocs);
        let deallocated_summary = pre.branch_summary.restrict(branch_deallocs);
        require allocs == to_aus(path_addrs.to_set()).insert(new_node_addr.au);
        require deallocs == (pre.betree_aus.dom() - new_betree_aus.dom())
            + summary_aus(deallocated_summary);
        update root = Some(replacement_root(path, new_node_addr, path_addrs));
        update betree_aus = new_betree_aus;
        update branch_aus = new_branch_aus;
        update branch_summary = new_branch_summary;
        update compactors = new_compactors;
        update compactor_receipts = new_compactor_receipts;
        update wip_branches = pre.wip_branches.remove(branch_idx);
    }}

    transition! { internal_noop(lbl: Label) {
        require lbl is Internal;
    }}
}}

impl CachedBranchBetree::Label {
    pub open spec fn allocs(self) -> Set<AU> {
        match self {
            CachedBranchBetree::Label::InternalAllocAccess{allocs, ..} =>
                allocs,
            _ => Set::empty(),
        }
    }
}

impl CachedBranchBetree::State {
    pub proof fn initialize_is_init_by(
        post: Self,
        root: Pointer,
        seq_end: LSN,
        betree_aus: AULikes,
        branch_aus: AULikes,
        branch_summary: Map<AU, Summary>,
    )
        requires CachedBranchBetree::State::initialize(
            post,
            root,
            seq_end,
            betree_aus,
            branch_aus,
            branch_summary,
        ),
        ensures CachedBranchBetree::State::init_by(
            post,
            CachedBranchBetree::Config::initialize(
                root,
                seq_end,
                betree_aus,
                branch_aus,
                branch_summary,
            ),
        ),
    {
        reveal(CachedBranchBetree::State::init_by);
    }

    pub proof fn put_effect(
        pre: Self,
        post: Self,
        puts: MsgHistory,
    )
        requires CachedBranchBetree::State::next(
            pre,
            post,
            CachedBranchBetree::Label::Put { puts },
        ),
        ensures post == (Self {
            memtable: pre.memtable.apply_puts(puts),
            ..pre
        }),
    {
        reveal(CachedBranchBetree::State::next);
        reveal(CachedBranchBetree::State::next_by);
        let step = choose |step: CachedBranchBetree::Step|
            CachedBranchBetree::State::next_by(
                pre,
                post,
                CachedBranchBetree::Label::Put { puts },
                step,
            );
        match step {
            CachedBranchBetree::Step::put() => {},
            _ => { assert(false); },
        }
    }

    pub proof fn next_wip_alloc_aus_subset(
        pre: Self,
        post: Self,
        lbl: CachedBranchBetree::Label,
    )
        requires
            CachedBranchBetree::State::next(pre, post, lbl),
            forall |idx: int| 0 <= idx < pre.wip_branches.len() ==>
                (#[trigger] pre.wip_branches[idx]).mini_allocator.wf(),
        ensures
            cached_bulk_branch_alloc_aus(post.wip_branches)
                <= cached_bulk_branch_alloc_aus(pre.wip_branches)
                    + lbl.allocs(),
    {
        reveal(CachedBranchBetree::State::next);
        reveal(CachedBranchBetree::State::next_by);
        let step = choose |step: CachedBranchBetree::Step|
            CachedBranchBetree::State::next_by(
                pre,
                post,
                lbl,
                step,
            );
        match step {
            CachedBranchBetree::Step::branch_begin() => {
                let appended = CachedBulkBranch::new(Set::empty());
                assert(appended.mini_allocator.all_aus().is_empty());
                cached_bulk_branch_alloc_aus_push_subset(
                    pre.wip_branches,
                    appended,
                    lbl.allocs(),
                );
            }
            CachedBranchBetree::Step::branch_build(
                idx,
                post_branch,
                event,
            ) => {
                cached_bulk_branch_build_all_aus(
                    pre.wip_branches[idx],
                    post_branch,
                    event,
                    lbl.allocs(),
                    lbl.arrow_InternalAllocAccess_deallocs(),
                );
                cached_bulk_branch_alloc_aus_update_subset(
                    pre.wip_branches,
                    idx,
                    post_branch,
                    lbl.allocs(),
                );
            }
            CachedBranchBetree::Step::branch_fill(idx, post_branch) => {
                cached_bulk_branch_fill_all_aus(
                    pre.wip_branches[idx],
                    post_branch,
                    lbl.allocs(),
                    lbl.arrow_InternalAllocAccess_deallocs(),
                );
                cached_bulk_branch_alloc_aus_update_subset(
                    pre.wip_branches,
                    idx,
                    post_branch,
                    lbl.allocs(),
                );
            }
            CachedBranchBetree::Step::branch_abort(idx) => {
                cached_bulk_branch_alloc_aus_remove_subset(
                    pre.wip_branches,
                    idx,
                );
            }
            CachedBranchBetree::Step::flush_memtable(
                branch_idx,
                new_root_addr,
                betree_reads,
                betree_writes,
                branch_reads,
            ) => {
                cached_bulk_branch_alloc_aus_remove_subset(
                    pre.wip_branches,
                    branch_idx,
                );
            }
            CachedBranchBetree::Step::compact_complete(
                input_idx,
                branch_idx,
                path,
                start,
                end,
                new_node_addr,
                path_addrs,
                betree_reads,
                betree_writes,
            ) => {
                cached_bulk_branch_alloc_aus_remove_subset(
                    pre.wip_branches,
                    branch_idx,
                );
            }
            _ => {
                assert(post.wip_branches == pre.wip_branches);
            }
        }
    }
}

} // verus!
