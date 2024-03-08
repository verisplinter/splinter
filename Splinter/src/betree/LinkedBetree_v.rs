// Copyright 2018-2023 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
#![allow(unused_imports)]
use builtin::*;

use builtin_macros::*;
use state_machines_macros::state_machine;

use vstd::{prelude::*,set_lib::*, map_lib::*};
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::disk::GenericDisk_v::*;
use crate::betree::Buffer_v::*;
use crate::betree::LinkedSeq_v::*;
use crate::betree::BufferDisk_v;
use crate::betree::BufferDisk_v::*;
use crate::betree::BufferOffsets_v::*;
use crate::betree::OffsetMap_v::*;
use crate::betree::Memtable_v::*;
use crate::betree::Domain_v::*;
use crate::betree::PivotTable_v::*;
use crate::betree::SplitRequest_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

verus! {
// Introduces a diskview and pointers, carries forward filtered buffer stacks inside the 
// betree nodes. There are two disk views here. One for the BetreeNode type, and one for 
// the abstract Branch type. A refining state machine replaces single-node branches with
// b+trees.

// propagate buffers<T>
#[verifier::ext_equal]
pub struct BetreeNode<T> {
    pub buffers: LinkedSeq<T>,
    pub pivots: PivotTable,
    pub children: Seq<Pointer>,
    pub flushed: BufferOffsets, // # of buffers flushed to each child
    pub _p: std::marker::PhantomData<(T,)>, // required by template
}

impl<T> BetreeNode<T> {
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.pivots.wf()
        &&& self.children.len() == self.pivots.num_ranges()
        &&& self.children.len() == self.flushed.len()
        &&& self.flushed.all_lte(self.buffers.len()) // values in flushed are bounded by # of buffers
    }

    pub open spec(checked) fn valid_child_index(self, child_idx: nat) -> bool
    {
        &&& child_idx < self.children.len()   
    }

    pub open spec(checked) fn occupied_child_index(self, child_idx: nat) -> bool
        recommends self.wf()
    {
        &&& self.valid_child_index(child_idx)
        &&& self.children[child_idx as int] is Some
    }

    pub open spec(checked) fn my_domain(self) -> Domain
        recommends self.wf()
    {
        Domain::Domain{
            start: self.pivots[0],
            end: self.pivots.pivots.last()
        }
    }

    pub open spec(checked) fn child_domain(self, child_idx: nat) -> Domain
        recommends self.wf(), self.valid_child_index(child_idx)
    {
        Domain::Domain{
            start: self.pivots[child_idx as int],
            end: self.pivots[child_idx as int + 1]
        }
    }

    pub open spec(checked) fn extend_buffer_seq(self, buffers: LinkedSeq<T>) -> BetreeNode<T>
        recommends self.wf()
    {
        BetreeNode{
            buffers: self.buffers.extend(buffers),
            pivots: self.pivots,
            children: self.children,
            flushed: self.flushed,
            ..self
        }
    }

    #[verifier(recommends_by)]
    proof fn flushed_ofs_inline_lemma(self, key: Key)
    {
        self.pivots.route_lemma(key);
        assert( 0 <= self.pivots.route(key) < self.flushed.offsets.len() );
    }

    // returns the flushed offset (index into buffers) for a given key
    // buffers flushed to a child are no longer active for that child
    // renamed from ActiveBuffersForKey
    pub open spec /*XXX (checked)*/ fn flushed_ofs(self, key: Key) -> nat
        recommends self.key_in_domain(key)
    {
        recommends_by(Self::flushed_ofs_inline_lemma);
        let r = self.pivots.route(key);
        self.flushed.offsets[r]
    }

    pub open spec(checked) fn is_leaf(self) -> bool
    {
        &&& self.children.len() == 1
        &&& self.children[0] is None
        &&& self.flushed.offsets == seq![0nat]
    }

    pub open spec(checked) fn is_index(self) -> bool
    {
        forall |i| #[trigger] self.valid_child_index(i) ==> self.children[i as int] is Some
    }

    pub open spec(checked) fn can_split_leaf(self, split_key: Key) -> bool
    {
        &&& self.wf()
        &&& self is leaf
        &&& self.my_domain().contains(split_key)
        &&& self.my_domain()->start != to_element(split_key)
    }

    pub open spec(checked) fn split_leaf(self, split_key: Key) -> (BetreeNode<T>, BetreeNode<T>)
        recommends self.can_split_leaf(split_key)
    {
        let new_left = BetreeNode{
            buffers: self.buffers,
            pivots: self.pivots.update(1, to_element(split_key)),
            children: self.children,
            flushed: self.flushed,
            ..self
        };

        let new_right = BetreeNode{
            buffers: self.buffers,
            pivots: self.pivots.update(0, to_element(split_key)),
            children: self.children,
            flushed: self.flushed,
            ..self
        };

        (new_left, new_right)
    }

    pub open spec(checked) fn can_split_index(self, pivot_idx: nat) -> bool
    {
        &&& self.wf()
        &&& self is index
        &&& 0 < pivot_idx < self.pivots.num_ranges()
    }

    pub open spec(checked) fn  split_index(self, pivot_idx: nat) -> (BetreeNode<T>, BetreeNode<T>)
        recommends self.can_split_index(pivot_idx)
    {
        let idx = pivot_idx as int;
        let new_left = BetreeNode{
            buffers: self.buffers,
            pivots: self.pivots.subrange(0, idx+1),
            children: self.children.subrange(0, idx),
            flushed: self.flushed.slice(0, idx),
            ..self
        };

        let new_right = BetreeNode{
            buffers: self.buffers,
            pivots: self.pivots.subrange(idx, self.pivots.len() as int),
            children: self.children.subrange(idx, self.children.len() as int),
            flushed: self.flushed.slice(idx, self.flushed.len() as int),
            ..self
        };

        (new_left, new_right)
    }

    pub open spec(checked) fn empty_root(domain: Domain) -> BetreeNode<T>
        recommends domain.wf(), domain is Domain
    {
        BetreeNode{
            buffers: LinkedSeq::empty(),
            pivots: domain_to_pivots(domain),
            children: seq![None],
            flushed: BufferOffsets{offsets: seq![0]},
            _p: arbitrary(),
        }
    }

    pub open spec(checked) fn key_in_domain(self, key: Key) -> bool
    {
        &&& self.wf()
        &&& self.pivots.bounded_key(key)
    }

    pub open spec /*XXX(checked)*/ fn child_ptr(self, key: Key) -> Pointer
        recommends self.key_in_domain(key)
    {
        self.children[self.pivots.route(key)]
    }

    pub open spec(checked) fn make_offset_map(self) -> OffsetMap
        recommends self.wf()
    {
        OffsetMap{ offsets: Map::new(|k| true,
            |k| if self.key_in_domain(k) {
                self.flushed_ofs(k)
            } else {
                self.buffers.len()
            })
        }
    }

    #[verifier::opaque]
    pub open spec fn active_buffers(self) -> Set<Address>
    {
        // let start = self.flushed.min_ofs() as int;
        // let end = self.buffers.len() as int;
        // let active_slice = self.buffers.slice(start, end);
        // Set::new(|buffer| active_slice.repr().contains((buffer)))
        Set::new(|buffer| exists |idx|
            self.flushed.min_ofs() <= idx < self.buffers.len() && self.buffers[idx] == buffer)
    }
} // end impl<T> BetreeNode

impl<T: QueryableDisk> BetreeNode<T> {
    // #[verifier::opaque]
    pub open spec(checked) fn compact_key_range(self, start: nat, end: nat, k: Key, buffer_dv: T) -> bool
        recommends self.wf(), start < end <= self.buffers.len()
    {
        let slice = self.buffers.slice(start as int, end as int);
        let slice_ofs_map = self.make_offset_map().decrement(start);
        &&& self.key_in_domain(k)
        &&& self.flushed_ofs(k) <= end
        &&& exists |idx| #[trigger] slice.key_in_buffer_filtered(buffer_dv, slice_ofs_map, 0, k, idx)
    }

    pub open spec /*(checked)*/ fn compact_key_value(self, start: nat, end: nat, k: Key, buffer_dv: T) -> Message
        recommends 
            self.wf(), 
            start < end <= self.buffers.len(), 
            self.compact_key_range(start, end, k, buffer_dv),
    {
        let from = if self.flushed_ofs(k) <= start { 0 } else { self.flushed_ofs(k)-start };
        self.buffers.slice(start as int, end as int).query_from(buffer_dv, k, from)
    }
} // end impl<T: QueryableDisk> BetreeNode

pub struct DiskView<T> {
    pub entries: Map<Address, BetreeNode<T>>,
    pub _p: std::marker::PhantomData<(T,)>, // required by template
}

impl<T> DiskView<T> {
    pub open spec(checked) fn entries_wf(self) -> bool 
    {
        forall |addr| #[trigger] self.entries.contains_key(addr) ==> self.entries[addr].wf()
    }

    pub open spec(checked) fn is_nondangling_ptr(self, ptr: Pointer) -> bool
    {
        ptr is Some ==> self.entries.contains_key(ptr.unwrap())
    }

    pub open spec(checked) fn node_has_nondangling_child_ptrs(self, node: BetreeNode<T>) -> bool
        recommends self.entries_wf(), node.wf()
    {
        forall |i| #[trigger] node.valid_child_index(i) ==> self.is_nondangling_ptr(node.children[i as int])
    }

    pub open spec(checked) fn child_linked(self, node: BetreeNode<T>, idx: nat) -> bool
        recommends 
            self.entries_wf(), 
            node.wf(), 
            node.valid_child_index(idx),
            self.node_has_nondangling_child_ptrs(node),
    {
        let child_ptr = node.children[idx as int];
        &&& child_ptr is Some ==> self.entries[child_ptr.unwrap()].my_domain() == node.child_domain(idx)
    }

    pub open spec(checked) fn node_has_linked_children(self, node: BetreeNode<T>) -> bool
        recommends self.entries_wf(), node.wf(), self.node_has_nondangling_child_ptrs(node)
    {
        forall |i| #[trigger] node.valid_child_index(i) ==> self.child_linked(node, i)
    }

    pub open spec(checked) fn healthy_child_ptrs(self) -> bool
        recommends self.entries_wf()
    {
        &&& forall |addr| #[trigger] self.entries.contains_key(addr) ==> ({
            &&& self.node_has_nondangling_child_ptrs(self.entries[addr])
            &&& self.node_has_linked_children(self.entries[addr])
        })
    }

    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.entries_wf()
        &&& self.healthy_child_ptrs()
        &&& self.entries.dom().finite()
    }

    pub open spec(checked) fn get(self, ptr: Pointer) -> BetreeNode<T>
        recommends self.is_nondangling_ptr(ptr), ptr is Some
    {
        self.entries[ptr.unwrap()]
    }

    pub open spec(checked) fn agrees_with_disk(self, other: DiskView<T>) -> bool
    {
        self.entries.agrees(other.entries)
    }

    pub open spec(checked) fn is_sub_disk(self, big: DiskView<T>) -> bool
    {
        self.entries <= big.entries  
    }

    pub open spec(checked) fn node_children_respects_rank(self, ranking: Ranking, addr: Address) -> bool
        recommends self.wf(), self.entries.contains_key(addr), ranking.contains_key(addr)
    {
        let node = self.entries[addr];
        &&& forall |idx| #[trigger] node.valid_child_index(idx) && node.children[idx as int] is Some 
            ==> ({
                let child_addr = node.children[idx as int].unwrap();
                &&& ranking.contains_key(child_addr)
                &&& ranking[child_addr] < ranking[addr]
            })
    }

    pub open spec(checked) fn valid_ranking(self, ranking: Ranking) -> bool
    {
        &&& self.wf()
        &&& forall |addr| #[trigger] self.entries.contains_key(addr) && ranking.contains_key(addr)
            ==> self.node_children_respects_rank(ranking, addr)
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool 
    {
        self.entries.dom().disjoint(addrs)
    }

    pub open spec(checked) fn modify_disk(self, addr: Address, node: BetreeNode<T>) -> DiskView<T>
    {
        DiskView{ entries: self.entries.insert(addr, node), ..self }
    }

    pub proof fn subdisk_implies_ranking_validity(self, big: DiskView<T>, ranking: Ranking)
        requires 
            self.wf(), 
            self.is_sub_disk(big), 
            big.valid_ranking(ranking),
        ensures 
            self.valid_ranking(ranking)
    {
        assert forall |addr| self.entries.contains_key(addr) && ranking.contains_key(addr)
        implies #[trigger] self.node_children_respects_rank(ranking, addr)
        by {
            assert(big.entries.dom().contains(addr)); // trigger
            assert(self.entries.dom().contains(addr));
        }
    }
} // end of impl<T> DiskView<T>

pub open spec(checked) fn empty_disk<T>() -> DiskView<T>
{
    DiskView{ entries: Map::empty(), _p: arbitrary() }
} 

// maybe name this a none flush addrs
pub struct TwoAddrs {
    pub addr1: Address,
    pub addr2: Address,
}

impl TwoAddrs {
    pub open spec(checked) fn no_duplicates(self) -> bool
    {
        &&& self.addr1 != self.addr2
    }

    pub open spec(checked) fn repr(self) -> Set<Address>
        recommends self.no_duplicates()
    {
        set!{self.addr1, self.addr2}
    }
}

pub struct SplitAddrs {
    pub left: Address,
    pub right: Address,
    pub parent: Address
}

impl SplitAddrs {
    pub open spec(checked) fn no_duplicates(self) -> bool
    {
        &&& self.left != self.right
        &&& self.right != self.parent
        &&& self.parent != self.left
    }

    pub open spec(checked) fn repr(self) -> Set<Address>
        recommends self.no_duplicates()
    {
        set!{self.left, self.right, self.parent}
    }
}

pub struct LinkedBetree<T> {
    pub root: Pointer,
    pub dv: DiskView<T>,
    pub buffer_dv: T,
}

pub type StampedBetree = Stamped<LinkedBetree<BufferDisk>>;

pub open spec(checked) fn empty_linked_betree() -> LinkedBetree<BufferDisk>
{
    LinkedBetree{root: None, dv: empty_disk(), buffer_dv: BufferDisk_v::empty_disk() }
}

pub open spec(checked) fn empty_image() -> StampedBetree {
    Stamped{ value: empty_linked_betree(), seq_end: 0 }
}

impl<T> LinkedBetree<T> {
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.dv.wf()
        &&& self.dv.is_nondangling_ptr(self.root)
    }

    pub open spec(checked) fn has_root(self) -> bool
    {
        &&& self.root is Some
        &&& self.dv.is_nondangling_ptr(self.root)
    }

    pub open spec(checked) fn root(self) -> BetreeNode<T>
        recommends self.has_root()
    {
        self.dv.get(self.root)
    }

    pub open spec(checked) fn valid_ranking(self, ranking: Ranking) -> bool
    {
        &&& self.wf()
        &&& self.dv.valid_ranking(ranking)
        &&& self.has_root() ==> ranking.contains_key(self.root.unwrap())
    }

    pub open spec(checked) fn acyclic(self) -> bool
    {
        &&& self.wf()
        &&& exists |ranking| self.valid_ranking(ranking)
    }

    pub open spec(checked) fn the_ranking(self) -> Ranking
        recommends self.acyclic()
    {
        let ranking = choose |ranking| self.valid_ranking(ranking);
        ranking
    }

    pub open spec(checked) fn finite_ranking(self) -> Ranking
        recommends self.acyclic()
    {
        self.the_ranking().restrict(self.dv.entries.dom())
    }

    proof fn finite_ranking_ensures(self)
        requires self.acyclic()
        ensures
            self.valid_ranking(self.finite_ranking()), 
            self.finite_ranking().dom().finite()
    {
        lemma_len_subset(self.finite_ranking().dom(), self.dv.entries.dom());
    }

    pub open spec(checked) fn child_at_idx(self, idx: nat) -> LinkedBetree<T>
        recommends 
            self.wf(), 
            self.has_root(), 
            self.root().valid_child_index(idx),
    {
        LinkedBetree{ root: self.root().children[idx as int], dv: self.dv, buffer_dv: self.buffer_dv }
    }

    pub open spec(checked) fn child_for_key(self, k: Key) -> LinkedBetree<T>
        recommends 
            self.has_root(), 
            self.root().key_in_domain(k),
    {
        LinkedBetree{ root: self.root().child_ptr(k), dv: self.dv, buffer_dv: self.buffer_dv }
    }

    pub open spec(checked) fn get_rank(self, ranking: Ranking) -> nat
        recommends self.wf()
    {
        if self.has_root() && ranking.contains_key(self.root.unwrap()) {
            ranking[self.root.unwrap()] + 1
        } else {
            0
        }
    }

    pub open spec(checked) fn child_count(self) -> nat
        recommends self.wf()
    {
        if self.has_root() { self.root().children.len() } else { 0 }
    }

    pub open spec(checked) fn can_recurse_for_reachable(self, ranking: Ranking, child_idx: nat) -> bool
    {
        &&& self.wf()
        &&& self.has_root()
        &&& self.valid_ranking(ranking)
        &&& child_idx <= self.child_count()
    }

    #[verifier::decreases_by]
    proof fn reachable_betree_addrs_using_ranking_recur_proof(self, ranking: Ranking, child_idx: nat)
    {
        if child_idx < self.child_count() {
            assert(self.root().valid_child_index(child_idx)); // trigger
        }
    }

    // TODO(verus): workaround since verus doesn't support mutually recursive closure
    closed spec(checked) fn reachable_betree_addrs_using_ranking_recur(self, ranking: Ranking, child_idx: nat) -> Set<Address>
        recommends self.can_recurse_for_reachable(ranking, child_idx)
        decreases self.get_rank(ranking), self.child_count()-child_idx when self.can_recurse_for_reachable(ranking, child_idx) 
            via Self::reachable_betree_addrs_using_ranking_recur_proof
    {
        if child_idx == self.child_count() {
            set!{}
        } else {
            let child_addrs = self.child_at_idx(child_idx).reachable_betree_addrs_using_ranking(ranking);
            let right_subtree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, child_idx + 1);
            child_addrs + right_subtree_addrs
        }
    }

    pub closed spec(checked) fn reachable_betree_addrs_using_ranking(self, ranking: Ranking) -> Set<Address>
        recommends self.wf(), self.valid_ranking(ranking)
        decreases self.get_rank(ranking) when self.wf() && self.valid_ranking(ranking)
    {
        if self.has_root() {
            let sub_tree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, 0);
            let root_addr = set!{ self.root.unwrap() };
            root_addr + sub_tree_addrs
        } else {
            set!{}
        }
    }

    // repr of all reachable betree nodes
    pub open spec(checked) fn reachable_betree_addrs(self) -> Set<Address>
        recommends self.acyclic()
    {
        self.reachable_betree_addrs_using_ranking(self.the_ranking())
    }

    // TODO(Jialin): can change to decreases by when we prove that all address from betree_addr is nondangling ptr
    pub open spec/*XXX (checked)*/ fn reachable_buffer(self, addr: Address, buffer_addr: Address) -> bool
        recommends self.acyclic()
    {
        &&& self.reachable_betree_addrs().contains(addr)
        &&& self.dv.get(Some(addr)).active_buffers().contains(buffer_addr)
    }

    // repr of all reachable buffers
    pub open spec(checked) fn reachable_buffer_addrs(self) -> Set<Address>
        recommends self.acyclic()
    {
        Set::new(|buffer_addr| exists |addr| self.reachable_buffer(addr, buffer_addr))
    }

    pub open spec(checked) fn grow(self, new_root_addr: Address) -> LinkedBetree<T>
    recommends self.wf() //, self.is_fresh(Set::empty().insert(new_root_addr))
    {
        let new_root = BetreeNode{
            buffers: LinkedSeq::empty(), 
            pivots: domain_to_pivots(total_domain()),
            children: seq![self.root],
            flushed: BufferOffsets{offsets: seq![0]},
            _p: arbitrary(),
        };
        let new_dv = self.dv.modify_disk(new_root_addr, new_root);
        LinkedBetree{ root: Some(new_root_addr), dv: new_dv, ..self }
    }

    pub open spec(checked) fn split_element(self, request: SplitRequest) -> Element
        recommends self.can_split_parent(request)
    {
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => to_element(split_key),
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => 
                self.child_at_idx(child_idx).root().pivots.pivots[child_pivot_idx as int]
        }
    }

    // operations on linked betree:
    pub open spec(checked) fn can_split_parent(self, request: SplitRequest) -> bool
    {
        &&& self.wf()
        &&& self.has_root()
        &&& self.root().valid_child_index(request.xxxget_child_idx())
        &&& self.child_at_idx(request.xxxget_child_idx()).has_root()
        &&& match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => {
                &&& self.child_at_idx(child_idx).root().can_split_leaf(split_key)
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                &&& self.child_at_idx(child_idx).root().can_split_index(child_pivot_idx)                
            }
        }
    }

    // NOTE: recommmends check sucks here
    // TODO(JL): maybe just change this to not check recommend?
    pub open spec/*(checked)*/ fn split_parent(self, request: SplitRequest, new_addrs: SplitAddrs) -> LinkedBetree<T>
        recommends self.can_split_parent(request)
    {
        match request {
            SplitRequest::SplitLeaf{child_idx, split_key} => {
                let (new_left_child, new_right_child) = self.child_at_idx(child_idx).root().split_leaf(split_key);
                let new_children = self.root().children.update(child_idx as int, Some(new_addrs.left)
                    ).insert(child_idx as int + 1, Some(new_addrs.right));

                let new_parent = BetreeNode{
                    pivots: self.root().pivots.insert(child_idx as int + 1, to_element(split_key)),
                    children: new_children,
                    flushed: self.root().flushed.dup(child_idx as int),
                    ..self.root()
                };

                let new_dv = self.dv.modify_disk(new_addrs.left, new_left_child
                    ).modify_disk(new_addrs.right, new_right_child
                    ).modify_disk(new_addrs.parent, new_parent);

                LinkedBetree{root: Some(new_addrs.parent), dv: new_dv, ..self }
            }
            SplitRequest::SplitIndex{child_idx, child_pivot_idx} => {
                let (new_left_child, new_right_child) = self.child_at_idx(child_idx).root().split_index(child_pivot_idx);
                let new_children = self.root().children.update(child_idx as int, Some(new_addrs.left)
                    ).insert(child_idx as int + 1, Some(new_addrs.right));

                // NOTE(Jialin): literally needs to match the syntax for the recommend check to be recognized
                let new_parent = BetreeNode{
                    pivots: self.root().pivots.insert(child_idx as int + 1, 
                            self.child_at_idx(child_idx).root().pivots[child_pivot_idx as int]), 
                    children: new_children,
                    flushed: self.root().flushed.dup(child_idx as int),
                    ..self.root()
                };

                let new_dv = self.dv.modify_disk(new_addrs.left, new_left_child
                    ).modify_disk(new_addrs.right, new_right_child
                    ).modify_disk(new_addrs.parent, new_parent);

                LinkedBetree{ root: Some(new_addrs.parent), dv: new_dv, ..self}
            }
        }
    }

    pub open spec(checked) fn can_flush(self, child_idx: nat, buffer_gc: nat) -> bool
    {
        &&& self.wf()
        &&& self.has_root()
        &&& self.root().occupied_child_index(child_idx)
        &&& self.root().flushed.update(child_idx as int, self.root().buffers.len()).all_gte(buffer_gc)
    }

    pub open spec/*XXX(checked)*/ fn flush(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs) -> LinkedBetree<T>
        recommends self.can_flush(child_idx, buffer_gc) //, self.is_fresh(new_addrs.repr())
    {
        let root = self.root();
        let flush_upto = root.buffers.len(); 
        let flushed_ofs = root.flushed.offsets[child_idx as int];

        let buffers_to_child = root.buffers.slice(flushed_ofs as int, flush_upto as int);
        let child = self.dv.get(root.children[child_idx as int]);
        let new_child = child.extend_buffer_seq(buffers_to_child);

        let new_root = BetreeNode{
            buffers: root.buffers.slice(buffer_gc as int, flush_upto as int),
            children: root.children.update(child_idx as int, Some(new_addrs.addr2)),
            flushed: root.flushed.update(child_idx as int, flush_upto).shift_left(buffer_gc),
            ..root
        };

        let new_dv = self.dv.modify_disk(new_addrs.addr1, new_root).modify_disk(new_addrs.addr2, new_child);
        LinkedBetree{ root: Some(new_addrs.addr1), dv: new_dv, ..self }
    }
} // end of LinkedBetree impl

impl<T: QueryableDisk> LinkedBetree<T> {
    pub open spec(checked) fn no_dangling_buffer_ptr(self) -> bool
        recommends self.acyclic()
    {
        self.reachable_buffer_addrs() <= self.buffer_dv.repr()
    }

    pub open spec(checked) fn valid_buffer_dv(self) -> bool
        recommends self.acyclic()
    {
        &&& self.buffer_dv.wf()
        &&& self.dv.is_fresh(self.buffer_dv.repr())
        &&& self.no_dangling_buffer_ptr()
    }

    pub open spec(checked) fn is_fresh(self, addrs: Set<Address>) -> bool
    {
        &&& self.dv.is_fresh(addrs)
        &&& self.buffer_dv.repr().disjoint(addrs)
    }

    pub open spec(checked) fn contains(self, other: Self) -> bool
    {
        &&& self.root == other.root
        &&& other.dv.is_sub_disk(self.dv)
        &&& other.buffer_dv.is_sub_disk(&self.buffer_dv)
    }

    // equivalent to build_tight_tree but only state properties of tight address
    pub open spec(checked) fn same_tight_tree(self, other: Self) -> bool
        recommends self.contains(other)
    {
        &&& self.acyclic()
        &&& self.reachable_betree_addrs() <= other.dv.entries.dom()
        &&& self.reachable_buffer_addrs() <= other.buffer_dv.repr()
    }

    pub open spec(checked) fn subtree_same_tightness(self, other: Self) -> bool
    {
        // NOTE(JL): GC should be driven by the allocation layer 
        // but any GC decision should still leave the disk in a wf state
        &&& other.wf()
        &&& self.contains(other)
        &&& self.same_tight_tree(other)
    }

    pub open spec(checked) fn compact_buffer_valid_domain(self, start: nat, end: nat, compacted_buffer: Buffer) -> bool
        recommends 
            self.wf(),
            self.has_root(),
            start < end <= self.root().buffers.len(),
    {
        forall |k| compacted_buffer.map.contains_key(k) <==> 
            #[trigger] self.root().compact_key_range(start, end, k, self.buffer_dv)
    }

    // #[verifier::opaque]
    pub open spec(checked) fn compact_buffer_valid_range(self, start: nat, end: nat, compacted_buffer: Buffer) -> bool
        recommends 
            self.wf(),
            self.has_root(),
            start < end <= self.root().buffers.len(),
            self.compact_buffer_valid_domain(start, end, compacted_buffer),
    {
        forall |k| compacted_buffer.map.contains_key(k) ==>
            #[trigger]  compacted_buffer.query(k) == self.root().compact_key_value(start, end, k, self.buffer_dv)
    }

    pub open spec(checked) fn can_compact(self, start: nat, end: nat, compacted_buffer: Buffer) -> bool 
    {
        &&& self.wf()
        &&& self.has_root()
        &&& start < end <= self.root().buffers.len()
        &&& self.compact_buffer_valid_domain(start, end, compacted_buffer)
        &&& self.compact_buffer_valid_range(start, end, compacted_buffer)
    }
} // end of impl<T: QueryableDisk> LinkedBetree

impl LinkedBetree<BufferDisk> {
    pub open spec(checked) fn push_memtable(self, memtable: Memtable, new_addrs: TwoAddrs) -> LinkedBetree<BufferDisk>
        recommends 
            self.wf(),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
    {
        let memtable_buffer = LinkedSeq{ addrs: seq![new_addrs.addr2], _p: arbitrary() };
        let new_root = 
            if self.has_root() {
                self.root().extend_buffer_seq(memtable_buffer)
            } else {
                BetreeNode::empty_root(total_domain()).extend_buffer_seq(memtable_buffer)
            };
        let new_dv = self.dv.modify_disk(new_addrs.addr1, new_root);
        let new_buffer_dv = self.buffer_dv.modify_disk(new_addrs.addr2, memtable.buffer);
        LinkedBetree{ root: Some(new_addrs.addr1), dv: new_dv, buffer_dv: new_buffer_dv }
    }

     pub open spec /*(checked)*/ fn compact(self, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs) -> LinkedBetree<BufferDisk>
        recommends 
            new_addrs.no_duplicates(), 
            self.is_fresh(new_addrs.repr()),
            self.can_compact(start, end, compacted_buffer),
    {
        let new_root = BetreeNode{
            buffers: self.root().buffers.update_subrange(start as int, end as int, new_addrs.addr2),
            flushed: self.root().flushed.adjust_compact(start as int, end as int),
            ..self.root()
        };

        let new_dv = self.dv.modify_disk(new_addrs.addr1, new_root);
        let new_buffer_dv = self.buffer_dv.modify_disk(new_addrs.addr2, compacted_buffer);
        LinkedBetree{ root: Some(new_addrs.addr1), dv: new_dv, buffer_dv: new_buffer_dv }
    }
}

pub struct QueryReceiptLine<T>{
    pub linked: LinkedBetree<T>,
    pub result: Message
}

impl<T> QueryReceiptLine<T>{
    pub open spec(checked) fn wf(self) -> bool
    {
        &&& self.result is Define
    }
} // end impl QueryReceiptLine

pub struct QueryReceipt<T>{
    pub key: Key,
    pub linked: LinkedBetree<T>,
    pub lines: Seq<QueryReceiptLine<T>>
}

impl<T: QueryableDisk> QueryReceipt<T>{
    pub open spec(checked) fn structure(self) -> bool
    {
        &&& 0 < self.lines.len()
        &&& self.linked.wf()
        &&& self.lines[0].linked == self.linked
        &&& forall |i:nat| i < self.lines.len() ==> (#[trigger] self.lines[i as int].linked.dv) == self.linked.dv
        &&& forall |i:nat| i < self.lines.len() ==> (#[trigger] self.lines[i as int].linked.buffer_dv) == self.linked.buffer_dv
        &&& forall |i:nat| i < self.lines.len() ==> (#[trigger] self.lines[i as int].linked.has_root()) <==> i < self.lines.len()-1
        &&& self.lines.last().result == Message::Define{value: default_value()}
    }

    pub open spec(checked) fn node(self, i:int) -> BetreeNode<T>
        recommends self.structure(), 0 <= i < self.lines.len() - 1
    {
        self.lines[i].linked.root()
    }

    pub open spec(checked) fn all_lines_wf(self) -> bool
        recommends self.structure()
    {
        &&& forall |i:nat| i < self.lines.len() ==> (#[trigger] self.lines[i as int].wf())
        &&& forall |i:nat| i < self.lines.len() ==> (#[trigger] self.lines[i as int].linked.acyclic())
        &&& forall |i:nat| i < self.lines.len()-1 ==> 
            (#[trigger] self.lines[i as int].linked.root().buffers).valid(self.linked.buffer_dv)
        &&& forall |i:nat| i < self.lines.len()-1 ==> (#[trigger] self.node(i as int).key_in_domain(self.key))
    }

    pub open spec(checked) fn child_linked_at(self, i: int) -> bool
        recommends self.structure(), self.all_lines_wf(), 0 <= i < self.lines.len()-1
    {
        self.lines[i+1].linked.root == self.node(i).child_ptr(self.key)
    }

    pub open spec(checked) fn result_at(self, i: int) -> Message
        recommends 0 <= i < self.lines.len()
    {
        self.lines[i].result
    }

    pub open spec/*XXX(checked)*/ fn result_linked_at(self, i: int) -> bool
        recommends self.structure(), self.all_lines_wf(), 0 <= i < self.lines.len()-1
    {
        let start = self.node(i).flushed_ofs(self.key);
        let msg = self.node(i).buffers.query_from(self.linked.buffer_dv, self.key, start as int);
        self.lines[i].result == self.result_at(i+1).merge(msg)
    }

    pub open spec(checked) fn result(self) -> Message
        recommends self.structure()
    {
        self.result_at(0)
    }

    pub open spec(checked) fn valid(self) -> bool
    {
        &&& self.structure()
        &&& self.all_lines_wf()
        &&& forall |i| 0 <= i < self.lines.len()-1 ==> #[trigger] self.child_linked_at(i)
        &&& forall |i| 0 <= i < self.lines.len()-1 ==> #[trigger] self.result_linked_at(i)
    }

    pub open spec(checked) fn valid_for(self, linked: LinkedBetree<T>, key: Key) -> bool
    {
        &&& self.valid()
        &&& self.linked == linked
        &&& self.key == key
    }
} // end impl<T: Queryable> QueryReceipt

pub type PathAddrs = Seq<Address>;

pub struct Path<T>{
    pub linked: LinkedBetree<T>,
    pub key: Key,
    pub depth: nat
}

impl<T: QueryableDisk> Path<T>{
    pub open spec(checked) fn subpath(self) -> Path<T>
        recommends 
            0 < self.depth, 
            self.linked.has_root(), 
            self.linked.root().key_in_domain(self.key)
    {
        Path{ linked: self.linked.child_for_key(self.key), key: self.key, depth: (self.depth - 1) as nat }
    }

    pub open spec(checked) fn valid(self) -> bool
        decreases self.depth
    {
        &&& self.linked.has_root()
        &&& self.linked.acyclic()
        &&& self.linked.root().key_in_domain(self.key)
        &&& (0 < self.depth ==> self.linked.root() is index)
        &&& (0 < self.depth ==> self.subpath().valid())
    }

    pub open spec(checked) fn target(self) -> LinkedBetree<T>
        recommends self.valid()
        decreases self.depth
    {
        if self.depth == 0 {
            self.linked
        } else {
            self.subpath().target()
        }
    }

    pub open spec(checked) fn addrs_on_path(self) -> Set<Address>
        recommends self.valid()
        decreases self.depth
    {
        if self.depth == 0 {
            set!{self.linked.root.unwrap()}
        } else {
            self.subpath().addrs_on_path() + set!{self.linked.root.unwrap()}
        }
    }

    pub open spec/*XXX(checked)*/ fn can_substitute(self, replacement: LinkedBetree<T>, path_addrs: PathAddrs) -> bool
    {
        &&& self.valid()
        &&& self.target().has_root()
        &&& replacement.wf()
        &&& replacement.has_root()
        &&& replacement.root().my_domain() == self.target().root().my_domain()
        &&& self.depth == path_addrs.len()
        &&& self.linked.dv.is_sub_disk(replacement.dv)
        &&& self.linked.buffer_dv.is_sub_disk(&replacement.buffer_dv)
    }

    pub open spec/*XXX (checked)*/ fn substitute(self, replacement: LinkedBetree<T>, path_addrs: PathAddrs) -> LinkedBetree<T>
        recommends self.can_substitute(replacement, path_addrs)
        decreases self.depth, 1nat
    {
        if self.depth == 0 {
            replacement
        } else {
            let node = self.linked.root();
            let subtree = self.subpath().substitute(replacement, path_addrs.subrange(1, path_addrs.len() as int));
            let new_children = node.children.update(node.pivots.route(self.key), subtree.root);
            let new_node = BetreeNode{ children: new_children, ..node };
            let new_dv = subtree.dv.modify_disk(path_addrs[0], new_node);
            LinkedBetree{ root: Some(path_addrs[0]), dv: new_dv, buffer_dv: replacement.buffer_dv }
        }
    }
} // end impl<T: Queryable> Path

state_machine!{ LinkedBetreeVars {
    fields {
        pub memtable: Memtable,
        pub linked: LinkedBetree<BufferDisk>,
    }

    pub enum Label
    {
        Query{end_lsn: LSN, key: Key, value: Value},
        Put{puts: MsgHistory},
        FreezeAs{stamped_betree: StampedBetree},
        Internal{},   // Local No-op label
    }

    transition!{ query(lbl: Label, receipt: QueryReceipt<BufferDisk>) {
        require let Label::Query{end_lsn, key, value} = lbl;
        require end_lsn == pre.memtable.seq_end;
        require receipt.valid_for(pre.linked, key);
        require Message::Define{value} == receipt.result().merge(pre.memtable.query(key));
    }}

    transition!{ put(lbl: Label) {
        require let Label::Put{puts} = lbl;
        require puts.wf();
        require puts.seq_start == pre.memtable.seq_end;
        update memtable = pre.memtable.apply_puts(puts);
    }}

    transition!{ freeze_as(lbl: Label) {
        require let Label::FreezeAs{stamped_betree} = lbl;
        require pre.memtable is empty;
        require stamped_betree == Stamped{value: pre.linked, seq_end: pre.memtable.seq_end};
    }}

    transition!{ internal_flush_memtable(lbl: Label, new_addrs: TwoAddrs) {
        require let Label::Internal{} = lbl;
        require new_addrs.no_duplicates();
        require pre.linked.is_fresh(new_addrs.repr());

        update memtable = pre.memtable.drain();
        update linked = pre.linked.push_memtable(pre.memtable, new_addrs);
    }}

    transition!{ internal_grow(lbl: Label, new_root_addr: Address) {
        require let Label::Internal{} = lbl;
        require pre.linked.is_fresh(Set::empty().insert(new_root_addr));
        update linked = pre.linked.grow(new_root_addr);
    }}

    transition!{ internal_split(lbl: Label, new_linked: LinkedBetree<BufferDisk>, path: Path<BufferDisk>, 
            request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path_addrs.no_duplicates();
        require path.depth == path_addrs.len();
        require path.target().can_split_parent(request);

        require new_addrs.no_duplicates();
        require new_addrs.repr().disjoint(path_addrs.to_set());

        require path.linked == pre.linked;
        require pre.linked.is_fresh(new_addrs.repr());
        require pre.linked.is_fresh(path_addrs.to_set());

        let splitted = path.substitute(path.target().split_parent(request, new_addrs), path_addrs);
        require splitted.subtree_same_tightness(new_linked);

        update linked = new_linked;
    }}

    transition!{ internal_flush(lbl: Label, new_linked: LinkedBetree<BufferDisk>, path: Path<BufferDisk>, 
            child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path_addrs.no_duplicates();
        require path.depth == path_addrs.len();
        require path.target().can_flush(child_idx, buffer_gc);

        require new_addrs.no_duplicates();
        require new_addrs.repr().disjoint(path_addrs.to_set());

        require path.linked == pre.linked;
        require pre.linked.is_fresh(new_addrs.repr());
        require pre.linked.is_fresh(path_addrs.to_set());

        let flushed = path.substitute(path.target().flush(child_idx, buffer_gc, new_addrs), path_addrs);
        require flushed.subtree_same_tightness(new_linked);

        update linked = new_linked;
    }}

    transition!{ internal_compact(lbl: Label, new_linked: LinkedBetree<BufferDisk>, path: Path<BufferDisk>, 
            start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) {
        require let Label::Internal{} = lbl;
        require path.valid();
        require path_addrs.no_duplicates();
        require path.depth == path_addrs.len();
        require path.target().can_compact(start, end, compacted_buffer);

        require new_addrs.no_duplicates();
        require new_addrs.repr().disjoint(path_addrs.to_set());

        require path.linked == pre.linked;
        require pre.linked.is_fresh(new_addrs.repr());
        require pre.linked.is_fresh(path_addrs.to_set());
        
        let compacted = path.substitute(path.target().compact(start, end, compacted_buffer, new_addrs), path_addrs);
        require compacted.subtree_same_tightness(new_linked);

        update linked = new_linked;
    }}

    transition!{ internal_noop(lbl: Label) {
        require let Label::Internal{} = lbl;
    }}

    init!{ initialize(stamped_betree: StampedBetree) {
        require stamped_betree.value.wf();
        init memtable = Memtable::empty_memtable(stamped_betree.seq_end);
        init linked = stamped_betree.value;
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.linked.acyclic()
        &&& self.linked.valid_buffer_dv()
        &&& self.linked.has_root() ==> self.linked.root().my_domain() == total_domain()
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, receipt: QueryReceipt<BufferDisk>) { }
   
    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(freeze_as)]
    fn freeze_as_inductive(pre: Self, post: Self, lbl: Label) { }

    #[inductive(internal_flush_memtable)]
    fn internal_flush_memtable_inductive(pre: Self, post: Self, lbl: Label, new_addrs: TwoAddrs) {
        // assume(false);
        let ranking = pre.linked.the_ranking();
        let pushed = pre.linked.push_memtable(pre.memtable, new_addrs);
        let pushed_ranking = pre.linked.push_memtable_new_ranking(pre.memtable, new_addrs, ranking);

        assert(pushed.acyclic());
        assert(pushed.buffer_dv.wf());
        assert(pushed.dv.is_fresh(pushed.buffer_dv.repr()));

        let buffer_addrs = pre.linked.reachable_buffer_addrs();
        let post_buffer_addrs = pushed.reachable_buffer_addrs();
        
        assert forall |addr| post_buffer_addrs.contains(addr) && addr != new_addrs.addr2
        implies #[trigger] buffer_addrs.contains(addr)
        by {
            if pushed.root().active_buffers().contains(addr) {
                reveal(BetreeNode::active_buffers);
                assert(pre.linked.has_root());
                assert(pre.linked.root().active_buffers().contains(addr));
                pre.linked.reachable_betree_addrs_using_ranking_closed(ranking);
                assert(pre.linked.reachable_buffer(pre.linked.root.unwrap(), addr));
                assert(buffer_addrs.contains(addr));
            } else {
                let tree_addr = choose |tree_addr| pushed.reachable_buffer(tree_addr, addr);
                let i = pushed.non_root_buffers_belongs_to_child(tree_addr, addr);
                pre.linked.same_child_same_reachable_buffers(pushed, i, i, pushed_ranking);
            }
        }
        assert(pushed.no_dangling_buffer_ptr());
    }
   
    #[inductive(internal_grow)]
    fn internal_grow_inductive(pre: Self, post: Self, lbl: Label, new_root_addr: Address) { 
        // assume(false);

        let old_ranking = pre.linked.finite_ranking();
        pre.linked.finite_ranking_ensures();

        let new_rank = 
            if pre.linked.has_root() { old_ranking[pre.linked.root.unwrap()]+1 } 
            else if old_ranking =~= map![] { 1 }
            else { get_max_rank(old_ranking) + 1 };

        let new_ranking = old_ranking.insert(new_root_addr, new_rank);
        assert(post.linked.valid_ranking(new_ranking));

        let post_child = post.linked.child_at_idx(0);
        assert(post_child.reachable_buffer_addrs() == pre.linked.reachable_buffer_addrs()) by {
            assert(post_child.valid_ranking(new_ranking)); // trigger?
            post_child.agreeable_disks_same_reachable_betree_addrs(pre.linked, new_ranking);
            post_child.reachable_betree_addrs_ignore_ranking(post_child.the_ranking(), new_ranking);
            pre.linked.reachable_betree_addrs_ignore_ranking(pre.linked.the_ranking(), new_ranking);
            post_child.same_reachable_betree_addrs_implies_same_buffer_addrs(pre.linked);
        }

        assert forall |addr| post.linked.reachable_buffer_addrs().contains(addr)
        implies #[trigger]  pre.linked.reachable_buffer_addrs().contains(addr)
        by {
            reveal(BetreeNode::active_buffers);
            let tree_addr = choose |tree_addr| post.linked.reachable_buffer(tree_addr, addr);
            let i = post.linked.non_root_buffers_belongs_to_child(tree_addr, addr);
            assert(i == 0);
        }
        assert(post.linked.no_dangling_buffer_ptr());
    }

    #[inductive(internal_split)]
    fn internal_split_inductive(pre: Self, post: Self, lbl: Label, new_linked: LinkedBetree<BufferDisk>, path: Path<BufferDisk>, 
        request: SplitRequest, new_addrs: SplitAddrs, path_addrs: PathAddrs) {
            // assume(false);

        let ranking = pre.linked.finite_ranking();
        path.target_ensures();
        path.valid_ranking_throughout(ranking);

        let new_subtree = path.target().split_parent(request, new_addrs);
        let new_ranking = path.target().split_new_ranking(request, new_addrs, ranking);

        let splitted = path.substitute(new_subtree, path_addrs);
        path.substitute_ensures(new_subtree, path_addrs);

        assert(post.linked.acyclic()) by {
            let _ = path.ranking_after_substitution(new_subtree, path_addrs, new_ranking);
            splitted.subtree_same_tightness_preserves_acyclicity(new_linked);
        }

        assert(post.linked.valid_buffer_dv()) by {
            path.target().split_parent_same_reachable_buffers(request, new_addrs, new_ranking);
            path.substitute_reachable_buffers_ensures(new_subtree, path_addrs, new_ranking);
            assert(splitted.no_dangling_buffer_ptr());
            assert(splitted.valid_buffer_dv());
            splitted.subtree_same_tightness_preserves_valid_buffer_dv(post.linked);
        }
     
        assert(post.linked.has_root() ==> post.linked.root().my_domain() == total_domain());
    }
   
    #[inductive(internal_flush)]
    fn internal_flush_inductive(pre: Self, post: Self, lbl: Label, new_linked: LinkedBetree<BufferDisk>, path: Path<BufferDisk>, 
        child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, path_addrs: PathAddrs) {

        let ranking = pre.linked.finite_ranking();
        path.target_ensures();

        path.valid_ranking_throughout(ranking); // seems to be here?
        // assume(false);

        let new_subtree = path.target().flush(child_idx, buffer_gc, new_addrs);
        let new_ranking = path.target().flush_new_ranking(child_idx, buffer_gc, new_addrs, ranking);
    
        let flushed = path.substitute(new_subtree, path_addrs);
        path.substitute_ensures(new_subtree, path_addrs);

        assert(post.linked.acyclic()) by {
            let _ = path.ranking_after_substitution(new_subtree, path_addrs, new_ranking);
            flushed.subtree_same_tightness_preserves_acyclicity(new_linked);
        }

        assert(post.linked.valid_buffer_dv()) by {
            path.target().flush_keeps_subset_reachable_buffers(child_idx, buffer_gc, new_addrs, new_ranking);
            path.substitute_reachable_buffers_ensures(new_subtree, path_addrs, new_ranking);
            assert(flushed.no_dangling_buffer_ptr());
            assert(flushed.valid_buffer_dv());
            flushed.subtree_same_tightness_preserves_valid_buffer_dv(post.linked);
        }

        assert(post.linked.has_root() ==> post.linked.root().my_domain() == total_domain());
    }
   
    #[inductive(internal_compact)]
    fn internal_compact_inductive(pre: Self, post: Self, lbl: Label, new_linked: LinkedBetree<BufferDisk>, path: Path<BufferDisk>, 
        start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs, path_addrs: PathAddrs) {

        // NOTE(JL): somehow really needs other context to verify
        // some context is not brought in properly???

        let ranking = pre.linked.finite_ranking();
        // pre.linked.finite_ranking_ensures();

        path.target_ensures();
        path.valid_ranking_throughout(ranking);

        let new_subtree = path.target().compact(start, end, compacted_buffer, new_addrs);
        let new_ranking = path.target().compact_new_ranking(start, end, compacted_buffer, new_addrs, ranking);
        
        // obvious facts cannot be proven
        // assert(pre.linked.dv.is_fresh(path_addrs.to_set()));
        // assert(path_addrs.to_set().disjoint(new_ranking.dom()));
        // path.target().compact_ensures(start, end, compacted_buffer, new_addrs);

        // ??????? why ?????? 
        // assert(pre.linked.dv == path.target().dv);
        // assert(new_subtree.dv.is_fresh(path_addrs.to_set()));
        // assert(new_subtree.wf());
        // assert(new_subtree.has_root());
        // assert(new_subtree.root().my_domain() == path.target().root().my_domain());
        // assert(path.linked.dv.is_sub_disk(new_subtree.dv));
        // assert(path.linked.buffer_dv.is_sub_disk(new_subtree.buffer_dv));
        assert(path.can_substitute(new_subtree, path_addrs));

        let compacted = path.substitute(new_subtree, path_addrs);
        path.substitute_ensures(new_subtree, path_addrs);

        assert(post.linked.acyclic()) by {
            assert(new_subtree.valid_ranking(new_ranking));
            // assert(path_addrs.to_set().disjoint(new_ranking.dom()));
            assert(path.ranking_for_substitution(new_subtree, path_addrs, new_ranking));
            let _ = path.ranking_after_substitution(new_subtree, path_addrs, new_ranking);
            compacted.subtree_same_tightness_preserves_acyclicity(new_linked);
        }

        assert(post.linked.valid_buffer_dv()) by {
            assume(new_subtree.reachable_buffer_addrs() <= path.target().reachable_buffer_addrs() + new_addrs.repr());
            path.substitute_reachable_buffers_ensures(new_subtree, path_addrs, new_ranking);
            assert(compacted.no_dangling_buffer_ptr());
            assert(compacted.valid_buffer_dv());
            compacted.subtree_same_tightness_preserves_valid_buffer_dv(post.linked);
        }

        assert(post.linked.has_root() ==> post.linked.root().my_domain() == total_domain());
    }

    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) { }
   
    #[inductive(initialize)]
    fn initialize_inductive(post: Self, stamped_betree: StampedBetree) { 
        assume(post.linked.acyclic());
        assume(post.linked.has_root() ==> post.linked.root().my_domain() == total_domain());
        assume(post.linked.valid_buffer_dv());
    }
}} // end LinkedBetree state machine

// utility & invariant proof functions

// TODO(JL): unstable
proof fn get_max_rank(ranking: Ranking) -> (max: nat)
    requires ranking.dom().finite()
    ensures forall |addr| #[trigger] ranking.contains_key(addr) ==> ranking[addr] <= max
    decreases ranking.dom().len()
{
    assume(false);
    if ranking.dom() is empty {
        assert forall |addr| #[trigger] ranking.contains_key(addr) 
        implies ranking[addr] <= 0 by { assert(false); }
        0
    } else {
        let curr_addr = ranking.dom().choose();
        let sub_ranking = ranking.remove(curr_addr);
        let other_max = get_max_rank(sub_ranking);

        if ranking[curr_addr] > other_max {
            assert forall |addr| sub_ranking.contains_key(addr) ==> ranking.contains_key(addr) by {}
            ranking[curr_addr]
        } else {
            assert forall |addr| #[trigger] ranking.contains_key(addr)
            implies ranking[addr] <= other_max 
            by {
                if addr != curr_addr {
                    assert(sub_ranking.contains_key(addr)); // trigger
                } else {
                    assert(ranking[curr_addr] <= other_max);
                }
            }
            other_max
        }
    }
}

pub proof fn path_addrs_to_set_additive(path_addrs: PathAddrs)
    requires path_addrs.len() > 0
    ensures path_addrs.to_set() == set![path_addrs[0]] + path_addrs.subrange(1, path_addrs.len() as int).to_set()
{
    let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
    let a = set![path_addrs[0]] + sub_path_addrs.to_set();
    let b = path_addrs.to_set();

    // TODO(verus): lack additive seq to set lemma
    assert forall |addr| a.contains(addr) <==> b.contains(addr)
    by {
        if a.contains(addr) {
            if sub_path_addrs.contains(addr) {
                let idx = choose |idx| 0 <= idx < sub_path_addrs.len() && sub_path_addrs[idx] == addr;
                assert(sub_path_addrs[idx] == path_addrs[idx + 1]);
            }
        }
        if b.contains(addr) {
            let idx = choose |idx| 0 <= idx < path_addrs.len() && path_addrs[idx] == addr;
            if idx > 0 {
                assert(sub_path_addrs[idx-1] == path_addrs[idx]);
            }
        }
    }
    assert(a =~= b);
}

// proofs used by invariant

impl<T> LinkedBetree<T> {
    pub proof fn child_at_idx_acyclic(self, idx: nat)
        requires 
            self.acyclic(), 
            self.has_root(), 
            self.root().valid_child_index(idx)
        ensures 
            self.child_at_idx(idx).acyclic()
    {
        assert(self.child_at_idx(idx).valid_ranking(self.the_ranking()));
    }

    pub open spec(checked) fn child_subtree_contains_addr(self, ranking: Ranking, addr: Address, start: nat, i: nat) -> bool
        recommends self.wf(), self.valid_ranking(ranking)
    {
        &&& start <= i < self.child_count()
        &&& self.child_at_idx(i).valid_ranking(ranking)
        &&& self.child_at_idx(i).reachable_betree_addrs_using_ranking(ranking).contains(addr)
    }

    #[verifier::opaque]
    pub closed spec(checked) fn exists_child_subtree_contains_addr(self, ranking: Ranking, addr: Address, start: nat) -> bool
        recommends self.wf(), self.valid_ranking(ranking)
    {
        exists |i| self.child_subtree_contains_addr(ranking, addr, start, i)
    }

    proof fn get_child_given_betree_addr(self, ranking: Ranking, addr: Address, start: nat) -> (i: nat)
        requires
            self.wf(), 
            self.valid_ranking(ranking),
            self.exists_child_subtree_contains_addr(ranking, addr, start),
        ensures 
            self.child_subtree_contains_addr(ranking, addr, start, i),
    {
        reveal(LinkedBetree::exists_child_subtree_contains_addr);
        let i = choose |i| self.child_subtree_contains_addr(ranking, addr, start, i);
        i
    }

    proof fn reachable_betree_addrs_using_ranking_recur_lemma(self, ranking: Ranking, child_idx: nat)
        requires self.can_recurse_for_reachable(ranking, child_idx)
        ensures ({
            let reachable_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, child_idx);
            &&& reachable_addrs <= self.dv.entries.dom()
            &&& forall |addr| reachable_addrs.contains(addr) ==> 
                #[trigger] self.exists_child_subtree_contains_addr(ranking, addr, child_idx)
            &&& forall |i| child_idx <= i < self.child_count() ==>
                #[trigger] self.child_at_idx(i).reachable_betree_addrs_using_ranking(ranking) <= reachable_addrs
        })
        decreases 
            self.get_rank(ranking),
            self.child_count() - child_idx,
    {
        let reachable_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, child_idx);
        if child_idx < self.child_count() {
            assert(self.root().valid_child_index(child_idx)); // trigger

            let child = self.child_at_idx(child_idx);
            let child_addrs = child.reachable_betree_addrs_using_ranking(ranking);
            let right_subtree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, child_idx+1);

            child.reachable_betree_addrs_using_ranking_closed(ranking);
            self.reachable_betree_addrs_using_ranking_recur_lemma(ranking, child_idx+1);

            assert(reachable_addrs <= self.dv.entries.dom());
            assert forall |addr| reachable_addrs.contains(addr)
            implies #[trigger] self.exists_child_subtree_contains_addr(ranking, addr, child_idx)
            by {
                if child_addrs.contains(addr) {
                    assert(self.child_subtree_contains_addr(ranking, addr, child_idx, child_idx));
                } else {
                    assert(right_subtree_addrs.contains(addr));
                    let i = self.get_child_given_betree_addr(ranking, addr, child_idx+1);
                    assert(self.child_subtree_contains_addr(ranking, addr, child_idx, i));
                }
                reveal(LinkedBetree::exists_child_subtree_contains_addr);
            }
        }
    }

    proof fn reachable_betree_addrs_using_ranking_closed(self, ranking: Ranking)
        requires self.wf(), self.valid_ranking(ranking)
        ensures ({
            let reachable_addrs = self.reachable_betree_addrs_using_ranking(ranking);
            &&& reachable_addrs <= self.dv.entries.dom()
            &&& self.has_root() ==> reachable_addrs.contains(self.root.unwrap())
            &&& forall |addr| reachable_addrs.contains(addr) && Some(addr) != self.root
                ==> #[trigger] self.exists_child_subtree_contains_addr(ranking, addr, 0)
        })
        decreases self.get_rank(ranking)
    {
        if self.has_root() {
            let sub_tree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, 0);
            self.reachable_betree_addrs_using_ranking_recur_lemma(ranking, 0);
            assert(sub_tree_addrs.insert(self.root.unwrap()) =~= self.reachable_betree_addrs_using_ranking(ranking));
        }
    }

    proof fn agreeable_disks_same_reachable_betree_addrs_recur_lemma(self, other: LinkedBetree<T>, ranking: Ranking, child_idx: nat)
        requires
            self.can_recurse_for_reachable(ranking, child_idx),
            other.can_recurse_for_reachable(ranking, child_idx),
            self.root == other.root,
            self.dv.agrees_with_disk(other.dv),
        ensures
            self.reachable_betree_addrs_using_ranking_recur(ranking, child_idx) 
            == other.reachable_betree_addrs_using_ranking_recur(ranking, child_idx),
        decreases 
            self.get_rank(ranking),
            self.child_count() - child_idx,
    {
        if child_idx < self.child_count() {
            let reachable = self.reachable_betree_addrs_using_ranking_recur(ranking, child_idx);
            let other_reachable = other.reachable_betree_addrs_using_ranking_recur(ranking, child_idx);

            let child = self.child_at_idx(child_idx);
            let other_child = other.child_at_idx(child_idx);
            assert(self.root().valid_child_index(child_idx)); // trigger

            child.agreeable_disks_same_reachable_betree_addrs(other_child, ranking);
            self.agreeable_disks_same_reachable_betree_addrs_recur_lemma(other, ranking, child_idx+1);
            assert(reachable =~= other_reachable);
        }
    }

    // subdisk same reachable
    proof fn agreeable_disks_same_reachable_betree_addrs(self, other: LinkedBetree<T>, ranking: Ranking)
        requires 
            self.wf(), 
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.root == other.root,
            self.dv.agrees_with_disk(other.dv),
        ensures
            self.reachable_betree_addrs_using_ranking(ranking)
            == other.reachable_betree_addrs_using_ranking(ranking)
        decreases 
            self.get_rank(ranking)
    {
        if self.has_root() {
            let sub_tree_addrs = self.reachable_betree_addrs_using_ranking_recur(ranking, 0);
            self.agreeable_disks_same_reachable_betree_addrs_recur_lemma(other, ranking, 0);
        }
    }

    proof fn reachable_betree_addrs_ignore_ranking_recur_lemma(self, r1: Ranking, r2: Ranking, child_idx: nat)
        requires 
            self.can_recurse_for_reachable(r1, child_idx),
            self.valid_ranking(r2),
        ensures 
            self.reachable_betree_addrs_using_ranking_recur(r1, child_idx) 
            == self.reachable_betree_addrs_using_ranking_recur(r2, child_idx)
        decreases 
            self.get_rank(r1),
            self.child_count() - child_idx,
    {
        if child_idx < self.child_count() {
            let r1_addrs = self.reachable_betree_addrs_using_ranking_recur(r1, child_idx);
            let r2_addrs = self.reachable_betree_addrs_using_ranking_recur(r2, child_idx);

            let child = self.child_at_idx(child_idx);
            assert(self.root().valid_child_index(child_idx)); // trigger

            child.reachable_betree_addrs_ignore_ranking(r1, r2);
            self.reachable_betree_addrs_ignore_ranking_recur_lemma(r1, r2, child_idx+1);
            assert(r1_addrs =~= r2_addrs);
        }
    }

    // rankings same reachable
    pub proof fn reachable_betree_addrs_ignore_ranking(self, r1: Ranking, r2: Ranking)
        requires 
            self.wf(), 
            self.valid_ranking(r1), 
            self.valid_ranking(r2),
        ensures 
            self.reachable_betree_addrs_using_ranking(r1) == self.reachable_betree_addrs_using_ranking(r2)
        decreases 
            self.get_rank(r1)
    {
        if self.has_root() {
            self.reachable_betree_addrs_ignore_ranking_recur_lemma(r1, r2, 0);
        }
    }

    // reachable buffer lemmas
    proof fn sub_reachable_betree_addrs_implies_sub_buffer_addrs(self, other: LinkedBetree<T>)
        requires 
            self.acyclic(),
            other.acyclic(),
            self.dv.agrees_with_disk(other.dv),
            self.reachable_betree_addrs() <= other.reachable_betree_addrs(),
        ensures
            self.reachable_buffer_addrs() <= other.reachable_buffer_addrs(),
    {
        let buffer_addrs = self.reachable_buffer_addrs();
        let other_buffer_addrs = other.reachable_buffer_addrs();

        assert forall |addr| buffer_addrs.contains(addr)
        implies other_buffer_addrs.contains(addr)
        by {
            let tree_addr = choose |tree_addr| self.reachable_buffer(tree_addr, addr);
            self.reachable_betree_addrs_using_ranking_closed(self.the_ranking());
            other.reachable_betree_addrs_using_ranking_closed(other.the_ranking());
            assert(other.dv.entries.contains_key(tree_addr)); // trigger
            assert(other.reachable_buffer(tree_addr, addr));
        }
    }

    proof fn same_reachable_betree_addrs_implies_same_buffer_addrs(self, other: LinkedBetree<T>)
        requires 
            self.acyclic(),
            other.acyclic(),
            self.dv.agrees_with_disk(other.dv),
            self.reachable_betree_addrs() == other.reachable_betree_addrs(),
        ensures
            self.reachable_buffer_addrs() == other.reachable_buffer_addrs(),
    {
        let buffer_addrs = self.reachable_buffer_addrs();
        let other_buffer_addrs = other.reachable_buffer_addrs();

        assert forall |addr| other_buffer_addrs.contains(addr)
        implies buffer_addrs.contains(addr)
        by {
            let tree_addr = choose |tree_addr| other.reachable_buffer(tree_addr, addr);
            other.reachable_betree_addrs_using_ranking_closed(other.the_ranking());
            assert(other.dv.entries.contains_key(tree_addr));

            self.reachable_betree_addrs_using_ranking_closed(self.the_ranking());
            assert(self.dv.entries.contains_key(tree_addr));
    
            assert(self.reachable_betree_addrs().contains(tree_addr));
            assert(self.dv.get(Some(tree_addr)) == other.dv.get(Some(tree_addr)));
            assert(self.reachable_buffer(tree_addr, addr));
        }

        self.sub_reachable_betree_addrs_implies_sub_buffer_addrs(other);
        assert(buffer_addrs =~= other_buffer_addrs);
    }

    proof fn non_root_buffers_belongs_to_child(self, tree_addr: Address, buffer_addr: Address) -> (i: nat)
        requires 
            self.acyclic(),
            self.has_root(),
            self.root.unwrap() != tree_addr,
            self.reachable_buffer(tree_addr, buffer_addr),
        ensures
            self.root().valid_child_index(i),
            self.child_at_idx(i).acyclic(),
            self.child_at_idx(i).reachable_buffer_addrs().contains(buffer_addr),
    {
        let ranking = self.the_ranking();
        self.reachable_betree_addrs_using_ranking_closed(ranking);
        let child_idx = self.get_child_given_betree_addr(ranking, tree_addr, 0);

        let child = self.child_at_idx(child_idx);
        self.child_at_idx_acyclic(child_idx);
        child.reachable_betree_addrs_ignore_ranking(ranking, child.the_ranking());
        assert(child.reachable_betree_addrs().contains(tree_addr));
        assert(child.reachable_buffer(tree_addr, buffer_addr));

        child_idx
    }

    proof fn child_at_idx_reachable_addrs_ensures(self, child_idx: nat)
        requires 
            self.acyclic(), 
            self.has_root(),
            self.root().valid_child_index(child_idx),
        ensures 
            self.child_at_idx(child_idx).acyclic(),
            self.child_at_idx(child_idx).reachable_betree_addrs() <= self.reachable_betree_addrs(),
            self.child_at_idx(child_idx).reachable_buffer_addrs() <= self.reachable_buffer_addrs(),
    {
        let ranking = self.the_ranking();
        let child = self.child_at_idx(child_idx);

        assert(child.valid_ranking(ranking));
        self.reachable_betree_addrs_using_ranking_recur_lemma(ranking, 0);
        assert(child.reachable_betree_addrs_using_ranking(ranking) <= self.reachable_betree_addrs_using_ranking(ranking));
        child.reachable_betree_addrs_ignore_ranking(ranking, child.the_ranking());
        child.sub_reachable_betree_addrs_implies_sub_buffer_addrs(self);
    }

    proof fn same_child_same_reachable_buffers(self, other: LinkedBetree<T>, idx: nat, other_idx: nat, ranking: Ranking)
        requires 
            self.has_root(),
            other.has_root(),
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.root().valid_child_index(idx),
            other.root().valid_child_index(other_idx),
            self.child_at_idx(idx).root == other.child_at_idx(other_idx).root,
            self.dv.agrees_with_disk(other.dv),
        ensures ({
            let child = self.child_at_idx(idx);
            let other_child = other.child_at_idx(other_idx);

            &&& child.acyclic()
            &&& other_child.acyclic()
            // &&& child.reachable_betree_addrs() == other.reachable_betree_addrs()
            &&& child.reachable_buffer_addrs() == other_child.reachable_buffer_addrs()
            &&& child.reachable_buffer_addrs() <= self.reachable_buffer_addrs()
            &&& other_child.reachable_buffer_addrs() <= other.reachable_buffer_addrs()
        })
    {
        let child = self.child_at_idx(idx);
        let other_child = other.child_at_idx(other_idx);

        self.child_at_idx_reachable_addrs_ensures(idx);
        other.child_at_idx_reachable_addrs_ensures(other_idx);

        child.reachable_betree_addrs_ignore_ranking(child.the_ranking(), ranking);
        other_child.reachable_betree_addrs_ignore_ranking(other_child.the_ranking(), ranking);

        child.agreeable_disks_same_reachable_betree_addrs(other_child, ranking);
        child.same_reachable_betree_addrs_implies_same_buffer_addrs(other_child);
    }

    pub proof fn split_new_ranking(self, request: SplitRequest, new_addrs: SplitAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(), self.has_root(),
            self.valid_ranking(ranking),
            self.can_split_parent(request),
            self.dv.is_fresh(new_addrs.repr()),
            new_addrs.no_duplicates(),
        ensures 
            self.valid_ranking(new_ranking),
            self.split_parent(request, new_addrs).valid_ranking(new_ranking),
            new_ranking.dom() == ranking.dom() + new_addrs.repr()
    {
        let child_idx = request.xxxget_child_idx();
        let child_addr = self.root().children[child_idx as int].unwrap();
        let result = self.split_parent(request, new_addrs);
        self.root().pivots.insert_wf(child_idx as int + 1, self.split_element(request));
        assert(result.root().wf());

        let new_addr_ranks = map![
            new_addrs.left => ranking[child_addr], 
            new_addrs.right => ranking[child_addr],
            new_addrs.parent => ranking[self.root.unwrap()],
        ];
        let new_ranking = ranking.union_prefer_right(new_addr_ranks);

        let child = self.dv.entries[child_addr];
        let new_left_child = result.dv.entries[new_addrs.left];
        let new_right_child = result.dv.entries[new_addrs.right];
        let delta = if request is SplitLeaf { 0 } else { request->child_pivot_idx };
        
        assert(forall |i| new_left_child.valid_child_index(i) ==> child.valid_child_index(i)); // trigger for a bunch of disk properties
        assert(forall |i| new_right_child.valid_child_index(i) ==> child.valid_child_index(i+delta)); // trigger for a bunch of disk properties
        
        assert forall |i| result.root().valid_child_index(i)
        implies ({
            let child_ptr = result.root().children[i as int];
            &&& result.dv.is_nondangling_ptr(child_ptr)
            &&& result.dv.child_linked(result.root(), i)
            &&& child_ptr is Some ==> {
                &&& new_ranking.contains_key(child_ptr.unwrap())
                &&& new_ranking[child_ptr.unwrap()] < new_ranking[result.root.unwrap()]
            }
        }) by {
            if i < child_idx {
                assert(self.root().valid_child_index(i));
            } else if i < child_idx + 1 {
                // case for new left child & new right child
            } else {
                assert(self.root().valid_child_index((i-1) as nat));
            }
        }
        assert(result.dv.wf());
        assert(result.dv.node_children_respects_rank(new_ranking, new_addrs.left));
        assert(result.dv.node_children_respects_rank(new_ranking, new_addrs.right));
        assert(result.dv.node_children_respects_rank(new_ranking, new_addrs.parent));
        assert(self.dv.valid_ranking(new_ranking));
        assert(new_ranking.dom() =~= ranking.dom() + new_addrs.repr());
        new_ranking
    }

    proof fn split_leaf_preserves_reachable_buffers(self, other: LinkedBetree<T>, ranking: Ranking)
        requires 
            self.has_root(),
            other.has_root(),
            self.valid_ranking(ranking),
            other.valid_ranking(ranking),
            self.root().buffers == other.root().buffers,
            self.root().flushed == other.root().flushed,
            self.root().children == other.root().children,
            self.dv.agrees_with_disk(other.dv),
        ensures 
            self.reachable_buffer_addrs() == other.reachable_buffer_addrs(),
    {
        assert forall |addr| self.reachable_buffer_addrs().contains(addr) 
            <==> other.reachable_buffer_addrs().contains(addr) 
        by {
            if self.root().active_buffers().contains(addr) 
                || other.root().active_buffers().contains(addr) 
            {
                reveal(BetreeNode::active_buffers);
                self.reachable_betree_addrs_using_ranking_closed(ranking);
                other.reachable_betree_addrs_using_ranking_closed(ranking);
                assert(self.reachable_buffer(self.root.unwrap(), addr));
                assert(other.reachable_buffer(other.root.unwrap(), addr));
            } else if self.reachable_buffer_addrs().contains(addr) {
                let tree_addr = choose |tree_addr| self.reachable_buffer(tree_addr, addr);
                let i = self.non_root_buffers_belongs_to_child(tree_addr, addr);
                self.same_child_same_reachable_buffers(other, i, i, ranking);
            } else if other.reachable_buffer_addrs().contains(addr) {
                let tree_addr = choose |tree_addr| other.reachable_buffer(tree_addr, addr);
                let i = other.non_root_buffers_belongs_to_child(tree_addr, addr);
                self.same_child_same_reachable_buffers(other, i, i, ranking);
            }
        }
        assert(self.reachable_buffer_addrs() =~= other.reachable_buffer_addrs());
    }

    proof fn split_index_preserves_reachable_buffers(self, left: LinkedBetree<T>, 
            right: LinkedBetree<T>, pivot_idx: nat, ranking: Ranking)
        requires 
            self.has_root(),
            left.has_root(),
            right.has_root(),
            self.valid_ranking(ranking),
            left.valid_ranking(ranking),
            right.valid_ranking(ranking),
            self.root().can_split_index(pivot_idx),
            left.root() == self.root().split_index(pivot_idx).0,
            right.root() == self.root().split_index(pivot_idx).1,
            left.dv == right.dv,
            self.dv.agrees_with_disk(left.dv),
        ensures 
            self.reachable_buffer_addrs() == left.reachable_buffer_addrs() + right.reachable_buffer_addrs(),
    {
        let reachable_buffers = self.reachable_buffer_addrs();
        let split_reachable_buffers = left.reachable_buffer_addrs() + right.reachable_buffer_addrs();

        let min_ofs = self.root().flushed.min_ofs();
        let left_ofs = left.root().flushed.min_ofs();
        let right_ofs = right.root().flushed.min_ofs();

        self.root().flushed.min_ofs_ensures();
        let idx_ofs = self.root().flushed.offsets.index_of(min_ofs);

        assert forall |i| 0 <= i < pivot_idx ==> 
            left.root().flushed.offsets[i] == self.root().flushed.offsets[i] by {} // trigger
        assert forall |i| 0 <= i < right.root().flushed.offsets.len() ==> 
            right.root().flushed.offsets[i] == self.root().flushed.offsets[i + pivot_idx] by {} // trigger
    
        left.root().flushed.min_ofs_ensures();
        right.root().flushed.min_ofs_ensures();
        assert(min_ofs <= left_ofs);
        assert(min_ofs <= right_ofs);

        if idx_ofs < pivot_idx {       
            left.root().flushed.all_gte_is_min_ofs(min_ofs);
            assert(left_ofs == min_ofs);
        } else {
            assert(right.root().flushed.offsets[idx_ofs - pivot_idx] == min_ofs);
            right.root().flushed.all_gte_is_min_ofs(min_ofs);
            assert(right_ofs == min_ofs);
        }

        left.reachable_betree_addrs_using_ranking_closed(ranking);
        right.reachable_betree_addrs_using_ranking_closed(ranking);

        assert forall |addr| #[trigger] reachable_buffers.contains(addr)
        implies split_reachable_buffers.contains(addr)
        by {
            if self.root().active_buffers().contains(addr) {
                reveal(BetreeNode::active_buffers);
                if min_ofs == left_ofs {
                    assert(left.root().active_buffers().contains(addr));
                    assert(left.reachable_buffer(left.root.unwrap(), addr));
                } else {
                    assert(right.root().active_buffers().contains(addr));
                    assert(right.reachable_buffer(right.root.unwrap(), addr));
                }
            } else {
                let tree_addr = choose |tree_addr| self.reachable_buffer(tree_addr, addr);
                let i = self.non_root_buffers_belongs_to_child(tree_addr, addr);
                if i < pivot_idx {
                    self.same_child_same_reachable_buffers(left, i, i, ranking);
                } else {
                    self.same_child_same_reachable_buffers(right, i, (i-pivot_idx) as nat, ranking);
                }
            }
        }

        assert forall |addr| split_reachable_buffers.contains(addr)
        implies reachable_buffers.contains(addr)
        by {
            if left.root().active_buffers().contains(addr) 
                || right.root().active_buffers().contains(addr)
            {
                reveal(BetreeNode::active_buffers);
                assert(self.root().active_buffers().contains(addr));
                assert(self.reachable_buffer(self.root.unwrap(), addr));
            } else {
                if left.reachable_buffer_addrs().contains(addr) {
                    let tree_addr = choose |tree_addr| left.reachable_buffer(tree_addr, addr);
                    let i = left.non_root_buffers_belongs_to_child(tree_addr, addr);
                    self.same_child_same_reachable_buffers(left, i, i, ranking);
                } else {
                    let tree_addr = choose |tree_addr| right.reachable_buffer(tree_addr, addr);
                    let i = right.non_root_buffers_belongs_to_child(tree_addr, addr);
                    self.same_child_same_reachable_buffers(right, (i+pivot_idx) as nat, i, ranking);
                }
            }
        }
        assert(reachable_buffers =~= split_reachable_buffers);
    }

    proof fn split_parent_same_reachable_buffers(self, request: SplitRequest, new_addrs: SplitAddrs, ranking: Ranking) 
        requires 
            self.can_split_parent(request),
            self.valid_ranking(ranking),
            self.split_parent(request, new_addrs).valid_ranking(ranking),
            self.dv.is_fresh(new_addrs.repr()),
            new_addrs.no_duplicates(),
        ensures 
            self.reachable_buffer_addrs() =~= self.split_parent(request, new_addrs).reachable_buffer_addrs(),
    {
        let child_idx = request.xxxget_child_idx();
        let child = self.child_at_idx(child_idx as nat);

        let new_parent = self.split_parent(request, new_addrs);
        let left_child = new_parent.child_at_idx(child_idx);
        let right_child = new_parent.child_at_idx((child_idx+1) as nat);

        assert(new_parent.root().valid_child_index(child_idx));
        assert(new_parent.root().valid_child_index((child_idx+1) as nat));

        assert(left_child.valid_ranking(ranking));
        assert(right_child.valid_ranking(ranking));

        let child_buffers = child.reachable_buffer_addrs();
        let left_buffers = left_child.reachable_buffer_addrs();
        let right_buffers = right_child.reachable_buffer_addrs();

        self.child_at_idx_reachable_addrs_ensures(child_idx);
        new_parent.child_at_idx_reachable_addrs_ensures(child_idx);
        new_parent.child_at_idx_reachable_addrs_ensures((child_idx+1) as nat);

        if request is SplitLeaf {
            child.split_leaf_preserves_reachable_buffers(left_child, ranking);
            child.split_leaf_preserves_reachable_buffers(right_child, ranking);
        } else {
            child.split_index_preserves_reachable_buffers(
                left_child, right_child, request->child_pivot_idx, ranking);
        }
        assert(child_buffers == left_buffers + right_buffers);

        let min_ofs = self.root().flushed.min_ofs();
        assert(min_ofs == new_parent.root().flushed.min_ofs()) by {
            self.root().flushed.min_ofs_ensures();
            self.root().flushed.dup_ensures(child_idx as int);
            new_parent.root().flushed.all_gte_is_min_ofs(min_ofs);
        }

        assert forall |addr| self.reachable_buffer_addrs().contains(addr)
        implies new_parent.reachable_buffer_addrs().contains(addr)
        by {
            reveal(BetreeNode::active_buffers);
            if self.root().active_buffers().contains(addr) {
                assert(new_parent.root().active_buffers().contains(addr));
                new_parent.reachable_betree_addrs_using_ranking_closed(ranking);
                assert(new_parent.reachable_buffer(new_parent.root.unwrap(), addr));
            } else {
                let tree_addr = choose |tree_addr| self.reachable_buffer(tree_addr, addr);
                let i = self.non_root_buffers_belongs_to_child(tree_addr, addr);
                if i != child_idx {
                    let new_i = if i < child_idx { i } else { (i + 1) as nat };
                    self.same_child_same_reachable_buffers(new_parent, i, new_i, ranking);
                }
            }
        }

        assert forall |addr| new_parent.reachable_buffer_addrs().contains(addr) 
        implies self.reachable_buffer_addrs().contains(addr)
        by {
            reveal(BetreeNode::active_buffers);
            if new_parent.root().active_buffers().contains(addr) {
                assert(self.root().active_buffers().contains(addr));
                self.reachable_betree_addrs_using_ranking_closed(ranking);
                assert(self.reachable_buffer(self.root.unwrap(), addr));
            } else { 
                let tree_addr = choose |tree_addr| new_parent.reachable_buffer(tree_addr, addr);
                let new_i = new_parent.non_root_buffers_belongs_to_child(tree_addr, addr);
                if new_i != child_idx && new_i != child_idx + 1 {
                    let i = if new_i < child_idx { new_i } else { (new_i - 1) as nat};
                    self.same_child_same_reachable_buffers(new_parent, i, new_i, ranking);
                }
            }
        }
    }

    proof fn flush_new_ranking(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(), 
            self.has_root(),
            self.valid_ranking(ranking),
            self.can_flush(child_idx, buffer_gc),
            new_addrs.no_duplicates(),
            self.dv.is_fresh(new_addrs.repr()),
        ensures 
            self.valid_ranking(new_ranking),
            self.flush(child_idx, buffer_gc, new_addrs).valid_ranking(new_ranking),
            new_ranking.dom() == ranking.dom() + new_addrs.repr(),
            buffer_gc <= self.root().buffers.len()
    {
        let result = self.flush(child_idx, buffer_gc, new_addrs);
        let old_child_addr = self.child_at_idx(child_idx).root.unwrap();

        assert(result.dv.entries.contains_key(new_addrs.addr1));
        assert(result.dv.entries.contains_key(new_addrs.addr2));

        let old_child = self.dv.entries[old_child_addr];
        let new_parent = result.dv.entries[new_addrs.addr1];
        let new_child = result.dv.entries[new_addrs.addr2];

        let old_parent_rank = ranking[self.root.unwrap()];
        let old_child_rank = ranking[old_child_addr];
        let new_ranking = ranking.insert(new_addrs.addr1, old_parent_rank).insert(new_addrs.addr2, old_child_rank);

        assert(result.dv.valid_ranking(new_ranking)) by {
            assert forall |i| #[trigger] new_child.valid_child_index(i) ==> old_child.valid_child_index(i) by {} // trigger
            assert forall |i| #[trigger] new_parent.valid_child_index(i) ==> self.root().valid_child_index(i) by {} // trigger
        }

        assert(buffer_gc <= self.root().buffers.len()) by {
            let updated_ofs = self.root().flushed.update(child_idx as int, self.root().buffers.len());
            assert(updated_ofs.offsets[child_idx as int] >= buffer_gc);
        }

        assert(result.wf());
        assert(new_ranking.dom() =~= ranking.dom() + new_addrs.repr());

        new_ranking
    }

    proof fn flush_keeps_subset_reachable_buffers(self, child_idx: nat, buffer_gc: nat, new_addrs: TwoAddrs, ranking: Ranking)
        requires 
            self.wf(), 
            self.has_root(),
            self.valid_ranking(ranking),
            self.can_flush(child_idx, buffer_gc),
            self.flush(child_idx, buffer_gc, new_addrs).valid_ranking(ranking),
            new_addrs.no_duplicates(),
            self.dv.is_fresh(new_addrs.repr()),
        ensures 
            self.flush(child_idx, buffer_gc, new_addrs).reachable_buffer_addrs()
                <= self.reachable_buffer_addrs()
    {
        let result = self.flush(child_idx, buffer_gc, new_addrs);
        let min_ofs = self.root().flushed.min_ofs();
        let result_ofs = result.root().flushed.min_ofs();
        let flush_upto = self.root().buffers.len(); 

        self.root().flushed.min_ofs_ensures();
        result.root().flushed.min_ofs_ensures();
        assert(min_ofs <= result_ofs + buffer_gc <= flush_upto);

        let child = self.child_at_idx(child_idx);
        let result_child = result.child_at_idx(child_idx);

        assert(child.valid_ranking(ranking)) by {
            assert(self.root().valid_child_index(child_idx));
        }
        assert(result_child.valid_ranking(ranking)) by {
            assert(result.root().valid_child_index(child_idx));
        }

        assert forall |addr| result_child.reachable_buffer_addrs().contains(addr)
        implies self.reachable_buffer_addrs().contains(addr)
        by {
            self.child_at_idx_reachable_addrs_ensures(child_idx);
            if result_child.root().active_buffers().contains(addr) {
                reveal(BetreeNode::active_buffers);

                let child_ofs = result_child.root().flushed.min_ofs();
                let idx = choose |idx| child_ofs <= idx < result_child.root().buffers.len()
                        && result_child.root().buffers[idx] == addr;

                if idx < child.root().buffers.len() {
                    assert(child.root().active_buffers().contains(addr));
                    child.reachable_betree_addrs_using_ranking_closed(ranking);
                    assert(child.reachable_buffer(child.root.unwrap(), addr));
                } else {
                    let flushed_ofs = self.root().flushed.offsets[child_idx as int];
                    let root_idx = idx - child.root().buffers.len() + flushed_ofs;
                    assert(self.root().buffers[root_idx] == addr);
                    assert(root_idx >= min_ofs);
                    assert(self.root().active_buffers().contains(addr));
                    self.reachable_betree_addrs_using_ranking_closed(ranking);
                    assert(self.reachable_buffer(self.root.unwrap(), addr));
                }
            } else {
                let tree_addr = choose |tree_addr| result_child.reachable_buffer(tree_addr, addr);
                let i = result_child.non_root_buffers_belongs_to_child(tree_addr, addr);
                child.same_child_same_reachable_buffers(result_child, i, i, ranking);
            }
        }

        assert forall |addr| result.reachable_buffer_addrs().contains(addr)
        implies self.reachable_buffer_addrs().contains(addr)
        by {
            if result.root().active_buffers().contains(addr) {
                reveal(BetreeNode::active_buffers);
                self.reachable_betree_addrs_using_ranking_closed(ranking);
                assert(self.reachable_buffer(self.root.unwrap(), addr));
            } else {
                let tree_addr = choose |tree_addr| result.reachable_buffer(tree_addr, addr);
                let i = result.non_root_buffers_belongs_to_child(tree_addr, addr);
                if i != child_idx {
                    self.same_child_same_reachable_buffers(result, i, i, ranking);
                }
            }
        }
    }
}

impl <T: QueryableDisk> LinkedBetree<T>{
    proof fn subtree_same_tightness_preserves_acyclicity(self, other: Self)
        requires 
            self.acyclic(),
            self.subtree_same_tightness(other),
        ensures 
            other.acyclic(),
    {
        assert(other.dv.entries.dom() <= self.dv.entries.dom());
        assert(other.valid_ranking(self.the_ranking()));
    }

    proof fn subtree_same_tightness_preserves_valid_buffer_dv(self, other: Self)
        requires 
            self.acyclic(),
            self.valid_buffer_dv(),
            self.subtree_same_tightness(other),
            other.buffer_dv.wf(),
        ensures
            other.valid_buffer_dv(),
    {
        assert forall |addr| other.dv.entries.contains_key(addr)
            ==> self.dv.entries.contains_key(addr) by {}
        assert(other.valid_ranking(self.the_ranking()));

        other.agreeable_disks_same_reachable_betree_addrs(self, self.the_ranking());
        other.reachable_betree_addrs_ignore_ranking(self.the_ranking(), other.the_ranking());
        assert(other.reachable_betree_addrs() == self.reachable_betree_addrs());

        other.buffer_dv.sub_disk_implies_sub_repr(&self.buffer_dv);
        other.same_reachable_betree_addrs_implies_same_buffer_addrs(self);
    }
}

impl LinkedBetree<BufferDisk> {
    proof fn push_memtable_new_ranking(self, memtable: Memtable, new_addrs: TwoAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(), 
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
            self.valid_ranking(ranking),
        ensures
            self.valid_ranking(new_ranking),
            self.push_memtable(memtable, new_addrs).valid_ranking(new_ranking),
            new_ranking.dom() == ranking.dom().insert(new_addrs.addr1)
    {
        let result = self.push_memtable(memtable, new_addrs);
        let new_rank = if self.has_root() { ranking[self.root.unwrap()]+1 } else { 0 };
        let new_ranking = ranking.insert(new_addrs.addr1, new_rank);

        if self.has_root() {
            assert(forall |i| result.root().valid_child_index(i) ==> self.root().valid_child_index(i)); // trigger
            assert(result.dv.node_has_nondangling_child_ptrs(result.root()));
            assert(result.dv.node_has_linked_children(result.root()));
        }
        assert(result.wf());
        assert(result.dv.valid_ranking(new_ranking));
        new_ranking
    }

    // NOTE(JL): this is largely affected by spinoff prover
    // almost can't proof anything without it, opaque doesn't seem to matter???
    #[verifier::spinoff_prover]
    proof fn compact_new_ranking(self, start: nat, end: nat, compacted_buffer: Buffer, 
        new_addrs: TwoAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires 
            self.wf(), 
            self.has_root(),
            self.valid_ranking(ranking),
            self.can_compact(start, end, compacted_buffer),
            new_addrs.no_duplicates(),
            self.is_fresh(new_addrs.repr()),
        ensures 
            self.valid_ranking(new_ranking),
            self.compact(start, end, compacted_buffer, new_addrs).valid_ranking(new_ranking),
            new_ranking.dom() == ranking.dom().insert(new_addrs.addr1),
    {
        let result = self.compact(start, end, compacted_buffer, new_addrs);
        let new_ranking = ranking.insert(new_addrs.addr1, ranking[self.root.unwrap()]);

        assert(new_ranking.dom() =~= ranking.dom().insert(new_addrs.addr1));
        assert(self.valid_ranking(new_ranking));

        let new_root = result.dv.entries[new_addrs.addr1];
        assert forall |i| #[trigger] new_root.valid_child_index(i) 
            ==> self.root().valid_child_index(i) by {} // trigger
        assert(result.dv.valid_ranking(new_ranking));

        new_ranking
    }

    // #[verifier::spinoff_prover]
    proof fn compact_ensures(self, start: nat, end: nat, compacted_buffer: Buffer, new_addrs: TwoAddrs)
        requires 
            self.can_compact(start, end, compacted_buffer),
            self.is_fresh(new_addrs.repr()),
            new_addrs.no_duplicates(),
        ensures ({
            let result = self.compact(start, end, compacted_buffer, new_addrs);
            &&& result.root().my_domain() == self.root().my_domain()
            &&& self.dv.is_sub_disk(result.dv)
            &&& self.buffer_dv.is_sub_disk(result.buffer_dv)
            &&& result.dv.entries.dom() <= self.dv.entries.dom() + new_addrs.repr()
            &&& result.buffer_dv.repr() <= self.buffer_dv.repr() + new_addrs.repr()
        })
    {
    }
}

impl<T: QueryableDisk> Path<T>{
// proofs for LinkedBetreeVars invariant

    proof fn target_ensures(self)
        requires 
            self.valid(),
        ensures 
            self.target().dv == self.linked.dv,
            self.target().buffer_dv == self.linked.buffer_dv
        decreases 
            self.depth
    {
        if 0 < self.depth {
            self.subpath().target_ensures();
        }
    }

    proof fn valid_ranking_throughout(self, ranking: Ranking)
        requires 
            self.valid(), 
            self.linked.valid_ranking(ranking)
        ensures 
            0 < self.depth ==> self.subpath().linked.valid_ranking(ranking),
            self.target().valid_ranking(ranking),
        decreases self.depth
    {
        if 0 < self.depth {
            let root = self.linked.root();
            root.pivots.route_lemma(self.key);
            assert(root.valid_child_index(root.pivots.route(self.key) as nat)); // trigger
            self.subpath().valid_ranking_throughout(ranking);
        }
    }

    proof fn substitute_ensures(self, replacement: LinkedBetree<T>, path_addrs: PathAddrs)
        requires
            self.can_substitute(replacement, path_addrs),
            path_addrs.no_duplicates(),
            replacement.dv.is_fresh(path_addrs.to_set()),
        ensures ({
            let result = self.substitute(replacement, path_addrs);
            &&& result.wf()
            &&& result.has_root()
            &&& result.root().my_domain() == self.linked.root().my_domain()
            &&& self.depth > 0 ==> result.root().pivots == self.linked.root().pivots
            &&& result.dv.entries.dom() =~= replacement.dv.entries.dom() + path_addrs.to_set()
            &&& replacement.dv.is_sub_disk(result.dv)
        })
        decreases self.depth, 1nat
    {
        if 0 < self.depth {
            let result = self.substitute(replacement, path_addrs);
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);

            self.subpath().substitute_ensures(replacement, sub_path_addrs);
            path_addrs_to_set_additive(path_addrs);
            assert(result.dv.entries.dom() =~= replacement.dv.entries.dom() + path_addrs.to_set());

            let node = result.dv.entries[path_addrs[0]];
            let r = node.pivots.route(self.key);
            node.pivots.route_lemma(self.key);
            assert(self.linked.dv.entries.contains_key(self.linked.root.unwrap())); // trigger

            assert forall |i| #[trigger] node.valid_child_index(i)
            implies {
                &&& result.dv.is_nondangling_ptr(node.children[i as int])
                &&& result.dv.child_linked(node, i)
            } by {
                assert(self.linked.root().valid_child_index(i)); // trigger
                if i != r {
                    let child_ptr = node.children[i as int];
                    if child_ptr is Some {
                        assert(replacement.dv.entries.contains_key(child_ptr.unwrap())); // trigger
                        assert(result.dv.entries.contains_key(child_ptr.unwrap())); // trigger
                    }
                }
            }
            assert(result.dv.node_has_nondangling_child_ptrs(node));
            assert(result.dv.node_has_linked_children(node));
            assert(result.wf());
        }
    }

    closed spec(checked) fn ranking_for_substitution(self, replacement: LinkedBetree<T>, path_addrs: PathAddrs, ranking: Ranking) -> bool
        recommends self.can_substitute(replacement, path_addrs)
    {
        &&& replacement.valid_ranking(ranking)
        &&& path_addrs.to_set().disjoint(ranking.dom())
        &&& self.linked.has_root() ==> ranking.contains_key(self.linked.root.unwrap())
    }

    proof fn ranking_after_substitution(self, replacement: LinkedBetree<T>, path_addrs: PathAddrs, ranking: Ranking) -> (new_ranking: Ranking)
        requires
            self.can_substitute(replacement, path_addrs),
            self.ranking_for_substitution(replacement, path_addrs, ranking),
            path_addrs.no_duplicates(),
            replacement.dv.is_fresh(path_addrs.to_set()),
        ensures 
            ranking <= new_ranking,
            new_ranking.dom() =~= ranking.dom() + path_addrs.to_set(),
            self.substitute(replacement, path_addrs).valid_ranking(new_ranking),
        decreases self.depth
    {
        self.substitute_ensures(replacement, path_addrs);
        PivotTable::route_lemma_auto();

        if self.depth == 0 {
            ranking
        } else {
            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let subtree = self.subpath().substitute(replacement, sub_path_addrs);
            self.subpath().substitute_ensures(replacement, sub_path_addrs);

            self.linked.dv.subdisk_implies_ranking_validity(replacement.dv, ranking);
            self.valid_ranking_throughout(ranking);

            let r = self.linked.root().pivots.route(self.key);
            assert(self.linked.root().valid_child_index(r as nat)); // trigger
            assert(self.subpath().linked.has_root());

            let intermediate_ranking = self.subpath().ranking_after_substitution(replacement, sub_path_addrs, ranking);
            let new_root_addr = path_addrs[0];
            let old_root_rank = intermediate_ranking[self.linked.root.unwrap()];
            let subtree_root_rank = intermediate_ranking[subtree.root.unwrap()];
            let new_root_rank = old_root_rank + subtree_root_rank + 1;
          
            let new_ranking = intermediate_ranking.insert(new_root_addr, new_root_rank);
            let result = self.substitute(replacement, path_addrs);
            let new_root = result.root();

            assert forall |i| #[trigger] new_root.valid_child_index(i) && new_root.children[i as int] is Some
            implies {
                &&& new_ranking.contains_key(new_root.children[i as int].unwrap())
                &&& new_ranking[new_root.children[i as int].unwrap()] < new_ranking[new_root_addr]
            } by {
                assert(self.linked.root().valid_child_index(i)); // trigger
                if i != r {
                    assert(intermediate_ranking.contains_key(new_root.children[i as int].unwrap()));
                    assert(intermediate_ranking.contains_key(self.linked.root.unwrap()));

                    assert(new_ranking.contains_key(new_root.children[i as int].unwrap()));
                    assert(new_ranking[new_root.children[i as int].unwrap()] < new_ranking[new_root_addr]);
                }
            }
            path_addrs_to_set_additive(path_addrs);
            new_ranking
        }
    }

    // any newly added buffer address must not be present in the old reachable buffer set
    closed spec(checked) fn new_reachable_buffers_are_fresh(self, replacement: LinkedBetree<T>) -> bool
        recommends
            self.valid(),
            replacement.acyclic(),
    {
        let reachable_buffers = self.linked.reachable_buffer_addrs();
        let replacement_buffers = replacement.reachable_buffer_addrs();

        &&& self.target().acyclic()
        &&& reachable_buffers.disjoint(replacement_buffers.difference(self.target().reachable_buffer_addrs()))
    }

    proof fn substitute_reachable_buffers_ensures(self, replacement: LinkedBetree<T>, path_addrs: PathAddrs, ranking: Ranking)
        requires
            self.linked.valid_ranking(ranking),
            self.can_substitute(replacement, path_addrs), 
            self.ranking_for_substitution(replacement, path_addrs, ranking),
            self.new_reachable_buffers_are_fresh(replacement),
            path_addrs.no_duplicates(),
            replacement.is_fresh(path_addrs.to_set()),
        ensures ({
            let result = self.substitute(replacement, path_addrs);
            let replacement_buffers = replacement.reachable_buffer_addrs();
            let new_buffers = replacement_buffers.difference(self.target().reachable_buffer_addrs());

            &&& result.acyclic()
            &&& replacement.reachable_buffer_addrs() <= result.reachable_buffer_addrs()
            &&& result.reachable_buffer_addrs().difference(new_buffers) <= self.linked.reachable_buffer_addrs()
        })
        decreases self.depth
    {
        let result = self.substitute(replacement, path_addrs);
        let replacement_buffers = replacement.reachable_buffer_addrs();
        let new_buffers = replacement_buffers.difference(self.target().reachable_buffer_addrs());

        if 0 < self.depth {
            self.substitute_ensures(replacement, path_addrs);
            let result_ranking = self.ranking_after_substitution(replacement, path_addrs, ranking);
        
            let r = self.linked.root().pivots.route(self.key) as nat;
            PivotTable::route_lemma(self.linked.root().pivots, self.key);

            self.linked.dv.subdisk_implies_ranking_validity(replacement.dv, ranking);
            self.valid_ranking_throughout(ranking);

            let sub_path_addrs = path_addrs.subrange(1, path_addrs.len() as int);
            let result_subtree = self.subpath().substitute(replacement, sub_path_addrs);

            self.subpath().substitute_ensures(replacement, sub_path_addrs);
            result_subtree.dv.subdisk_implies_ranking_validity(result.dv, result_ranking);
            assert(result_subtree.valid_ranking(result_ranking));

            self.linked.child_at_idx_reachable_addrs_ensures(r);
            result.child_at_idx_reachable_addrs_ensures(r);

            self.subpath().substitute_reachable_buffers_ensures(replacement, sub_path_addrs, ranking);
            assert(self.subpath().linked.reachable_buffer_addrs() == self.linked.child_at_idx(r).reachable_buffer_addrs());    
            assert(result_subtree.reachable_buffer_addrs() == result.child_at_idx(r).reachable_buffer_addrs()) 
            by {
                let result_child = result.child_at_idx(r);
                result.child_at_idx_acyclic(r);
                result_subtree.agreeable_disks_same_reachable_betree_addrs(result_child, result_ranking);
                result_subtree.reachable_betree_addrs_ignore_ranking(result_subtree.the_ranking(), result_ranking);
                result_child.reachable_betree_addrs_ignore_ranking(result_child.the_ranking(), result_ranking);
                result_subtree.same_reachable_betree_addrs_implies_same_buffer_addrs(result.child_at_idx(r));
            }
            assert(replacement.reachable_buffer_addrs() <= result.reachable_buffer_addrs());

            let reachable_buffers = self.linked.reachable_buffer_addrs();
            let result_old_buffers = result.reachable_buffer_addrs().difference(new_buffers);

            assert forall |addr| #[trigger] result_old_buffers.contains(addr)
            implies reachable_buffers.contains(addr)
            by {
                if result.root().active_buffers().contains(addr) {
                    assert(self.linked.root().active_buffers().contains(addr)) by {     
                        reveal(BetreeNode::active_buffers);
                    }
                    assert(self.linked.reachable_buffer(self.linked.root.unwrap(), addr)); // witness
                    assert(reachable_buffers.contains(addr));
                } else {
                    let tree_addr = choose |tree_addr| result.reachable_buffer(tree_addr, addr);
                    assert(result.reachable_betree_addrs().contains(tree_addr));
                    let i = result.non_root_buffers_belongs_to_child(tree_addr, addr);
                    assert(result.child_at_idx(i).reachable_buffer_addrs().contains(addr));
                    if i == r {
                        self.linked.child_at_idx_reachable_addrs_ensures(i);
                    } else {
                        result.same_child_same_reachable_buffers(self.linked, i, i, result_ranking);
                    }
                }
            }
        }
    }
}
} // end verus!
