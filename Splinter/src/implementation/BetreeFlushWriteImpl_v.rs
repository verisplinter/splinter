// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_multisets_equal;
use vstd::assert_seqs_equal;
use vstd::multiset::Multiset;
use vstd::seq_lib::{lemma_multiset_commutative, to_multiset_build};

use crate::allocation_layer::Likes_v::{
    to_au_likes, to_au_likes_commutative_over_add,
};
use crate::allocation_layer::LikesBetree_v::Likeable;
use crate::betree::LinkedBetree_v::{Addrs, TwoAddrs};
use crate::implementation::AuLikesImpl_v::seq_to_au_likes;
use crate::implementation::BetreePageImpl_v::marshall_betree_node_page;
use crate::implementation::BetreePathImpl_v::BetreePathWorkspace;
use crate::implementation::BetreePageImpl_v::betree_node_addr;
use crate::implementation::BetreeSplitWriteImpl_v::{
    AncestorWriteBuild, complete_ancestor_write_batch, iaddr_views,
    iaddr_views_unique, iaddress_aus_likes,
};
use crate::implementation::BetreeStructuralPageImpl_v::{
    build_compact_node_page, build_flush_node_pages, compact_node_view,
    flush_child_view, flush_parent_view,
};
use crate::implementation::BetreeWriteBatchImpl_v::{
    BetreeWriteEntry, betree_node_writes, betree_raw_writes,
    betree_raw_writes_dom, betree_raw_writes_to_nodes,
    betree_write_entries_push, betree_write_entries_wf,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranchBetree_v::{
    LoadedBetree, LoadedBetreePath, added_path_likes,
    compact_replacement, direct_buffer_likes, flush_replacement,
    path_discard_likes,
    replacement_root, substitute_writes,
};
use crate::implementation::CachingDiskBranchBetree_v::to_betree_nodes;
use crate::implementation::IBetreeNode_v::IBetreeNode;
use crate::marshalling::IBetreeNodeFormat_v::raw_page_to_betree_node;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::WF_v::WF;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::ImplDisk_t::{IAddress, IAU};
use crate::spec::KeyType_t::Key;
use crate::disk::GenericDisk_v::{Address, AU};

verus! {

pub open spec fn cached_flush_parent_wf(
    cache: Cache::State,
    root: Address,
    key: Key,
    depth: nat,
    child_idx: nat,
    buffer_gc: nat,
    new_child_addr: Address,
) -> bool {
    forall |
        path: LoadedBetreePath,
        path_reads: Map<Address, RawPage>,
        child_addr: Address,
        child_raw: RawPage,
    | {
        &&& path.root == root
        &&& path.key == key
        &&& path.depth() == depth
        &&& path.valid_for(Some(root), to_betree_nodes(path_reads))
        &&& forall |addr: Address| #[trigger] path_reads.contains_key(addr)
            ==> cache.valid_read(addr, path_reads[addr])
        &&& path.target().node.valid_child_index(child_idx)
        &&& path.target().node.children[child_idx as int]
            == Some(child_addr)
        &&& cache.valid_read(child_addr, child_raw)
        &&& buffer_gc <= path.target().node.buffers.len()
        &&& path.target().node.flushed.update(
            child_idx as int,
            path.target().node.buffers.len(),
        ).all_gte(buffer_gc)
    } ==> {
        let child = raw_page_to_betree_node(child_raw);
        &&& child.wf()
        &&& flush_parent_view(
            path.target().node,
            child_idx,
            buffer_gc,
            new_child_addr,
        ).wf()
        &&& flush_child_view(
            path.target().node,
            child,
            child_idx,
        ).wf()
    }
}

proof fn two_write_entries(left: BetreeWriteEntry, right: BetreeWriteEntry)
    requires
        left.wf(),
        right.wf(),
        left.addr@ != right.addr@,
    ensures
        betree_write_entries_wf(seq![left, right]),
        betree_node_writes(seq![left, right]) == map![
            left.addr@ => raw_page_to_betree_node(left.page@),
            right.addr@ => raw_page_to_betree_node(right.page@),
        ],
{
    reveal_with_fuel(betree_node_writes, 3);

    let empty = Seq::<BetreeWriteEntry>::empty();
    assert(betree_write_entries_wf(empty));
    assert(!betree_raw_writes(empty).dom().contains(left.addr@));
    betree_write_entries_push(empty, left);
    let one = empty.push(left);
    betree_raw_writes_dom(one);
    assert(!betree_raw_writes(one).dom().contains(right.addr@));
    betree_write_entries_push(one, right);
    assert(seq![left, right] == one.push(right));
    assert(betree_node_writes(seq![left, right])
        == betree_node_writes(seq![left]).insert(
            right.addr@,
            raw_page_to_betree_node(right.page@),
        ));
    assert(betree_node_writes(seq![left])
        == Map::empty().insert(
            left.addr@,
            raw_page_to_betree_node(left.page@),
        ));
    assert_maps_equal!(
        betree_node_writes(seq![left, right]),
        map![
            left.addr@ => raw_page_to_betree_node(left.page@),
            right.addr@ => raw_page_to_betree_node(right.page@),
        ],
        addr => {}
    );
}

pub struct FlushWriteBuild {
    pub entries: Vec<BetreeWriteEntry>,
    pub new_root: IAddress,
}

pub fn build_compact_write_batch(
    path: &BetreePathWorkspace,
    start: usize,
    end: usize,
    sealed_root: IAddress,
    new_node_addr: IAddress,
    path_addrs: &Vec<IAddress>,
) -> (out: Option<FlushWriteBuild>)
    requires
        path.wf(),
        path_addrs@.len() == path.receipt@.depth(),
        (start as nat) < (end as nat),
        end as nat <= path.receipt@.target().node.buffers.len(),
        compact_node_view(
            path.receipt@.target().node,
            start as nat,
            end as nat,
            sealed_root@,
        ).wf(),
        sealed_root@.wf(),
        new_node_addr@.wf(),
        betree_node_addr(new_node_addr@),
        forall |i: int| 0 <= i < path_addrs@.len()
            ==> (#[trigger] path_addrs@[i])@.wf(),
        forall |i: int| 0 <= i < path_addrs@.len()
            ==> betree_node_addr((#[trigger] path_addrs@[i])@),
        iaddr_views_unique(path_addrs@),
        !iaddr_views(path_addrs@).to_set().contains(new_node_addr@),
    ensures
        out is Some ==> {
            let built = out.unwrap();
            let replacement = compact_replacement(
                path.receipt@,
                start as nat,
                end as nat,
                sealed_root@,
                TwoAddrs {
                    addr1: new_node_addr@,
                    addr2: sealed_root@,
                },
            );
            &&& betree_write_entries_wf(built.entries@)
            &&& to_betree_nodes(betree_raw_writes(built.entries@))
                == substitute_writes(
                    path.receipt@,
                    new_node_addr@,
                    replacement,
                    iaddr_views(path_addrs@),
                )
            &&& betree_raw_writes(built.entries@).dom()
                <= set![new_node_addr@]
                    + iaddr_views(path_addrs@).to_set()
            &&& built.new_root@ == replacement_root(
                path.receipt@,
                new_node_addr@,
                iaddr_views(path_addrs@),
            )
        },
{
    let target_idx = path.nodes.len() - 1;
    let target = &path.nodes[target_idx];
    let compact = match build_compact_node_page(
        target,
        start,
        end,
        sealed_root,
    ) {
        Some(compact) => compact,
        None => return None,
    };
    let page = marshall_betree_node_page(&compact.node);
    let entry = BetreeWriteEntry { addr: new_node_addr, page };
    let entries = vec![entry];
    let ghost replacement = compact_replacement(
        path.receipt@,
        start as nat,
        end as nat,
        sealed_root@,
        TwoAddrs {
            addr1: new_node_addr@,
            addr2: sealed_root@,
        },
    );
    proof {
        reveal_with_fuel(betree_node_writes, 2);
        assert(path.nodes@[target_idx as int]@ == path.receipt@.target().node);
        assert(entry.wf());

        assert(betree_write_entries_wf(entries@));
        assert(raw_page_to_betree_node(entry.page@) == compact.node@);
        assert(compact.node@ == compact_node_view(
            path.receipt@.target().node,
            start as nat,
            end as nat,
            sealed_root@,
        ));
        assert(replacement == map![new_node_addr@ => compact.node@]);
        assert(betree_node_writes(entries@) == replacement);
        betree_raw_writes_to_nodes(entries@);
        assert(replacement.dom() == set![new_node_addr@]);
    }
    let completed = match complete_ancestor_write_batch(
        path,
        entries,
        new_node_addr,
        Ghost(replacement),
        path_addrs,
    ) {
        Some(completed) => completed,
        None => return None,
    };
    Some(FlushWriteBuild {
        entries: completed.entries,
        new_root: completed.new_root,
    })
}

pub fn build_flush_write_batch(
    path: &BetreePathWorkspace,
    child_addr: IAddress,
    child: &IBetreeNode,
    child_idx: usize,
    buffer_gc: usize,
    parent_addr: IAddress,
    new_child_addr: IAddress,
    path_addrs: &Vec<IAddress>,
) -> (out: Option<FlushWriteBuild>)
    requires
        path.wf(),
        path_addrs@.len() == path.receipt@.depth(),
        path.receipt@.target().node.valid_child_index(child_idx as nat),
        path.receipt@.target().node.children[child_idx as int] == Some(child_addr@),
        child.wf(),
        child@.wf(),
        buffer_gc as nat <= path.receipt@.target().node.buffers.len(),
        path.receipt@.target().node.flushed.update(
            child_idx as int,
            path.receipt@.target().node.buffers.len(),
        ).all_gte(buffer_gc as nat),
        flush_parent_view(
            path.receipt@.target().node,
            child_idx as nat,
            buffer_gc as nat,
            new_child_addr@,
        ).wf(),
        flush_child_view(
            path.receipt@.target().node,
            child@,
            child_idx as nat,
        ).wf(),
        parent_addr@.wf(),
        new_child_addr@.wf(),
        betree_node_addr(parent_addr@),
        betree_node_addr(new_child_addr@),
        forall |i: int| 0 <= i < path_addrs@.len()
            ==> (#[trigger] path_addrs@[i])@.wf(),
        forall |i: int| 0 <= i < path_addrs@.len()
            ==> betree_node_addr((#[trigger] path_addrs@[i])@),
        parent_addr != new_child_addr,
        iaddr_views_unique(path_addrs@),
        iaddr_views(path_addrs@).to_set().disjoint(
            set![parent_addr@, new_child_addr@],
        ),
    ensures
        out is Some ==> {
            let built = out.unwrap();
            let reads = map![child_addr@ => child@];
            let new_addrs = TwoAddrs {
                addr1: parent_addr@,
                addr2: new_child_addr@,
            };
            let model_writes = substitute_writes(
                path.receipt@,
                parent_addr@,
                flush_replacement(
                    path.receipt@,
                    reads,
                    child_idx as nat,
                    buffer_gc as nat,
                    new_addrs,
                ),
                iaddr_views(path_addrs@),
            );
            &&& betree_write_entries_wf(built.entries@)
            &&& to_betree_nodes(betree_raw_writes(built.entries@))
                == model_writes
            &&& betree_raw_writes(built.entries@).dom()
                <= set![parent_addr@, new_child_addr@]
                    + iaddr_views(path_addrs@).to_set()
            &&& built.new_root@ == replacement_root(
                path.receipt@,
                parent_addr@,
                iaddr_views(path_addrs@),
            )
        },
{
    let target_idx = path.nodes.len() - 1;
    let parent = &path.nodes[target_idx];
    let pages = match build_flush_node_pages(
        parent,
        child,
        child_idx,
        buffer_gc,
        new_child_addr,
    ) {
        Some(pages) => pages,
        None => return None,
    };
    let parent_page = marshall_betree_node_page(&pages.parent);
    let child_page = marshall_betree_node_page(&pages.child);
    let mut entries = Vec::<BetreeWriteEntry>::new();
    entries.push(BetreeWriteEntry { addr: parent_addr, page: parent_page });
    entries.push(BetreeWriteEntry { addr: new_child_addr, page: child_page });
    let ghost reads = map![child_addr@ => child@];
    let ghost new_addrs = TwoAddrs {
        addr1: parent_addr@,
        addr2: new_child_addr@,
    };
    let ghost base = flush_replacement(
        path.receipt@,
        reads,
        child_idx as nat,
        buffer_gc as nat,
        new_addrs,
    );
    proof {
        assert(path.nodes@[target_idx as int]@ == path.receipt@.target().node);
        assert(entries@ == seq![entries@[0], entries@[1]]);
        assert(entries@[0].wf());
        assert(entries@[1].wf());
        two_write_entries(entries@[0], entries@[1]);
        assert(raw_page_to_betree_node(entries@[0].page@)
            == pages.parent@);
        assert(raw_page_to_betree_node(entries@[1].page@)
            == pages.child@);
        assert(base == map![
            parent_addr@ => pages.parent@,
            new_child_addr@ => pages.child@,
        ]);
        assert(betree_node_writes(entries@) == base);
        betree_raw_writes_to_nodes(entries@);
        assert(base.dom() == set![parent_addr@, new_child_addr@]);
    }
    let completed = match complete_ancestor_write_batch(
        path,
        entries,
        parent_addr,
        Ghost(base),
        path_addrs,
    ) {
        Some(completed) => completed,
        None => return None,
    };
    Some(FlushWriteBuild {
        entries: completed.entries,
        new_root: completed.new_root,
    })
}

pub proof fn two_added_au_likes(
    parent: IAddress,
    child: IAddress,
    path_addrs: Seq<IAddress>,
    destinations: Seq<IAddress>,
    new_aus: Seq<IAU>,
)
    requires
        destinations == seq![parent, child] + path_addrs,
        new_aus.len() == destinations.len(),
        forall |i: int| 0 <= i < new_aus.len()
            ==> (#[trigger] new_aus[i]) as nat == destinations[i]@.au,
        parent@ != child@,
    ensures
        seq_to_au_likes(new_aus) =~= to_au_likes(added_path_likes(
            TwoAddrs { addr1: parent@, addr2: child@ },
            iaddr_views(path_addrs),
        )),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    iaddress_aus_likes(destinations, new_aus);
    let addrs = TwoAddrs { addr1: parent@, addr2: child@ };
    let prefix = seq![parent@, child@];
    assert(iaddr_views(destinations)
        == prefix + iaddr_views(path_addrs)) by {
        assert_seqs_equal!(
            iaddr_views(destinations),
            prefix + iaddr_views(path_addrs),
            i => {}
        );
    }
    let empty = Seq::<Address>::empty();
    empty.to_multiset_ensures();
    assert(empty.to_multiset() =~= Multiset::<Address>::empty());
    to_multiset_build(empty, parent@);
    let one = seq![parent@];
    assert(one == empty.push(parent@));
    assert(one.to_multiset()
        =~= Multiset::singleton(parent@));
    to_multiset_build(one, child@);
    assert(prefix == one.push(child@));
    assert(prefix.to_multiset()
        =~= Multiset::singleton(parent@).insert(child@));
    assert(addrs.likes()
        == Multiset::singleton(parent@).add(
            Multiset::singleton(child@),
        ));
    assert(prefix.to_multiset() =~= addrs.likes());
    assert(addrs.repr().finite());
    assert(addrs.repr().to_multiset() == addrs.likes()) by {
        assert forall |addr: Address|
            addrs.repr().to_multiset().count(addr)
                == addrs.likes().count(addr) by {
            finite_set_to_multiset_count(addrs.repr(), addr);
            if addr == parent@ {
            } else if addr == child@ {
            } else {
                assert(!addrs.repr().contains(addr));
            }
        }
    }
    lemma_multiset_commutative(
        prefix,
        iaddr_views(path_addrs),
    );
    assert_multisets_equal!(
        iaddr_views(destinations).to_multiset(),
        added_path_likes(addrs, iaddr_views(path_addrs)),
        addr => {}
    );
}

proof fn finite_set_to_multiset_count<A>(set: Set<A>, value: A)
    requires set.finite(),
    ensures
        set.to_multiset().count(value)
            == if set.contains(value) { 1nat } else { 0nat },
    decreases set.len(),
{
    broadcast use vstd::set_lib::group_set_properties;
    if set.len() == 0 {
        set.lemma_len0_is_empty();
    } else {
        let chosen = set.choose();
        finite_set_to_multiset_count(set.remove(chosen), value);
        if value == chosen {
            assert(!set.remove(chosen).contains(value));
        } else {
            assert(set.remove(chosen).contains(value) == set.contains(value));
        }
    }
}

} // verus!
