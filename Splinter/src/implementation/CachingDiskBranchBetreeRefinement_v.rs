// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Refinement from CachingDiskBranchBetree to AllocationBranchBetree.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::map_lib::*;
use vstd::multiset::Multiset;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;

use crate::abstract_system::StampedMap_v::Stamped;
use crate::allocation_layer::BranchTypes_v::{BranchNode, Summary};
use crate::allocation_layer::AllocationBulkBranch_v::{
    AllocationBulkBranch, BulkBranchEvent, BulkBranchPhase,
};
use crate::allocation_layer::AllocationBranchBetree_v::{
    AllocationBranchBetree, CompactorInput, read_ref_aus, seq_addrs_to_aus,
    summary_aus,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Buffer_v::Buffer;
use crate::betree::LinkedBetree_v::{
    Addrs, DiskView as BetreeDiskView, LinkedBetree, LinkedBetreeVars, Path,
    PathAddrs, QueryReceipt, QueryReceiptLine, SplitAddrs, TwoAddrs,
};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::betree::LinkedSeq_v::LinkedSeq;
use crate::allocation_layer::LikesBetree_v::Likeable;
use crate::allocation_layer::Likes_v::to_au_likes;
use crate::betree::LinkedBranch_v::{
    DiskView as BranchDiskView, LinkedBranch, Path as BranchPath,
    Refinement_v as LinkedBranchRefinement,
};
use crate::implementation::CachedBranchBetree_v::{
    CachedBranchBetree, LoadedBetreePath,
    LoadedBetreeQueryReceipt, branch_receipts_result, branch_receipts_valid,
    grow_writes, loaded_branch_reads_for_roots,
    loaded_sealed_branch,
};
use crate::implementation::CachedBulkBranch_v::{
    CachedBulkBranch, CachedBulkBranchEvent,
    cached_bulk_branch_alloc_aus,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    BranchBuildEvent, CachingDiskBranchBetree, PageAccess,
    disk_access_empty_alloc_access_is_forget,
    disk_access_empty_alloc_visible_stable, disk_access_for_alloc,
    disk_access_empty_effect_is_extension,
    disk_access_for_alloc_visible_on_stable,
    disk_access_for_alloc_witness,
    disk_extend_empty_is_identity,
    disk_access_for_alloc_visible_outside_alloc_dealloc,
    disk_extend_for_alloc,
    disk_extend_visible_outside_allocs, disk_forget_visible_outside_aus,
    loose_disk_for_summary, tight_branch_addrs, tight_branch_exists,
    reclaim_guarded_aus, reclaim_guarded_aus_preserves_inv,
    tight_branch_of, tight_sealed_branch_disk, to_betree_nodes,
    to_branch_nodes, visible_branch_disk,
};
use crate::implementation::BulkBranchProofUtils_v::{
    active_loaded_nodes_follow_readable_writes, active_loaded_nodes_of,
    child_branch_inv_internal_from_parent,
    mini_allocator_add_aus_preserves_allocated_addrs,
    mini_allocator_allocated_addrs,
    mini_allocator_allocated_addrs_subset_all_aus,
    query_read_node_matches_visible,
    receipt_query_matches_branch_query,
};
use crate::implementation::BranchProofUtils_v::{
    mini_allocator_allocate_preserves_all_aus, tight_branch_in_loose_disk,
};
use crate::implementation::CachedBranch_v::{
    CachedBranch, loaded_append_write_nodes, loaded_grow_write_nodes,
    loaded_initialize_write_nodes, loaded_seal_write_nodes,
    loaded_split_write_nodes,
};
use crate::implementation::CachingDisk_v::{
    CachingDisk, PageStatus, addresses_in_aus,
};
use crate::spec::AsyncDisk_t::{AU, Address, RawPage};
use crate::spec::Messages_t::{Message, default_value};
use crate::disk::GenericDisk_v::{
    Pointer, addrs_with_different_au, seq_addrs_disjoint_aus,
    set_addrs_disjoint_aus, to_aus,
};

verus! {

proof fn addresses_in_aus_preserves_disjointness(left: Set<AU>, right: Set<AU>)
    requires left.disjoint(right)
    ensures addresses_in_aus(left).disjoint(addresses_in_aus(right))
{
}

proof fn finite_set_to_multiset_count<A>(set: Set<A>, value: A)
    requires set.finite()
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
        assert(set.contains(chosen));
        finite_set_to_multiset_count(set.remove(chosen), value);
        if value == chosen {
            assert(!set.remove(chosen).contains(value));
        } else {
            assert(set.remove(chosen).contains(value) == set.contains(value));
        }
    }
}

proof fn split_addrs_repr_likes(addrs: SplitAddrs)
    requires addrs.no_duplicates()
    ensures addrs.repr().to_multiset() == addrs.likes()
{
    assert forall |addr: Address|
        addrs.repr().to_multiset().count(addr) == addrs.likes().count(addr)
    by {
        finite_set_to_multiset_count(addrs.repr(), addr);
        if addr == addrs.left {
        } else if addr == addrs.right {
        } else if addr == addrs.parent {
        } else {
            assert(!addrs.repr().contains(addr));
        }
    };
}

proof fn two_addrs_repr_likes(addrs: TwoAddrs)
    requires addrs.no_duplicates()
    ensures addrs.repr().to_multiset() == addrs.likes()
{
    assert forall |addr: Address|
        addrs.repr().to_multiset().count(addr) == addrs.likes().count(addr)
    by {
        finite_set_to_multiset_count(addrs.repr(), addr);
        if addr == addrs.addr1 {
        } else if addr == addrs.addr2 {
        } else {
            assert(!addrs.repr().contains(addr));
        }
    };
}

proof fn summary_aus_restrict_subset(
    summaries: Map<AU, Summary>,
    keys: Set<AU>,
)
    requires summaries.dom().finite()
    ensures
        summary_aus(summaries.restrict(keys))
            <= summary_aus(summaries),
{
    lemma_values_finite(summaries);
    crate::betree::Utils_v::lemma_subset_finite(
        summaries.dom(),
        summaries.restrict(keys).dom(),
    );
    lemma_values_finite(summaries.restrict(keys));
    assert forall |au: AU|
        #[trigger] summary_aus(summaries.restrict(keys)).contains(au)
        implies summary_aus(summaries).contains(au)
    by {
        let summary =
            crate::betree::Utils_v::lemma_union_set_of_sets_contains(
                summaries.restrict(keys).values(),
                au,
            );
        assert(summaries.values().contains(summary));
        crate::betree::Utils_v::lemma_union_set_of_sets_subset(
            summaries.values(),
            summary,
        );
    }
}

proof fn map_restrict_equal_on_subset<K, V>(
    left: Map<K, V>,
    right: Map<K, V>,
    big: Set<K>,
    small: Set<K>,
)
    requires
        small <= big,
        left.restrict(big) == right.restrict(big),
    ensures left.restrict(small) == right.restrict(small),
{
    assert_maps_equal!(
        left.restrict(small),
        right.restrict(small),
        key => {
            if left.restrict(small).contains_key(key) {
                assert(left.contains_key(key));
                assert(small.contains(key));
                assert(big.contains(key));
                assert(left.restrict(big).contains_key(key));
                assert(right.restrict(big).contains_key(key));
                assert(right.contains_key(key));
                assert(left.restrict(big)[key] == left[key]);
                assert(right.restrict(big)[key] == right[key]);
            }
            if right.restrict(small).contains_key(key) {
                assert(right.contains_key(key));
                assert(small.contains(key));
                assert(big.contains(key));
                assert(right.restrict(big).contains_key(key));
                assert(left.restrict(big).contains_key(key));
                assert(left.contains_key(key));
                assert(left.restrict(big)[key] == left[key]);
                assert(right.restrict(big)[key] == right[key]);
            }
        }
    );
}

pub proof fn summary_partition_disjoint(
    summary: Map<AU, Summary>,
    removed: Set<AU>,
)
    requires
        summary.dom().finite(),
        summary.values().finite(),
        crate::allocation_layer::AllocationBranchBetree_v::map_with_disjoint_values(
            summary,
        ),
    ensures
        summary_aus(summary.remove_keys(removed)).disjoint(
            summary_aus(summary.restrict(removed)),
        ),
        summary_aus(summary)
            == summary_aus(summary.remove_keys(removed))
                + summary_aus(summary.restrict(removed)),
{
    let kept = summary.remove_keys(removed);
    let dropped = summary.restrict(removed);
    crate::betree::Utils_v::lemma_subset_finite(
        summary.dom(),
        kept.dom(),
    );
    crate::betree::Utils_v::lemma_subset_finite(
        summary.dom(),
        dropped.dom(),
    );
    lemma_values_finite(kept);
    lemma_values_finite(dropped);
    assert forall |au: AU|
        #[trigger] summary_aus(kept).contains(au)
            && #[trigger] summary_aus(dropped).contains(au)
        implies false
    by {
        let kept_set = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
            kept.values(),
            au,
        );
        let dropped_set = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
            dropped.values(),
            au,
        );
        let kept_key = choose |key: AU|
            kept.contains_key(key) && kept[key] == kept_set;
        let dropped_key = choose |key: AU|
            dropped.contains_key(key) && dropped[key] == dropped_set;
        assert(summary.contains_key(kept_key));
        assert(summary.contains_key(dropped_key));
        assert(!removed.contains(kept_key));
        assert(removed.contains(dropped_key));
        assert(kept_key != dropped_key);
        assert(summary[kept_key].disjoint(summary[dropped_key]));
    };
    assert(summary_aus(summary)
        == summary_aus(kept) + summary_aus(dropped)) by {
        assert forall |au: AU|
            #[trigger] summary_aus(summary).contains(au)
            <==> (summary_aus(kept)
                + summary_aus(dropped)).contains(au)
        by {
            if summary_aus(summary).contains(au) {
                let member =
                    crate::betree::Utils_v::
                        lemma_union_set_of_sets_contains(
                            summary.values(),
                            au,
                        );
                let key = choose |key: AU|
                    summary.contains_key(key)
                        && summary[key] == member;
                if removed.contains(key) {
                    assert(dropped.contains_key(key));
                    assert(dropped.values().contains(member));
                    crate::betree::Utils_v::
                        lemma_union_set_of_sets_subset(
                            dropped.values(),
                            member,
                        );
                } else {
                    assert(kept.contains_key(key));
                    assert(kept.values().contains(member));
                    crate::betree::Utils_v::
                        lemma_union_set_of_sets_subset(
                            kept.values(),
                            member,
                        );
                }
            } else if summary_aus(kept).contains(au) {
                let member =
                    crate::betree::Utils_v::
                        lemma_union_set_of_sets_contains(
                            kept.values(),
                            au,
                        );
                let key = choose |key: AU|
                    kept.contains_key(key)
                        && kept[key] == member;
                assert(summary.contains_key(key));
                assert(summary.values().contains(member));
                crate::betree::Utils_v::
                    lemma_union_set_of_sets_subset(
                        summary.values(),
                        member,
                    );
            } else if summary_aus(dropped).contains(au) {
                let member =
                    crate::betree::Utils_v::
                        lemma_union_set_of_sets_contains(
                            dropped.values(),
                            au,
                        );
                let key = choose |key: AU|
                    dropped.contains_key(key)
                        && dropped[key] == member;
                assert(summary.contains_key(key));
                assert(summary.values().contains(member));
                crate::betree::Utils_v::
                    lemma_union_set_of_sets_subset(
                        summary.values(),
                        member,
                    );
            }
        }
    }
}

proof fn direct_au_restrict_is_domain<V>(
    entries: Map<Address, V>,
    live: Set<Address>,
)
    requires
        live <= entries.dom(),
        set_addrs_disjoint_aus(entries.dom()),
    ensures
        crate::allocation_layer::Likes_v::restrict_domain_au(
            entries,
            to_aus(live),
        ) == live,
{
    crate::disk::GenericDisk_v::to_aus_domain(live);
    let kept = crate::allocation_layer::Likes_v::restrict_domain_au(
        entries,
        to_aus(live),
    );
    assert forall |addr: Address| #[trigger] live.contains(addr)
        implies kept.contains(addr)
    by {
        assert(entries.contains_key(addr));
        assert(to_aus(live).contains(addr.au));
    };
    assert forall |addr: Address| #[trigger] kept.contains(addr)
        implies live.contains(addr)
    by {
        assert(to_aus(live).contains(addr.au));
        let live_addr = choose |live_addr: Address|
            live.contains(live_addr) && live_addr.au == addr.au;
        assert(entries.contains_key(live_addr));
        if addr != live_addr {
            assert(addrs_with_different_au(addr, live_addr));
            assert(addr.au != live_addr.au);
        }
    };
}

proof fn union_seq_of_sets_push<A>(sets: Seq<Set<A>>, last: Set<A>)
    ensures
        crate::betree::Utils_v::union_seq_of_sets(sets.push(last))
            == crate::betree::Utils_v::union_seq_of_sets(sets) + last,
{
    assert(sets.push(last).drop_last() == sets);
    assert(sets.push(last).last() == last);
}

proof fn to_branch_nodes_restrict_agrees(
    left: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    right: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    addrs: Set<Address>,
)
    requires left.restrict(addrs) == right.restrict(addrs)
    ensures to_branch_nodes(left).restrict(addrs)
        == to_branch_nodes(right).restrict(addrs)
{
    assert_maps_equal!(
        to_branch_nodes(left).restrict(addrs),
        to_branch_nodes(right).restrict(addrs),
        addr => {
            if to_branch_nodes(left).restrict(addrs).contains_key(addr) {
                assert(addrs.contains(addr));
                assert(left.contains_key(addr));
                assert(left.restrict(addrs).contains_key(addr));
                assert(right.restrict(addrs).contains_key(addr));
                assert(right.contains_key(addr));
                assert(left.restrict(addrs)[addr]
                    == right.restrict(addrs)[addr]);
                assert(left.restrict(addrs)[addr] == left[addr]);
                assert(right.restrict(addrs)[addr] == right[addr]);
                assert(left[addr] == right[addr]);
            }
            if to_branch_nodes(right).restrict(addrs).contains_key(addr) {
                assert(addrs.contains(addr));
                assert(right.contains_key(addr));
                assert(right.restrict(addrs).contains_key(addr));
                assert(left.restrict(addrs).contains_key(addr));
                assert(left.contains_key(addr));
                assert(left.restrict(addrs)[addr]
                    == right.restrict(addrs)[addr]);
                assert(left.restrict(addrs)[addr] == left[addr]);
                assert(right.restrict(addrs)[addr] == right[addr]);
                assert(left[addr] == right[addr]);
            }
        }
    );
}

proof fn map_remove_keys_preserves_point<K, V>(
    map: Map<K, V>,
    keys: Set<K>,
    key: K,
)
    requires
        map.contains_key(key),
        !keys.contains(key),
    ensures
        map.remove_keys(keys).contains_key(key),
        map.remove_keys(keys)[key] == map[key],
        map.remove_keys(keys) <= map,
{
    assert forall |candidate: K|
        #[trigger] map.remove_keys(keys).contains_key(candidate)
        <==> map.contains_key(candidate) && !keys.contains(candidate)
    by {};
    assert(map.remove_keys(keys) <= map) by {
        assert forall |candidate: K|
            #[trigger] map.remove_keys(keys).contains_key(candidate)
            implies map.contains_key(candidate)
                && map.remove_keys(keys)[candidate] == map[candidate]
        by {};
    };
}

proof fn to_betree_nodes_restrict_agrees(
    left: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    right: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
    addrs: Set<Address>,
)
    requires left.restrict(addrs) == right.restrict(addrs)
    ensures to_betree_nodes(left).restrict(addrs)
        == to_betree_nodes(right).restrict(addrs)
{
    assert_maps_equal!(
        to_betree_nodes(left).restrict(addrs),
        to_betree_nodes(right).restrict(addrs),
        addr => {
            if to_betree_nodes(left).restrict(addrs).contains_key(addr) {
                assert(addrs.contains(addr));
                assert(left.contains_key(addr));
                assert(left.restrict(addrs).contains_key(addr));
                assert(right.restrict(addrs).contains_key(addr));
                assert(right.contains_key(addr));
                assert(left.restrict(addrs)[addr]
                    == right.restrict(addrs)[addr]);
                assert(left.restrict(addrs)[addr] == left[addr]);
                assert(right.restrict(addrs)[addr] == right[addr]);
                assert(left[addr] == right[addr]);
            }
            if to_betree_nodes(right).restrict(addrs).contains_key(addr) {
                assert(addrs.contains(addr));
                assert(right.contains_key(addr));
                assert(right.restrict(addrs).contains_key(addr));
                assert(left.restrict(addrs).contains_key(addr));
                assert(left.contains_key(addr));
                assert(left.restrict(addrs)[addr]
                    == right.restrict(addrs)[addr]);
                assert(left.restrict(addrs)[addr] == left[addr]);
                assert(right.restrict(addrs)[addr] == right[addr]);
                assert(left[addr] == right[addr]);
            }
        }
    );
}

proof fn wip_entries_equal_active_loaded_nodes(
    disk: CachingDisk::State,
    mini_allocator: MiniAllocator,
)
    ensures
        to_branch_nodes(disk.visible()).restrict(
            mini_allocator_allocated_addrs(mini_allocator),
        ) == active_loaded_nodes_of(disk, mini_allocator),
{
    assert_maps_equal!(
        to_branch_nodes(disk.visible()).restrict(
            mini_allocator_allocated_addrs(mini_allocator),
        ),
        active_loaded_nodes_of(disk, mini_allocator),
        addr => {}
    );
}

proof fn mini_allocator_allocated_addrs_after_allocate(
    mini_allocator: MiniAllocator,
    addr: Address,
)
    requires
        mini_allocator.wf(),
        mini_allocator.can_allocate(addr),
    ensures
        mini_allocator_allocated_addrs(mini_allocator.allocate(addr))
            == mini_allocator_allocated_addrs(mini_allocator).insert(addr),
{
    assert forall |candidate: Address|
        #[trigger] mini_allocator_allocated_addrs(
            mini_allocator.allocate(addr),
        ).contains(candidate)
        <==> mini_allocator_allocated_addrs(mini_allocator).insert(addr)
            .contains(candidate)
    by {
        if candidate.au == addr.au {
            assert(mini_allocator.allocate(addr).allocs[candidate.au]
                == mini_allocator.allocs[candidate.au].reserve(set![addr]));
        } else {
            assert(mini_allocator.allocate(addr).allocs.contains_key(candidate.au)
                == mini_allocator.allocs.contains_key(candidate.au));
            if mini_allocator.allocs.contains_key(candidate.au) {
                assert(mini_allocator.allocate(addr).allocs[candidate.au]
                    == mini_allocator.allocs[candidate.au]);
            }
        }
    };
}

proof fn mini_allocator_allocated_addrs_after_prune(
    mini_allocator: MiniAllocator,
    aus: Set<AU>,
)
    requires mini_allocator.wf()
    ensures
        mini_allocator_allocated_addrs(mini_allocator.prune(aus))
            == mini_allocator_allocated_addrs(mini_allocator)
                - addresses_in_aus(aus),
{
    assert forall |addr: Address|
        #[trigger] mini_allocator_allocated_addrs(
            mini_allocator.prune(aus),
        ).contains(addr)
        <==> (mini_allocator_allocated_addrs(mini_allocator)
            - addresses_in_aus(aus)).contains(addr)
    by {
        if aus.contains(addr.au) {
            assert(!mini_allocator.prune(aus).allocs.contains_key(addr.au));
        } else {
            assert(mini_allocator.prune(aus).allocs.contains_key(addr.au)
                == mini_allocator.allocs.contains_key(addr.au));
            if mini_allocator.allocs.contains_key(addr.au) {
                assert(mini_allocator.prune(aus).allocs[addr.au]
                    == mini_allocator.allocs[addr.au]);
            }
        }
    };
}

proof fn disk_access_without_alloc_or_dealloc(
    pre: CachingDisk::State,
    post: CachingDisk::State,
    guard_aus: Set<AU>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.inv(),
        crate::implementation::CachingDiskBranchBetree_v::disk_access_for_alloc(
            pre,
            post,
            Set::empty(),
            Set::empty(),
            guard_aus,
            reads,
            writes,
        ),
    ensures
        CachingDisk::State::next(
            pre,
            post,
            CachingDisk::Label::Access{reads, writes},
        ),
{
    let witness = disk_access_for_alloc_witness(
        pre,
        post,
        Set::empty(),
        Set::empty(),
        guard_aus,
        reads,
        writes,
    );
    disk_extend_empty_is_identity(pre, witness.expanded);
    assert(witness.expanded == pre);
    assert(Set::<AU>::empty() - guard_aus == Set::<AU>::empty());
    CachingDisk::State::forget_effect(
        witness.accessed,
        post,
        Set::empty() - guard_aus,
    );
    assert(post == witness.accessed) by {
        assert_maps_equal!(post.cache, witness.accessed.cache, addr => {});
        assert_maps_equal!(post.persistent, witness.accessed.persistent, addr => {});
        assert_maps_equal!(post.status, witness.accessed.status, addr => {});
    };
}

proof fn wip_entries_after_writes(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    pre_allocator: MiniAllocator,
    post_allocator: MiniAllocator,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre_disk.inv(),
        CachingDisk::State::next(
            pre_disk,
            post_disk,
            CachingDisk::Label::Access{reads, writes},
        ),
        mini_allocator_allocated_addrs(post_allocator)
            == mini_allocator_allocated_addrs(pre_allocator) + writes.dom(),
    ensures
        to_branch_nodes(post_disk.visible()).restrict(
            mini_allocator_allocated_addrs(post_allocator),
        ) == to_branch_nodes(pre_disk.visible()).restrict(
            mini_allocator_allocated_addrs(pre_allocator),
        ).union_prefer_right(to_branch_nodes(writes)),
{
    let pre_allocated = mini_allocator_allocated_addrs(pre_allocator);
    let post_allocated = mini_allocator_allocated_addrs(post_allocator);
    let write_nodes = to_branch_nodes(writes);

    CachingDisk::State::access_visible_effect(
        pre_disk,
        post_disk,
        reads,
        writes,
    );
    assert(writes.dom() <= post_allocated);
    active_loaded_nodes_follow_readable_writes(
        pre_disk,
        post_disk,
        post_allocator,
        writes,
    );
    wip_entries_equal_active_loaded_nodes(pre_disk, pre_allocator);
    wip_entries_equal_active_loaded_nodes(pre_disk, post_allocator);
    wip_entries_equal_active_loaded_nodes(post_disk, post_allocator);

    assert_maps_equal!(
        active_loaded_nodes_of(pre_disk, post_allocator)
            .union_prefer_right(write_nodes),
        active_loaded_nodes_of(pre_disk, pre_allocator)
            .union_prefer_right(write_nodes),
        addr => {
            if !write_nodes.contains_key(addr) {
                assert(!writes.contains_key(addr));
                if active_loaded_nodes_of(pre_disk, post_allocator)
                    .contains_key(addr)
                {
                    assert(post_allocated.contains(addr));
                    assert(pre_allocated.contains(addr));
                    assert(active_loaded_nodes_of(pre_disk, pre_allocator)
                        .contains_key(addr));
                }
                if active_loaded_nodes_of(pre_disk, pre_allocator)
                    .contains_key(addr)
                {
                    assert(pre_allocated.contains(addr));
                    assert(post_allocated.contains(addr));
                    assert(active_loaded_nodes_of(pre_disk, post_allocator)
                        .contains_key(addr));
                }
            }
        }
    );
}

proof fn to_betree_nodes_union_prefer_right(
    left: Map<Address, RawPage>,
    right: Map<Address, RawPage>,
)
    ensures
        to_betree_nodes(left.union_prefer_right(right))
            == to_betree_nodes(left).union_prefer_right(to_betree_nodes(right)),
{
    assert_maps_equal!(
        to_betree_nodes(left.union_prefer_right(right)),
        to_betree_nodes(left).union_prefer_right(to_betree_nodes(right)),
        addr => {}
    );
}

proof fn grow_preserves_tight_domain(
    linked: LinkedBetree<BranchNode>,
    new_root_addr: Address,
)
    requires
        linked.acyclic(),
        linked.has_root() ==> linked.root().my_domain()
            == crate::betree::Domain_v::total_domain(),
        linked.dv.entries.dom() == linked.reachable_betree_addrs(),
        linked.dv.is_fresh(set![new_root_addr]),
    ensures
        linked.grow(new_root_addr).acyclic(),
        linked.grow(new_root_addr).dv.entries.dom()
            == linked.grow(new_root_addr).reachable_betree_addrs(),
        linked.grow(new_root_addr).reachable_buffer_addrs()
            == linked.reachable_buffer_addrs(),
{
    let grown = linked.grow(new_root_addr);
    let ranking = linked.grow_new_ranking(new_root_addr);
    let child = grown.child_at_idx(0);
    assert(grown.acyclic());
    assert(grown.root().valid_child_index(0));
    assert(child.root == linked.root);
    assert(child.dv.agrees_with(linked.dv));
    assert(child.valid_ranking(ranking));
    assert(linked.valid_ranking(ranking));
    child.agreeable_disks_same_reachable_betree_addrs(linked, ranking);
    child.reachable_betree_addrs_ignore_ranking(ranking, child.the_ranking());
    linked.reachable_betree_addrs_ignore_ranking(ranking, linked.the_ranking());
    assert(child.reachable_betree_addrs() == linked.reachable_betree_addrs());
    grown.reachable_betree_addrs_using_ranking_recur_lemma(ranking, 0);
    grown.reachable_betree_addrs_ignore_ranking(ranking, grown.the_ranking());
    assert(grown.child_count() == 1);
    assert(grown.reachable_betree_addrs()
        == set![new_root_addr] + child.reachable_betree_addrs());
    assert(grown.dv.entries.dom() == linked.dv.entries.dom().insert(new_root_addr));
    assert(grown.dv.entries.dom() == grown.reachable_betree_addrs());
    child.same_reachable_betree_addrs_implies_same_buffer_addrs(linked);
    assert forall |buffer_addr: Address|
        #[trigger] grown.reachable_buffer_addrs().contains(buffer_addr)
        implies linked.reachable_buffer_addrs().contains(buffer_addr)
    by {
        let tree_addr = choose |tree_addr: Address|
            grown.reachable_buffer(tree_addr, buffer_addr);
        assert(grown.reachable_betree_addrs().contains(tree_addr));
        if tree_addr == new_root_addr {
            assert(grown.dv.get(Some(tree_addr)).buffers.len() == 0);
            assert(!grown.dv.get(Some(tree_addr)).buffers.contains(buffer_addr));
        } else {
            assert(child.reachable_betree_addrs().contains(tree_addr));
            assert(child.reachable_buffer(tree_addr, buffer_addr));
            assert(child.reachable_buffer_addrs().contains(buffer_addr));
        }
    };
    assert forall |buffer_addr: Address|
        #[trigger] linked.reachable_buffer_addrs().contains(buffer_addr)
        implies grown.reachable_buffer_addrs().contains(buffer_addr)
    by {
        assert(child.reachable_buffer_addrs().contains(buffer_addr));
        let tree_addr = choose |tree_addr: Address|
            child.reachable_buffer(tree_addr, buffer_addr);
        assert(grown.reachable_betree_addrs().contains(tree_addr));
        assert(grown.reachable_buffer(tree_addr, buffer_addr));
    };
}

pub proof fn betree_read_node_matches_visible(
    disk: CachingDisk::State,
    reads: Map<Address, RawPage>,
    addr: Address,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        reads.contains_key(addr),
        disk.visible().contains_key(addr),
    ensures
        to_betree_nodes(disk.visible()).contains_key(addr),
        to_betree_nodes(reads)[addr] == to_betree_nodes(disk.visible())[addr],
{
    assert(disk.cache.contains_key(addr));
    assert(reads[addr] == disk.cache[addr]);
    if disk.visible_cache().contains_key(addr) {
        assert(disk.visible()[addr] == disk.cache[addr]);
    } else {
        assert(disk.persistent.contains_key(addr));
        assert(disk.status.contains_key(addr));
        assert(disk.status[addr] == PageStatus::Clean);
        disk.clean_page_agrees(addr);
        assert(disk.persistent[addr] == disk.cache[addr]);
        assert(disk.visible()[addr] == disk.persistent[addr]);
    }
}

pub proof fn loaded_betree_path_tail_valid(
    loaded: LoadedBetreePath,
    reads: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
)
    requires
        loaded.valid_for(Some(loaded.root), reads),
        loaded.depth() > 0,
    ensures
        loaded.tail().valid_for(Some(loaded.tail().root), reads),
        loaded.tail().depth() + 1 == loaded.depth(),
        loaded.tail().target() == loaded.target(),
{
    let tail = loaded.tail();
    assert(loaded.wf());
    assert(tail.lines.len() > 0);
    assert(tail.lines.len() == loaded.lines.len() - 1);
    assert(tail.lines[0].addr == tail.root);
    assert forall |i: int| 0 <= i < tail.lines.len()
        implies (#[trigger] tail.lines[i]).wf()
    by {
        assert(tail.lines[i] == loaded.lines[i + 1]);
    };
    assert forall |i: int| 0 <= i < tail.lines.len()
        implies (#[trigger] tail.lines[i]).node.key_in_domain(tail.key)
    by {
        assert(tail.lines[i] == loaded.lines[i + 1]);
    };
    assert forall |i: int| 0 <= i < tail.lines.len() - 1
        implies (#[trigger] tail.lines[i]).node.is_index()
    by {
        assert(tail.lines[i] == loaded.lines[i + 1]);
    };
    assert forall |i: int| 0 <= i < tail.lines.len() - 1 implies {
        let line = tail.lines[i];
        &&& line.node.child_ptr(tail.key) is Some
        &&& line.node.child_ptr(tail.key).unwrap()
            == (#[trigger] tail.lines[i + 1]).addr
    } by {
        assert(tail.lines[i] == loaded.lines[i + 1]);
        assert(tail.lines[i + 1] == loaded.lines[i + 2]);
        loaded_betree_path_wf_child(loaded, i + 1);
    };
    assert forall |i: int| 0 <= i < tail.lines.len() - 1
        implies (#[trigger] tail.lines[i]).node.child_ptr(tail.key) is Some
    by {
        assert(tail.lines[i] == loaded.lines[i + 1]);
        loaded_betree_path_wf_child(loaded, i + 1);
    };
    assert forall |i: int| 0 <= i < tail.lines.len() implies {
        &&& reads.contains_key(tail.lines[i].addr)
        &&& #[trigger] reads[tail.lines[i].addr] == tail.lines[i].node
    } by {
        assert(tail.lines[i] == loaded.lines[i + 1]);
    };
    assert(tail.wf());
    assert(tail.needed_addrs() <= reads.dom()) by {
        assert forall |addr: Address| #[trigger] tail.needed_addrs().contains(addr)
            implies reads.dom().contains(addr)
        by {
            let i = choose |i: int| 0 <= i < tail.lines.len()
                && tail.lines[i].addr == addr;
            assert(tail.lines[i] == loaded.lines[i + 1]);
            assert(reads.contains_key(addr));
        }
    }
    assert(tail.target() == loaded.target()) by {
        assert(tail.lines.last() == loaded.lines.last());
    };
}

pub proof fn loaded_betree_path_wf_child(loaded: LoadedBetreePath, i: int)
    requires
        loaded.wf(),
        0 <= i < loaded.lines.len() - 1,
    ensures
        loaded.lines[i].node.child_ptr(loaded.key) is Some,
        loaded.lines[i].node.child_ptr(loaded.key).unwrap()
            == loaded.lines[i + 1].addr,
{
    assert(loaded.lines[i + 1].addr == loaded.lines[i + 1].addr);
}

proof fn loaded_path_reads_come_from_pre_cache(
    pre_disk: CachingDisk::State,
    expanded: CachingDisk::State,
    allocs: Set<AU>,
    owned_aus: Set<AU>,
    linked: LinkedBetree<BranchNode>,
    reads: Map<Address, RawPage>,
    loaded: LoadedBetreePath,
)
    requires
        pre_disk.inv(),
        disk_extend_for_alloc(pre_disk, expanded, allocs),
        reads <= expanded.cache,
        owned_aus.disjoint(allocs),
        linked.acyclic(),
        linked.dv.entries.dom() <= addresses_in_aus(owned_aus),
        linked.dv.entries <= to_betree_nodes(pre_disk.visible()),
        loaded.valid_for(linked.root, to_betree_nodes(reads)),
    ensures
        reads.restrict(loaded.needed_addrs()) <= pre_disk.cache,
    decreases loaded.depth(),
{
    let root = linked.root.unwrap();
    assert(linked.dv.entries.contains_key(root));
    assert(loaded.needed_addrs().contains(root)) by {
        assert(loaded.lines[0].addr == loaded.root);
    };
    assert(to_betree_nodes(reads).contains_key(root));
    assert(owned_aus.contains(root.au));
    assert(!allocs.contains(root.au));
    assert(reads.contains_key(root));
    assert(expanded.cache.contains_key(root));
    assert(pre_disk.cache.contains_key(root)) by {
        if !pre_disk.cache.contains_key(root) {
            assert((expanded.cache.dom() - pre_disk.cache.dom())
                .contains(root));
            assert(addresses_in_aus(allocs).contains(root));
        }
    };
    assert(expanded.cache[root] == pre_disk.cache[root]);
    assert(reads[root] == pre_disk.cache[root]);
    assert(to_betree_nodes(pre_disk.visible()).contains_key(root));
    assert(pre_disk.visible().contains_key(root));

    let root_read = reads.restrict(set![root]);
    assert(root_read <= pre_disk.cache);
    betree_read_node_matches_visible(pre_disk, root_read, root);
    assert(to_betree_nodes(reads)[root] == linked.dv.entries[root]);
    assert(loaded.lines[0].node == linked.root());

    if loaded.depth() > 0 {
        let tail = loaded.tail();
        let child = linked.child_for_key(loaded.key);
        loaded_betree_path_wf_child(loaded, 0);
        assert(child.root == Some(tail.root));
        assert(linked.root().is_index());
        let ranking = linked.the_ranking();
        assert(linked.valid_ranking(ranking));
        assert(child.valid_ranking(ranking)) by {
            let child_idx = linked.root().pivots.route(loaded.key) as nat;
            linked.root().pivots.route_lemma(loaded.key);
            assert(linked.root().valid_child_index(child_idx));
            assert(linked.dv.node_children_respects_rank(ranking, root));
            assert(ranking.contains_key(tail.root));
        };
        assert(child.acyclic());
        loaded_betree_path_tail_valid(
            loaded,
            to_betree_nodes(reads),
        );
        assert(tail.valid_for(child.root, to_betree_nodes(reads)));
        loaded_path_reads_come_from_pre_cache(
            pre_disk,
            expanded,
            allocs,
            owned_aus,
            child,
            reads,
            tail,
        );
        assert forall |addr: Address|
            #[trigger] reads.restrict(loaded.needed_addrs())
                .contains_key(addr)
            implies pre_disk.cache.contains_key(addr)
                && reads.restrict(loaded.needed_addrs())[addr]
                    == pre_disk.cache[addr]
        by {
            if addr != root {
                assert(tail.needed_addrs().contains(addr)) by {
                    let i = choose |i: int|
                        0 <= i < loaded.lines.len()
                            && loaded.lines[i].addr == addr;
                    assert(i > 0);
                    assert(tail.lines[i - 1] == loaded.lines[i]);
                };
                assert(reads.restrict(tail.needed_addrs())
                    .contains_key(addr));
            }
        };
    } else {
        assert(loaded.lines.len() == 1);
        assert(loaded.needed_addrs() == set![root]) by {
            assert forall |addr: Address|
                #[trigger] loaded.needed_addrs().contains(addr)
                implies addr == root
            by {
                let i = choose |i: int|
                    0 <= i < loaded.lines.len()
                        && loaded.lines[i].addr == addr;
                assert(i == 0);
            };
        };
    }
}

pub proof fn loaded_betree_path_matches_linked(
    disk: CachingDisk::State,
    linked: LinkedBetree<BranchNode>,
    reads: Map<Address, RawPage>,
    loaded: LoadedBetreePath,
    depth: nat,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        linked.acyclic(),
        linked.dv.entries <= to_betree_nodes(disk.visible()),
        loaded.valid_for(linked.root, to_betree_nodes(reads)),
        depth <= loaded.depth(),
    ensures ({
        let path = Path{linked, key: loaded.key, depth};
        &&& path.valid()
        &&& path.target().acyclic()
        &&& path.target().root == Some(loaded.lines[depth as int].addr)
        &&& path.target().root() == loaded.lines[depth as int].node
        &&& path.target().dv == linked.dv
        &&& path.target().buffer_dv == linked.buffer_dv
    }),
    decreases depth,
{
    let loaded_reads = to_betree_nodes(reads);
    let path = Path{linked, key: loaded.key, depth};
    let root = linked.root.unwrap();
    assert(loaded.wf());
    assert(loaded.needed_addrs().contains(root)) by {
        assert(loaded.lines[0].addr == loaded.root);
    }
    assert(loaded_reads.contains_key(root));
    assert(linked.dv.entries.contains_key(root));
    assert(to_betree_nodes(disk.visible()).contains_key(root));
    betree_read_node_matches_visible(disk, reads, root);
    assert(loaded_reads[root] == linked.dv.entries[root]);
    assert(linked.root() == loaded.lines[0].node);

    if depth == 0 {
        assert(path.valid());
        assert(path.target() == linked);
    } else {
        assert(loaded.lines.len() > 1);
        let ranking = linked.the_ranking();
        let child = linked.child_for_key(loaded.key);
        let tail = loaded.tail();
        let child_addr = loaded.lines[1].addr;
        loaded_betree_path_wf_child(loaded, 0);
        assert(linked.root().child_ptr(loaded.key) == Some(child_addr));
        assert(child.root == Some(child_addr));
        assert(linked.root().is_index());
        assert(linked.dv.is_nondangling_ptr(Some(child_addr))) by {
            let child_idx = linked.root().pivots.route(loaded.key) as nat;
            linked.root().pivots.route_lemma(loaded.key);
            assert(linked.root().valid_child_index(child_idx));
            assert(linked.dv.node_has_nondangling_child_ptrs(linked.root()));
        }
        assert(child.wf());
        assert(child.valid_ranking(ranking)) by {
            assert(linked.valid_ranking(ranking));
            let child_idx = linked.root().pivots.route(loaded.key) as nat;
            linked.root().pivots.route_lemma(loaded.key);
            assert(linked.root().valid_child_index(child_idx));
            assert(linked.dv.node_children_respects_rank(ranking, root));
            assert(ranking.contains_key(child_addr));
        }
        assert(child.acyclic());
        loaded_betree_path_tail_valid(loaded, loaded_reads);
        assert(tail.valid_for(child.root, loaded_reads));
        assert(depth - 1 <= tail.depth());
        loaded_betree_path_matches_linked(disk, child, reads, tail, (depth - 1) as nat);
        assert(path.subpath() == Path{
            linked: child,
            key: tail.key,
            depth: (depth - 1) as nat,
        });
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(tail.lines[(depth - 1) as int] == loaded.lines[depth as int]);
    }
}

proof fn loaded_path_addrs_match_linked(
    disk: CachingDisk::State,
    linked: LinkedBetree<BranchNode>,
    reads: Map<Address, RawPage>,
    loaded: LoadedBetreePath,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        linked.acyclic(),
        linked.dv.entries <= to_betree_nodes(disk.visible()),
        loaded.valid_for(linked.root, to_betree_nodes(reads)),
    ensures ({
        let path = Path {
            linked,
            key: loaded.key,
            depth: loaded.depth(),
        };
        &&& path.valid()
        &&& loaded.path_addrs()
            == path.addrs_on_path().push(path.target().root.unwrap())
    }),
    decreases loaded.depth(),
{
    loaded_betree_path_matches_linked(
        disk,
        linked,
        reads,
        loaded,
        loaded.depth(),
    );
    let path = Path {
        linked,
        key: loaded.key,
        depth: loaded.depth(),
    };
    if loaded.depth() == 0 {
        assert(loaded.lines.len() == 1);
        assert(path.addrs_on_path() == Seq::<Address>::empty());
        assert(path.target().root.unwrap() == loaded.lines[0].addr);
        assert_seqs_equal!(
            loaded.path_addrs(),
            path.addrs_on_path().push(path.target().root.unwrap()),
            i => { assert(i == 0); }
        );
    } else {
        let tail = loaded.tail();
        let child = linked.child_for_key(loaded.key);
        loaded_betree_path_wf_child(loaded, 0);
        loaded_betree_path_matches_linked(
            disk,
            linked,
            reads,
            loaded,
            0,
        );
        assert(linked.root() == loaded.lines[0].node);
        assert(linked.root().child_ptr(loaded.key) == Some(tail.root));
        assert(child.root == Some(tail.root));
        assert(linked.root().is_index());
        assert(child.valid_ranking(linked.the_ranking())) by {
            let ranking = linked.the_ranking();
            let child_idx = linked.root().pivots.route(loaded.key) as nat;
            linked.root().pivots.route_lemma(loaded.key);
            assert(linked.root().valid_child_index(child_idx));
            assert(linked.dv.node_children_respects_rank(
                ranking,
                linked.root.unwrap(),
            ));
            assert(ranking.contains_key(tail.root));
        };
        assert(child.acyclic());
        loaded_betree_path_tail_valid(
            loaded,
            to_betree_nodes(reads),
        );
        loaded_path_addrs_match_linked(disk, child, reads, tail);
        assert(path.subpath() == Path {
            linked: child,
            key: tail.key,
            depth: tail.depth(),
        });
        assert(path.addrs_on_path()
            == seq![linked.root.unwrap()] + path.subpath().addrs_on_path());
        assert(loaded.path_addrs()
            == seq![loaded.root] + tail.path_addrs());
        assert(linked.root.unwrap() == loaded.root);
    }
}

proof fn loaded_substitute_writes_match(
    disk: CachingDisk::State,
    reads: Map<Address, RawPage>,
    loaded: LoadedBetreePath,
    path: Path<BranchNode>,
    new_subtree_root: Address,
    replacement: LinkedBetree<BranchNode>,
    replacement_writes: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    path_addrs: PathAddrs,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        path.valid(),
        path.linked.dv.entries <= to_betree_nodes(disk.visible()),
        loaded.valid_for(path.linked.root, to_betree_nodes(reads)),
        loaded.key == path.key,
        loaded.depth() == path.depth,
        path_addrs.len() == path.depth,
        path_addrs.no_duplicates(),
        path_addrs.to_set().disjoint(path.linked.dv.entries.dom()),
        path_addrs.to_set().disjoint(replacement_writes.dom()),
        replacement.root == Some(new_subtree_root),
        replacement.dv.entries
            == path.linked.dv.entries.union_prefer_right(replacement_writes),
    ensures ({
        let substituted = path.substitute(replacement, path_addrs);
        let writes = crate::implementation::CachedBranchBetree_v::substitute_writes(
            loaded,
            new_subtree_root,
            replacement_writes,
            path_addrs,
        );
        &&& substituted.root == Some(
            crate::implementation::CachedBranchBetree_v::replacement_root(
                loaded,
                new_subtree_root,
                path_addrs,
            ),
        )
        &&& substituted.dv.entries
            == path.linked.dv.entries.union_prefer_right(writes)
        &&& substituted.buffer_dv == replacement.buffer_dv
        &&& writes.dom() <= replacement_writes.dom() + path_addrs.to_set()
    }),
    decreases path.depth,
{
    loaded_betree_path_matches_linked(
        disk,
        path.linked,
        reads,
        loaded,
        0,
    );
    assert(loaded.lines[0].node == path.linked.root());
    if path.depth == 0 {
        assert(loaded.depth() == 0);
        assert(path_addrs.len() == 0);
        assert(path_addrs == Seq::<Address>::empty());
    } else {
        assert(loaded.lines.len() > 1);
        let tail = loaded.tail();
        let subpath = path.subpath();
        let tail_addrs = path_addrs.skip(1);
        loaded_betree_path_tail_valid(
            loaded,
            to_betree_nodes(reads),
        );
        assert(tail.wf());
        assert(subpath.valid());
        assert(tail.key == subpath.key);
        assert(tail.depth() == subpath.depth);
        loaded_betree_path_matches_linked(
            disk,
            path.linked,
            reads,
            loaded,
            1,
        );
        let one = Path {
            linked: path.linked,
            key: path.key,
            depth: 1,
        };
        assert(one.target() == subpath.linked);
        assert(one.target().root == Some(loaded.lines[1].addr));
        assert(tail.root == loaded.lines[1].addr);
        assert(tail.root == subpath.linked.root.unwrap());
        assert(tail.lines[0].node == subpath.linked.root());
        assert(tail_addrs.len() == subpath.depth);
        assert(tail_addrs.no_duplicates());
        assert(tail_addrs.to_set().disjoint(
            subpath.linked.dv.entries.dom(),
        ));
        assert(tail_addrs.to_set().disjoint(replacement_writes.dom()));
        assert(subpath.linked.dv == path.linked.dv);
        assert(subpath.linked.buffer_dv == path.linked.buffer_dv);
        assert(subpath.linked.dv.entries
            <= to_betree_nodes(disk.visible()));
        loaded_substitute_writes_match(
            disk,
            reads,
            tail,
            subpath,
            new_subtree_root,
            replacement,
            replacement_writes,
            tail_addrs,
        );

        let child_root =
            crate::implementation::CachedBranchBetree_v::replacement_root(
                tail,
                new_subtree_root,
                tail_addrs,
            );
        let child_idx = loaded.lines[0].node.pivots.route(loaded.key);
        let new_node = crate::betree::LinkedBetree_v::BetreeNode {
            children: loaded.lines[0].node.children.update(
                child_idx,
                Some(child_root),
            ),
            ..loaded.lines[0].node
        };
        let tail_writes =
            crate::implementation::CachedBranchBetree_v::substitute_writes(
                tail,
                new_subtree_root,
                replacement_writes,
                tail_addrs,
            );
        assert(!tail_writes.contains_key(path_addrs[0])) by {
            assert(tail_writes.dom()
                <= replacement_writes.dom() + tail_addrs.to_set());
        };
        let subtree = subpath.substitute(replacement, tail_addrs);
        assert(subtree.dv.entries
            == path.linked.dv.entries.union_prefer_right(tail_writes));
        assert(path.substitute(replacement, path_addrs).dv.entries
            == subtree.dv.entries.insert(path_addrs[0], new_node));
        assert(!path.linked.dv.entries.contains_key(path_addrs[0]));
        assert_maps_equal!(
            path.substitute(replacement, path_addrs).dv.entries,
            path.linked.dv.entries.union_prefer_right(
                tail_writes.insert(path_addrs[0], new_node),
            ),
            addr => {
                if addr == path_addrs[0] {
                    assert(!tail_writes.contains_key(addr));
                    assert(!path.linked.dv.entries.contains_key(addr));
                }
            }
        );
    }
}

proof fn branch_receipts_match_query_from(
    disk: CachingDisk::State,
    buffer_dv: BufferDisk<BranchNode>,
    roots: LinkedSeq,
    start: nat,
    receipts: Seq<crate::implementation::CachedBranch_v::LoadedPathReceipt>,
    key: crate::spec::KeyType_t::Key,
    reads: Map<Address, RawPage>,
    receipt_idx: int,
)
    requires
        disk.inv(),
        reads <= disk.cache,
        branch_receipts_valid(
            roots,
            start,
            receipts,
            key,
            to_branch_nodes(reads),
        ),
        buffer_dv.valid_buffers(roots),
        buffer_dv.sealed_branch_roots(roots.addrs.to_set()),
        buffer_dv.entries <= to_branch_nodes(disk.visible()),
        0 <= receipt_idx <= receipts.len(),
    ensures
        buffer_dv.query_from(roots, key, start as int + receipt_idx)
            == branch_receipts_result(receipts, receipt_idx),
    decreases receipts.len() - receipt_idx,
{
    if receipt_idx < receipts.len() {
        let root_idx = start as int + receipt_idx;
        let root = roots[root_idx];
        let receipt = receipts[receipt_idx];
        let branch = buffer_dv.get_branch(root);
        assert(root_idx < roots.len());
        assert(roots.addrs.to_set().contains(root));
        buffer_dv.sealed_branch_roots_contains(roots.addrs.to_set(), root);
        assert(branch.valid_sealed_branch());
        assert(branch.inv());
        assert(receipt.valid_for(root, to_branch_nodes(reads)));
        assert(receipt.target().node is Leaf);
        assert(branch.disk_view.entries == buffer_dv.entries);
        receipt_query_matches_branch_query(disk, branch, reads, receipt);
        branch_receipts_match_query_from(
            disk,
            buffer_dv,
            roots,
            start,
            receipts,
            key,
            reads,
            receipt_idx + 1,
        );
    }
}

pub open spec fn loaded_query_receipt_i(
    receipt: LoadedBetreeQueryReceipt,
    linked: LinkedBetree<BranchNode>,
) -> QueryReceipt<BranchNode> {
    let line_count = receipt.path.lines.len();
    QueryReceipt {
        key: receipt.path.key,
        linked,
        lines: Seq::new(line_count + 1, |i: int| {
            if i < line_count {
                QueryReceiptLine {
                    linked: Path {
                        linked,
                        key: receipt.path.key,
                        depth: i as nat,
                    }.target(),
                    result: receipt.result_at(i),
                }
            } else {
                QueryReceiptLine {
                    linked: LinkedBetree {
                        root: None,
                        dv: linked.dv,
                        buffer_dv: linked.buffer_dv,
                    },
                    result: Message::Define{value: default_value()},
                }
            }
        }),
    }
}

proof fn loaded_query_result_is_define(
    receipt: LoadedBetreeQueryReceipt,
    i: int,
)
    requires
        receipt.path.lines.len() > 0,
        receipt.buffer_receipts.len() == receipt.path.lines.len(),
        0 <= i < receipt.path.lines.len(),
    ensures receipt.result_at(i) is Define,
    decreases receipt.path.lines.len() - i,
{
    if i < receipt.path.lines.len() - 1 {
        loaded_query_result_is_define(receipt, i + 1);
    }
}

proof fn agreeable_branches_same_reachable(
    left: LinkedBranch<Summary>,
    right: LinkedBranch<Summary>,
    left_ranking: crate::disk::GenericDisk_v::Ranking,
    right_ranking: crate::disk::GenericDisk_v::Ranking,
)
    requires
        left.inv_internal(left_ranking),
        right.inv_internal(right_ranking),
        left.root == right.root,
        left.disk_view.agrees_with_disk(right.disk_view),
    ensures
        left.reachable_addrs_using_ranking(left_ranking)
            == right.reachable_addrs_using_ranking(right_ranking),
    decreases left.get_rank(left_ranking), right.get_rank(right_ranking),
{
    assert(left.disk_view.entries.contains_key(left.root));
    assert(right.disk_view.entries.contains_key(right.root));
    assert(left.disk_view.entries[left.root]
        == right.disk_view.entries[right.root]);
    assert(left.root() == right.root());
    if left.root() is Index {
        assert(right.root() is Index);
        assert(left.root()->children == right.root()->children);
        assert forall |i: int| 0 <= i < left.root()->children.len()
            implies (#[trigger] left.child_reachable_addrs_using_ranking(left_ranking, i))
                == right.child_reachable_addrs_using_ranking(right_ranking, i)
        by {
            assert(left.root().valid_child_index(i));
            assert(right.root().valid_child_index(i));
            let left_child = left.child_at_idx(i);
            let right_child = right.child_at_idx(i);
            assert(left_child.root == right_child.root);
            assert(left_child.disk_view == left.disk_view);
            assert(right_child.disk_view == right.disk_view);
            child_branch_inv_internal_from_parent(left, left_ranking, i);
            child_branch_inv_internal_from_parent(right, right_ranking, i);
            assert(left_child.inv_internal(left_ranking));
            assert(right_child.inv_internal(right_ranking));
            assert(left_ranking[left_child.root] < left_ranking[left.root]);
            assert(right_ranking[right_child.root] < right_ranking[right.root]);
            agreeable_branches_same_reachable(
                left_child,
                right_child,
                left_ranking,
                right_ranking,
            );
        };
        assert_seqs_equal!(
            left.children_reachable_addrs_using_ranking(left_ranking),
            right.children_reachable_addrs_using_ranking(right_ranking),
            i => {
                assert(left.child_reachable_addrs_using_ranking(left_ranking, i)
                    == right.child_reachable_addrs_using_ranking(right_ranking, i));
            }
        );
    }
}

proof fn agreeable_betrees_same_reachable_recur(
    left: LinkedBetree<BranchNode>,
    right: LinkedBetree<BranchNode>,
    left_ranking: crate::disk::GenericDisk_v::Ranking,
    right_ranking: crate::disk::GenericDisk_v::Ranking,
    child_idx: nat,
)
    requires
        left.can_recurse_for_reachable(left_ranking, child_idx),
        right.can_recurse_for_reachable(right_ranking, child_idx),
        left.root().children == right.root().children,
        left.dv.agrees_with(right.dv),
    ensures
        left.reachable_betree_addrs_using_ranking_recur(
            left_ranking, child_idx,
        ) == right.reachable_betree_addrs_using_ranking_recur(
            right_ranking, child_idx,
        ),
    decreases
        left.get_rank(left_ranking),
        right.get_rank(right_ranking),
        left.child_count() - child_idx,
{
    if child_idx < left.child_count() {
        assert(left.root().valid_child_index(child_idx));
        assert(right.root().valid_child_index(child_idx));
        let left_child = left.child_at_idx(child_idx);
        let right_child = right.child_at_idx(child_idx);
        assert(left_child.root == right_child.root);
        assert(left_child.valid_ranking(left_ranking));
        assert(right_child.valid_ranking(right_ranking));
        agreeable_betrees_same_reachable(
            left_child, right_child, left_ranking, right_ranking,
        );
        agreeable_betrees_same_reachable_recur(
            left, right, left_ranking, right_ranking, child_idx + 1,
        );
    }
}

proof fn agreeable_betrees_same_reachable(
    left: LinkedBetree<BranchNode>,
    right: LinkedBetree<BranchNode>,
    left_ranking: crate::disk::GenericDisk_v::Ranking,
    right_ranking: crate::disk::GenericDisk_v::Ranking,
)
    requires
        left.valid_ranking(left_ranking),
        right.valid_ranking(right_ranking),
        left.root == right.root,
        left.dv.agrees_with(right.dv),
    ensures
        left.reachable_betree_addrs_using_ranking(left_ranking)
            == right.reachable_betree_addrs_using_ranking(right_ranking),
    decreases left.get_rank(left_ranking), right.get_rank(right_ranking),
{
    if left.has_root() {
        assert(right.has_root());
        assert(left.root() == right.root());
        assert(left.root().children == right.root().children);
        agreeable_betrees_same_reachable_recur(
            left, right, left_ranking, right_ranking, 0,
        );
    }
}

pub proof fn tight_branch_unique(
    loose_disk: BufferDisk<BranchNode>,
    root: Address,
    summary: Summary,
    left: LinkedBranch<Summary>,
    right: LinkedBranch<Summary>,
)
    requires
        tight_branch_in_loose_disk(loose_disk, root, summary, left),
        tight_branch_in_loose_disk(loose_disk, root, summary, right),
    ensures left == right,
{
    let left_ranking = left.the_ranking();
    let right_ranking = right.the_ranking();
    assert(left.disk_view.agrees_with_disk(right.disk_view)) by {
        assert forall |addr: Address|
            #[trigger] left.disk_view.entries.contains_key(addr)
                && right.disk_view.entries.contains_key(addr)
            implies left.disk_view.entries[addr] == right.disk_view.entries[addr]
        by {
            assert(loose_disk.entries.contains_key(addr));
            assert(left.disk_view.entries[addr] == loose_disk.entries[addr]);
            assert(right.disk_view.entries[addr] == loose_disk.entries[addr]);
        };
    }
    agreeable_branches_same_reachable(
        left,
        right,
        left_ranking,
        right_ranking,
    );
    assert(left.representation() == right.representation());
    assert(left.root() == right.root());
    assert(left.full_repr() == right.full_repr());
    assert(left.disk_view.entries.dom() == right.disk_view.entries.dom());
    assert_maps_equal!(left.disk_view.entries, right.disk_view.entries, addr => {
        if left.disk_view.entries.contains_key(addr) {
            assert(right.disk_view.entries.contains_key(addr));
            assert(loose_disk.entries.contains_key(addr));
        }
        if right.disk_view.entries.contains_key(addr) {
            assert(left.disk_view.entries.contains_key(addr));
        }
    });
}

pub proof fn tight_branch_unique_in_unbounded_disk(
    loose_disk: BufferDisk<BranchNode>,
    root: Address,
    left: LinkedBranch<Summary>,
    right: LinkedBranch<Summary>,
)
    requires
        left.root == root,
        right.root == root,
        left.valid_sealed_branch(),
        right.valid_sealed_branch(),
        left.tight_disk_view_with_summary(),
        right.tight_disk_view_with_summary(),
        left.disk_view.entries <= loose_disk.entries,
        right.disk_view.entries <= loose_disk.entries,
    ensures left == right,
{
    let left_ranking = left.the_ranking();
    let right_ranking = right.the_ranking();
    assert(left.disk_view.agrees_with_disk(right.disk_view)) by {
        assert forall |addr: Address|
            #[trigger] left.disk_view.entries.contains_key(addr)
                && right.disk_view.entries.contains_key(addr)
            implies left.disk_view.entries[addr]
                == right.disk_view.entries[addr]
        by {
            assert(loose_disk.entries.contains_key(addr));
            assert(left.disk_view.entries[addr] == loose_disk.entries[addr]);
            assert(right.disk_view.entries[addr] == loose_disk.entries[addr]);
        };
    }
    agreeable_branches_same_reachable(
        left,
        right,
        left_ranking,
        right_ranking,
    );
    assert(left.representation() == right.representation());
    assert(left.root() == right.root());
    assert(left.full_repr() == right.full_repr());
    assert(left.disk_view.entries.dom() == right.disk_view.entries.dom());
    assert_maps_equal!(left.disk_view.entries, right.disk_view.entries, addr => {
        if left.disk_view.entries.contains_key(addr) {
            assert(right.disk_view.entries.contains_key(addr));
            assert(loose_disk.entries.contains_key(addr));
        }
        if right.disk_view.entries.contains_key(addr) {
            assert(left.disk_view.entries.contains_key(addr));
        }
    });
}

pub proof fn tight_branch_of_equals_candidate(
    loose_disk: BufferDisk<BranchNode>,
    root: Address,
    summary: Summary,
    candidate: LinkedBranch<Summary>,
)
    requires tight_branch_in_loose_disk(loose_disk, root, summary, candidate)
    ensures tight_branch_of(loose_disk, root, summary) == candidate
{
    assert(tight_branch_exists(loose_disk, root, summary));
    tight_branch_of_is_candidate(loose_disk, root, summary);
    tight_branch_unique(
        loose_disk,
        root,
        summary,
        tight_branch_of(loose_disk, root, summary),
        candidate,
    );
}

proof fn tight_sealed_branch_disk_insert(
    pre_loose: BufferDisk<BranchNode>,
    post_loose: BufferDisk<BranchNode>,
    pre_roots: Set<Address>,
    new_root: Address,
    pre_summary: Map<AU, Summary>,
    post_summary: Map<AU, Summary>,
    new_branch: LinkedBranch<Summary>,
)
    requires
        post_summary == pre_summary.insert(new_root.au, new_branch.get_summary()),
        !pre_summary.contains_key(new_root.au),
        tight_branch_in_loose_disk(
            loose_disk_for_summary(post_loose, new_branch.get_summary()),
            new_root,
            new_branch.get_summary(),
            new_branch,
        ),
        forall |root: Address| #[trigger] pre_roots.contains(root) ==> {
            &&& pre_summary.contains_key(root.au)
            &&& tight_branch_exists(
                loose_disk_for_summary(
                    pre_loose, pre_summary[root.au],
                ),
                root,
                pre_summary[root.au],
            )
            &&& loose_disk_for_summary(
                post_loose, post_summary[root.au],
            ) == loose_disk_for_summary(
                pre_loose, pre_summary[root.au],
            )
        },
    ensures
        tight_sealed_branch_disk(
            post_loose,
            pre_roots.insert(new_root),
            post_summary,
        ).entries == tight_sealed_branch_disk(
            pre_loose,
            pre_roots,
            pre_summary,
        ).entries.union_prefer_right(new_branch.disk_view.entries),
{
    tight_branch_of_equals_candidate(
        loose_disk_for_summary(post_loose, new_branch.get_summary()),
        new_root,
        new_branch.get_summary(),
        new_branch,
    );
    assert_maps_equal!(
        tight_sealed_branch_disk(
            post_loose,
            pre_roots.insert(new_root),
            post_summary,
        ).entries,
        tight_sealed_branch_disk(
            pre_loose,
            pre_roots,
            pre_summary,
        ).entries.union_prefer_right(new_branch.disk_view.entries),
        addr => {
            if tight_branch_addrs(
                post_loose,
                pre_roots.insert(new_root),
                post_summary,
            ).contains(addr) {
                let root = choose |root: Address|
                    pre_roots.insert(new_root).contains(root)
                    && tight_branch_of(
                        loose_disk_for_summary(
                            post_loose, post_summary[root.au],
                        ),
                        root,
                        post_summary[root.au],
                    ).disk_view.entries.contains_key(addr);
                if root == new_root {
                    assert(new_branch.disk_view.entries.contains_key(addr));
                    assert(post_loose.entries.contains_key(addr)) by {
                        assert(new_branch.disk_view.entries
                            <= loose_disk_for_summary(
                                post_loose, new_branch.get_summary(),
                            ).entries);
                        assert(loose_disk_for_summary(
                            post_loose, new_branch.get_summary(),
                        ).entries.contains_key(addr));
                    };
                } else {
                    assert(pre_roots.contains(root));
                    assert(post_summary[root.au] == pre_summary[root.au]);
                    tight_branch_of_is_candidate(
                        loose_disk_for_summary(
                            pre_loose, pre_summary[root.au],
                        ),
                        root,
                        pre_summary[root.au],
                    );
                    assert(tight_branch_of(
                        loose_disk_for_summary(
                            pre_loose, pre_summary[root.au],
                        ),
                        root,
                        pre_summary[root.au],
                    ).disk_view.entries <= loose_disk_for_summary(
                        pre_loose, pre_summary[root.au],
                    ).entries);
                    assert(loose_disk_for_summary(
                        pre_loose, pre_summary[root.au],
                    ).entries.contains_key(addr));
                    assert(pre_loose.entries.contains_key(addr));
                    assert(post_loose.entries.contains_key(addr)) by {
                        assert(loose_disk_for_summary(
                            post_loose, post_summary[root.au],
                        ) == loose_disk_for_summary(
                            pre_loose, pre_summary[root.au],
                        ));
                        assert(loose_disk_for_summary(
                            post_loose, post_summary[root.au],
                        ).entries.contains_key(addr));
                    };
                    assert(exists |old_root: Address|
                        pre_roots.contains(old_root)
                        && tight_branch_of(
                            loose_disk_for_summary(
                                pre_loose, pre_summary[old_root.au],
                            ),
                            old_root,
                            pre_summary[old_root.au],
                        ).disk_view.entries.contains_key(addr)) by {
                        assert(pre_roots.contains(root));
                    };
                }
            }
            if tight_branch_addrs(
                pre_loose, pre_roots, pre_summary,
            ).contains(addr) {
                let root = choose |root: Address|
                    pre_roots.contains(root)
                    && tight_branch_of(
                        loose_disk_for_summary(
                            pre_loose, pre_summary[root.au],
                        ),
                        root,
                        pre_summary[root.au],
                    ).disk_view.entries.contains_key(addr);
                assert(post_summary[root.au] == pre_summary[root.au]);
                tight_branch_of_is_candidate(
                    loose_disk_for_summary(
                        pre_loose, pre_summary[root.au],
                    ),
                    root,
                    pre_summary[root.au],
                );
                assert(tight_branch_of(
                    loose_disk_for_summary(
                        pre_loose, pre_summary[root.au],
                    ),
                    root,
                    pre_summary[root.au],
                ).disk_view.entries <= loose_disk_for_summary(
                    pre_loose, pre_summary[root.au],
                ).entries);
                assert(loose_disk_for_summary(
                    pre_loose, pre_summary[root.au],
                ).entries.contains_key(addr));
                assert(pre_loose.entries.contains_key(addr));
                assert(post_loose.entries.contains_key(addr)) by {
                    assert(loose_disk_for_summary(
                        post_loose, post_summary[root.au],
                    ) == loose_disk_for_summary(
                        pre_loose, pre_summary[root.au],
                    ));
                    assert(loose_disk_for_summary(
                        post_loose, post_summary[root.au],
                    ).entries.contains_key(addr));
                };
                assert(exists |post_root: Address|
                    pre_roots.insert(new_root).contains(post_root)
                    && tight_branch_of(
                        loose_disk_for_summary(
                            post_loose, post_summary[post_root.au],
                        ),
                        post_root,
                        post_summary[post_root.au],
                    ).disk_view.entries.contains_key(addr)) by {
                    assert(pre_roots.insert(new_root).contains(root));
                };
            }
            if new_branch.disk_view.entries.contains_key(addr) {
                assert(exists |post_root: Address|
                    pre_roots.insert(new_root).contains(post_root)
                    && tight_branch_of(
                        loose_disk_for_summary(
                            post_loose, post_summary[post_root.au],
                        ),
                        post_root,
                        post_summary[post_root.au],
                    ).disk_view.entries.contains_key(addr)) by {
                    assert(pre_roots.insert(new_root).contains(new_root));
                    assert(post_summary[new_root.au] == new_branch.get_summary());
                };
            }
            if tight_sealed_branch_disk(
                post_loose,
                pre_roots.insert(new_root),
                post_summary,
            ).entries.contains_key(addr) && (tight_sealed_branch_disk(
                pre_loose,
                pre_roots,
                pre_summary,
            ).entries.union_prefer_right(
                new_branch.disk_view.entries,
            )).contains_key(addr) {
                if new_branch.disk_view.entries.contains_key(addr) {
                    assert(new_branch.disk_view.entries
                        <= loose_disk_for_summary(
                            post_loose, new_branch.get_summary(),
                        ).entries);
                    assert(loose_disk_for_summary(
                        post_loose, new_branch.get_summary(),
                    ).entries.contains_key(addr));
                    assert(new_branch.disk_view.entries[addr]
                        == loose_disk_for_summary(
                            post_loose, new_branch.get_summary(),
                        ).entries[addr]);
                    assert(loose_disk_for_summary(
                        post_loose, new_branch.get_summary(),
                    ).entries[addr] == post_loose.entries[addr]);
                    assert(post_loose.entries[addr]
                        == new_branch.disk_view.entries[addr]);
                } else {
                    let root = choose |root: Address|
                        pre_roots.contains(root)
                        && tight_branch_of(
                            loose_disk_for_summary(
                                pre_loose, pre_summary[root.au],
                            ),
                            root,
                            pre_summary[root.au],
                        ).disk_view.entries.contains_key(addr);
                    assert(loose_disk_for_summary(
                        post_loose, post_summary[root.au],
                    ) == loose_disk_for_summary(
                        pre_loose, pre_summary[root.au],
                    ));
                    let old_branch = tight_branch_of(
                        loose_disk_for_summary(
                            pre_loose, pre_summary[root.au],
                        ),
                        root,
                        pre_summary[root.au],
                    );
                    assert(old_branch.disk_view.entries.contains_key(addr));
                    tight_branch_of_is_candidate(
                        loose_disk_for_summary(
                            pre_loose, pre_summary[root.au],
                        ),
                        root,
                        pre_summary[root.au],
                    );
                    assert(old_branch.disk_view.entries
                        <= loose_disk_for_summary(
                            pre_loose, pre_summary[root.au],
                        ).entries);
                    assert(loose_disk_for_summary(
                        pre_loose, pre_summary[root.au],
                    ).entries.contains_key(addr));
                    assert(post_loose.entries[addr] == pre_loose.entries[addr]);
                }
            }
        }
    );
}

proof fn tight_sealed_branch_disk_prune(
    full_loose: BufferDisk<BranchNode>,
    post_loose: BufferDisk<BranchNode>,
    full_roots: Set<Address>,
    post_roots: Set<Address>,
    full_summary: Map<AU, Summary>,
    post_summary: Map<AU, Summary>,
    branch_deallocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        full_roots.finite(),
        set_addrs_disjoint_aus(full_roots),
        post_roots <= full_roots,
        forall |root: Address| #[trigger] full_roots.contains(root) ==> {
            &&& full_summary.contains_key(root.au)
            &&& tight_branch_exists(
                loose_disk_for_summary(full_loose, full_summary[root.au]),
                root,
                full_summary[root.au],
            )
        },
        ({
            let full_buffer = tight_sealed_branch_disk(
                full_loose,
                full_roots,
                full_summary,
            );
            &&& full_buffer.to_branch_disk().wf()
            &&& full_buffer.sealed_branch_roots(full_roots)
            &&& crate::allocation_layer::AllocationBranchBetree_v::map_with_disjoint_values(
                full_summary,
            )
            &&& crate::disk::GenericDisk_v::addrs_closed(
                full_buffer.entries.dom(),
                summary_aus(full_summary),
            )
            &&& full_summary == full_buffer.build_branch_summary(full_roots)
        }),
        to_aus(full_roots - post_roots) == branch_deallocs,
        post_summary == full_summary.remove_keys(branch_deallocs),
        deallocs == summary_aus(full_summary.restrict(branch_deallocs)),
        post_loose.entries == full_loose.entries.restrict(
            addresses_in_aus(summary_aus(post_summary)),
        ),
    ensures ({
        let post_summary_aus = summary_aus(post_summary);
        let full_buffer = tight_sealed_branch_disk(
            full_loose,
            full_roots,
            full_summary,
        );
        let kept_domain = crate::allocation_layer::Likes_v::restrict_domain_au(
            full_buffer.entries,
            post_summary_aus,
        );
        &&& forall |root: Address| #[trigger] post_roots.contains(root) ==> {
            &&& post_summary.contains_key(root.au)
            &&& tight_branch_exists(
                loose_disk_for_summary(post_loose, post_summary[root.au]),
                root,
                post_summary[root.au],
            )
        }
        &&& tight_sealed_branch_disk(
            post_loose,
            post_roots,
            post_summary,
        ).entries == full_buffer.entries.restrict(kept_domain)
    }),
{
    let full_buffer = tight_sealed_branch_disk(
        full_loose,
        full_roots,
        full_summary,
    );
    let post_summary_aus = summary_aus(post_summary);
    let kept_domain = crate::allocation_layer::Likes_v::restrict_domain_au(
        full_buffer.entries,
        post_summary_aus,
    );
    let expected = BufferDisk {
        entries: full_buffer.entries.restrict(kept_domain),
    };

    full_buffer.build_branch_summary_remove(
        full_summary,
        full_roots,
        post_roots,
    );
    assert(post_summary == full_summary.remove_keys(
        to_aus(full_roots - post_roots),
    ));
    assert(expected.to_branch_disk().wf());
    assert(expected.sealed_branch_roots(post_roots));
    assert(post_summary == expected.build_branch_summary(post_roots));
    assert(set_addrs_disjoint_aus(post_roots)) by {
        assert(post_roots <= full_roots);
    };

    full_buffer.build_branch_summary_finite(full_roots);
    crate::betree::Utils_v::lemma_subset_finite(
        full_summary.dom(),
        post_summary.dom(),
    );
    lemma_values_finite(post_summary);

    assert forall |root: Address| #[trigger] post_roots.contains(root)
        implies {
            &&& post_summary.contains_key(root.au)
            &&& tight_branch_exists(
                loose_disk_for_summary(post_loose, post_summary[root.au]),
                root,
                post_summary[root.au],
            )
            &&& tight_branch_of(
                loose_disk_for_summary(post_loose, post_summary[root.au]),
                root,
                post_summary[root.au],
            ) == tight_branch_of(
                loose_disk_for_summary(full_loose, full_summary[root.au]),
                root,
                full_summary[root.au],
            )
        }
    by {
        expected.build_branch_summary_contains(post_roots, root);
        assert(post_summary.contains_key(root.au));
        assert(!branch_deallocs.contains(root.au));
        assert(post_summary[root.au] == full_summary[root.au]);
        let root_summary = post_summary[root.au];
        assert(post_summary.values().contains(root_summary));
        crate::betree::Utils_v::lemma_union_set_of_sets_subset(
            post_summary.values(),
            root_summary,
        );
        let full_root_loose = loose_disk_for_summary(
            full_loose,
            root_summary,
        );
        let post_root_loose = loose_disk_for_summary(
            post_loose,
            root_summary,
        );
        assert(post_root_loose == full_root_loose) by {
            assert_maps_equal!(
                post_root_loose.entries,
                full_root_loose.entries,
                addr => {
                    if addresses_in_aus(root_summary).contains(addr) {
                        assert(addresses_in_aus(post_summary_aus)
                            .contains(addr));
                    }
                }
            );
        };
        tight_branch_of_is_candidate(
            full_root_loose,
            root,
            root_summary,
        );
        let old_branch = tight_branch_of(
            full_root_loose,
            root,
            root_summary,
        );
        assert(tight_branch_in_loose_disk(
            post_root_loose,
            root,
            root_summary,
            old_branch,
        ));
        tight_branch_of_equals_candidate(
            post_root_loose,
            root,
            root_summary,
            old_branch,
        );
    };

    lemma_values_finite(full_summary);
    crate::betree::Utils_v::lemma_subset_finite(
        full_summary.dom(),
        full_summary.restrict(branch_deallocs).dom(),
    );
    lemma_values_finite(full_summary.restrict(branch_deallocs));
    summary_partition_disjoint(full_summary, branch_deallocs);
    assert(post_summary_aus.disjoint(deallocs));

    assert_maps_equal!(
        tight_sealed_branch_disk(
            post_loose,
            post_roots,
            post_summary,
        ).entries,
        expected.entries,
        addr => {
            if tight_sealed_branch_disk(
                post_loose,
                post_roots,
                post_summary,
            ).entries.contains_key(addr) {
                let root = choose |root: Address|
                    post_roots.contains(root)
                        && tight_branch_of(
                            loose_disk_for_summary(
                                post_loose,
                                post_summary[root.au],
                            ),
                            root,
                            post_summary[root.au],
                        ).disk_view.entries.contains_key(addr);
                assert(full_roots.contains(root));
                assert(full_buffer.entries.contains_key(addr));
                tight_branch_of_is_candidate(
                    loose_disk_for_summary(
                        post_loose,
                        post_summary[root.au],
                    ),
                    root,
                    post_summary[root.au],
                );
                let branch = tight_branch_of(
                    loose_disk_for_summary(
                        post_loose,
                        post_summary[root.au],
                    ),
                    root,
                    post_summary[root.au],
                );
                assert(branch.full_repr().contains(addr));
                assert(branch.get_summary().contains(addr.au));
                assert(post_summary_aus.contains(addr.au));
                assert(kept_domain.contains(addr));
            }
            if expected.entries.contains_key(addr) {
                assert(full_buffer.entries.contains_key(addr));
                assert(post_summary_aus.contains(addr.au));
                let old_root = choose |root: Address|
                    full_roots.contains(root)
                        && tight_branch_of(
                            loose_disk_for_summary(
                                full_loose,
                                full_summary[root.au],
                            ),
                            root,
                            full_summary[root.au],
                        ).disk_view.entries.contains_key(addr);
                if !post_roots.contains(old_root) {
                    assert((full_roots - post_roots).contains(old_root));
                    crate::disk::GenericDisk_v::to_aus_domain(
                        full_roots - post_roots,
                    );
                    assert(branch_deallocs.contains(old_root.au));
                    let old_summary = full_summary[old_root.au];
                    let dropped = full_summary.restrict(branch_deallocs);
                    assert(dropped.contains_key(old_root.au));
                    assert(dropped.values().contains(old_summary));
                    tight_branch_of_is_candidate(
                        loose_disk_for_summary(full_loose, old_summary),
                        old_root,
                        old_summary,
                    );
                    let old_branch = tight_branch_of(
                        loose_disk_for_summary(full_loose, old_summary),
                        old_root,
                        old_summary,
                    );
                    assert(old_branch.full_repr().contains(addr));
                    assert(old_summary.contains(addr.au));
                    crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                        dropped.values(),
                        old_summary,
                    );
                    assert(deallocs.contains(addr.au));
                    assert(false);
                }
                assert(post_roots.contains(old_root));
                assert(tight_sealed_branch_disk(
                    post_loose,
                    post_roots,
                    post_summary,
                ).entries.contains_key(addr));
            }
        }
    );
}

proof fn loaded_wip_branch_matches(
    pre: CachingDiskBranchBetree::State,
    new_disk: CachingDisk::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    access: PageAccess,
    branch_idx: int,
    output_reads: crate::implementation::CachedBranch_v::LoadedBranch,
)
    requires
        pre.refinement_inv(),
        0 <= branch_idx < pre.betree.wip_branches.len(),
        pre.betree.wip_branches[branch_idx].is_sealed(),
        crate::implementation::CachingDiskBranchBetree_v::disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        ),
        access.wf(),
        access.branch_writes.is_empty(),
        output_reads <= access.loaded_branch_reads(),
        crate::implementation::CachedBranchBetree_v::valid_loaded_sealed_branch(
            pre.betree.wip_branches[branch_idx].sealed_root(),
            pre.betree.wip_branches[branch_idx].summary(),
            output_reads,
        ),
        pre.betree.wip_branches[branch_idx].mini_allocator.all_aus()
            .disjoint(allocs),
        pre.betree.wip_branches[branch_idx].mini_allocator.all_aus()
            .disjoint(deallocs),
    ensures ({
        let cached = pre.betree.wip_branches[branch_idx];
        let model_branch = pre.wip_branch_i(branch_idx).sealed_branch();
        let loaded = loaded_sealed_branch(
            cached.sealed_root(),
            output_reads.restrict(addresses_in_aus(cached.summary())),
        );
        loaded == model_branch
    }),
{
    let cached = pre.betree.wip_branches[branch_idx];
    let allocation_branch = pre.wip_branch_i(branch_idx);
    let model_branch = allocation_branch.sealed_branch();
    let root = cached.sealed_root();
    let summary = cached.summary();
    let loaded = loaded_sealed_branch(
        root,
        output_reads.restrict(addresses_in_aus(summary)),
    );
    let witness = disk_access_for_alloc_witness(
        pre.disk,
        new_disk,
        allocs,
        deallocs,
        guard_aus,
        access.reads(),
        access.writes(),
    );

    assert(allocation_branch == pre.i().wip_branches[branch_idx]);
    assert(pre.i().wip_branches_inv());
    assert(allocation_branch.inv());
    assert(allocation_branch.is_sealed());
        assert(model_branch.valid_sealed_branch());
    assert(model_branch.tight_disk_view_with_summary());
    assert(model_branch.root == root);
    assert(model_branch.get_summary() == summary);
    assert(loaded.valid_sealed_branch());
    assert(loaded.get_summary() == summary);

    let allocated = mini_allocator_allocated_addrs(cached.mini_allocator);
    mini_allocator_allocated_addrs_subset_all_aus(cached.mini_allocator);
    assert(loaded.disk_view.agrees_with_disk(model_branch.disk_view)) by {
        assert forall |addr: Address|
            #[trigger] loaded.disk_view.entries.contains_key(addr)
                && model_branch.disk_view.entries.contains_key(addr)
            implies loaded.disk_view.entries[addr]
                == model_branch.disk_view.entries[addr]
        by {
            assert(output_reads.contains_key(addr));
            assert(output_reads.restrict(addresses_in_aus(summary))
                .contains_key(addr));
            assert(access.loaded_branch_reads().contains_key(addr));
            assert(access.branch_reads.contains_key(addr));
            assert(access.reads().contains_key(addr));
            assert(allocated.contains(addr));
            assert(addresses_in_aus(cached.mini_allocator.all_aus())
                .contains(addr));
            assert(witness.expanded.cache.contains_key(addr));
            assert(pre.disk.cache.contains_key(addr)) by {
                if !pre.disk.cache.contains_key(addr) {
                    assert((witness.expanded.cache.dom() - pre.disk.cache.dom())
                        .contains(addr));
                    assert(addresses_in_aus(allocs).contains(addr));
                    assert(false);
                }
            };
            assert(witness.expanded.cache[addr] == pre.disk.cache[addr]);
            assert(access.reads()[addr] == access.branch_reads[addr]) by {
                assert(!access.betree_reads.contains_key(addr)) by {
                    if access.betree_reads.contains_key(addr) {
                        assert(access.betree_reads.dom().disjoint(
                            access.branch_reads.dom(),
                        ));
                    }
                };
            };
            assert(access.branch_reads[addr] == pre.disk.cache[addr]);
            assert(pre.disk.visible().contains_key(addr));
            let one_read = access.branch_reads.restrict(set![addr]);
            assert(one_read <= pre.disk.cache);
            query_read_node_matches_visible(pre.disk, one_read, addr);
            assert(model_branch.disk_view.entries[addr]
                == to_branch_nodes(pre.disk.visible())[addr]);
            assert(loaded.disk_view.entries[addr]
                == output_reads[addr]);
            assert(output_reads[addr]
                == access.loaded_branch_reads()[addr]);
            assert(access.loaded_branch_reads()[addr]
                == to_branch_nodes(one_read)[addr]);
        };
    };
    agreeable_branches_same_reachable(
        loaded,
        model_branch,
        loaded.the_ranking(),
        model_branch.the_ranking(),
    );
    assert(loaded.full_repr() == model_branch.full_repr());
    assert(loaded.disk_view.entries.dom()
        == model_branch.disk_view.entries.dom());
    assert_maps_equal!(
        loaded.disk_view.entries,
        model_branch.disk_view.entries,
        addr => {}
    );
}

proof fn loaded_compactor_reads_match_semantic(
    pre: CachingDiskBranchBetree::State,
    new_disk: CachingDisk::State,
    allocs: Set<AU>,
    deallocs: Set<AU>,
    guard_aus: Set<AU>,
    access: PageAccess,
    input_idx: int,
    input_reads: crate::implementation::CachedBranch_v::LoadedBranch,
)
    requires
        pre.refinement_inv(),
        0 <= input_idx < pre.betree.compactors.len(),
        crate::implementation::CachingDiskBranchBetree_v::disk_access_for_alloc(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            access.reads(),
            access.writes(),
        ),
        access.wf(),
        access.branch_writes.is_empty(),
        input_reads <= access.loaded_branch_reads(),
        crate::implementation::CachedBranchBetree_v::valid_loaded_sealed_branches(
            pre.betree.compactors[input_idx].input_buffers.addrs.to_set(),
            pre.betree.branch_summary,
            input_reads,
        ),
        summary_aus(pre.betree.branch_summary).disjoint(allocs),
    ensures
        input_reads <= pre.semantic_sealed_branch_disk().entries,
{
    let roots = pre.betree.compactors[input_idx]
        .input_buffers.addrs.to_set();
    let witness = disk_access_for_alloc_witness(
        pre.disk,
        new_disk,
        allocs,
        deallocs,
        guard_aus,
        access.reads(),
        access.writes(),
    );
    assert forall |addr: Address| #[trigger] input_reads.contains_key(addr)
        implies pre.semantic_sealed_branch_disk().entries.contains_key(addr)
            && input_reads[addr]
                == pre.semantic_sealed_branch_disk().entries[addr]
    by {
        let root = choose |root: Address|
            roots.contains(root)
                && loaded_sealed_branch(
                    root,
                    input_reads.restrict(addresses_in_aus(
                        pre.betree.branch_summary[root.au],
                    )),
                ).disk_view.entries.contains_key(addr);
        let root_summary = pre.betree.branch_summary[root.au];
        let loaded = loaded_sealed_branch(
            root,
            input_reads.restrict(addresses_in_aus(root_summary)),
        );
        let semantic = tight_branch_of(
            loose_disk_for_summary(
                pre.visible_sealed_branch_disk(),
                root_summary,
            ),
            root,
            root_summary,
        );
        assert(pre.semantic_branch_roots().contains(root)) by {
            assert(CompactorInput::input_roots(pre.betree.compactors)
                .contains(root)) by {
                let root_sets = Seq::new(
                    pre.betree.compactors.len(),
                    |idx: int| pre.betree.compactors[idx]
                        .input_buffers.addrs.to_set(),
                );
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    root_sets,
                    input_idx,
                );
            };
        };
        assert(pre.betree.branch_summary.contains_key(root.au));
        assert(pre.tight_branches_exist());
        tight_branch_of_is_candidate(
            loose_disk_for_summary(
                pre.visible_sealed_branch_disk(),
                root_summary,
            ),
            root,
            root_summary,
        );
        assert(input_reads.restrict(addresses_in_aus(root_summary)).restrict(
            addresses_in_aus(root_summary),
        ) == input_reads.restrict(addresses_in_aus(root_summary))) by {
            assert_maps_equal!(
                input_reads.restrict(addresses_in_aus(root_summary)).restrict(
                    addresses_in_aus(root_summary),
                ),
                input_reads.restrict(addresses_in_aus(root_summary)),
                read_addr => {}
            );
        };
        assert(loaded.valid_sealed_branch());
        assert(loaded.get_summary() == root_summary);
        assert(semantic.disk_view.entries <= loose_disk_for_summary(
            pre.visible_sealed_branch_disk(),
            root_summary,
        ).entries);
        assert(loaded.disk_view.agrees_with_disk(semantic.disk_view)) by {
            assert forall |read_addr: Address|
                #[trigger] loaded.disk_view.entries.contains_key(read_addr)
                    && semantic.disk_view.entries.contains_key(read_addr)
                implies loaded.disk_view.entries[read_addr]
                    == semantic.disk_view.entries[read_addr]
            by {
                assert(input_reads.contains_key(read_addr));
                assert(access.loaded_branch_reads().contains_key(read_addr));
                assert(access.branch_reads.contains_key(read_addr));
                assert(access.reads().contains_key(read_addr));
                assert(root_summary.contains(read_addr.au));
                assert(summary_aus(pre.betree.branch_summary)
                    .contains(read_addr.au)) by {
                    assert(pre.betree.branch_summary.values()
                        .contains(root_summary));
                    pre.i().inv_branch_summary_ensures();
                    let (_, branch_likes) = pre.linked_i().transitive_likes();
                    let semantic_roots = branch_likes.dom()
                        + CompactorInput::input_roots(pre.betree.compactors);
                    pre.semantic_sealed_branch_disk()
                        .build_branch_summary_finite(semantic_roots);
                    lemma_values_finite(pre.betree.branch_summary);
                    crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                        pre.betree.branch_summary.values(),
                        root_summary,
                    );
                };
                assert(witness.expanded.cache.contains_key(read_addr));
                assert(pre.disk.cache.contains_key(read_addr)) by {
                    if !pre.disk.cache.contains_key(read_addr) {
                        assert((witness.expanded.cache.dom()
                            - pre.disk.cache.dom()).contains(read_addr));
                        assert(addresses_in_aus(allocs).contains(read_addr));
                        assert(false);
                    }
                };
                assert(witness.expanded.cache[read_addr]
                    == pre.disk.cache[read_addr]);
                assert(access.reads()[read_addr]
                    == access.branch_reads[read_addr]) by {
                    assert(!access.betree_reads.contains_key(read_addr)) by {
                        if access.betree_reads.contains_key(read_addr) {
                            assert(access.betree_reads.dom().disjoint(
                                access.branch_reads.dom(),
                            ));
                        }
                    };
                };
                assert(access.branch_reads[read_addr]
                    == pre.disk.cache[read_addr]);
                assert(loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    root_summary,
                ).entries.contains_key(read_addr));
                assert(pre.visible_sealed_branch_disk().entries
                    .contains_key(read_addr));
                assert(to_branch_nodes(pre.disk.visible())
                    .contains_key(read_addr));
                assert(pre.disk.visible().contains_key(read_addr));
                let one_read = access.branch_reads.restrict(set![read_addr]);
                assert(one_read <= pre.disk.cache);
                query_read_node_matches_visible(
                    pre.disk,
                    one_read,
                    read_addr,
                );
                assert(semantic.disk_view.entries[read_addr]
                    == loose_disk_for_summary(
                        pre.visible_sealed_branch_disk(),
                        root_summary,
                    ).entries[read_addr]);
                assert(loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    root_summary,
                ).entries[read_addr]
                    == to_branch_nodes(pre.disk.visible())[read_addr]);
                assert(loaded.disk_view.entries[read_addr]
                    == input_reads[read_addr]);
                assert(input_reads[read_addr]
                    == access.loaded_branch_reads()[read_addr]);
                assert(access.loaded_branch_reads()[read_addr]
                    == to_branch_nodes(one_read)[read_addr]);
            };
        };
        agreeable_branches_same_reachable(
            loaded,
            semantic,
            loaded.the_ranking(),
            semantic.the_ranking(),
        );
        assert(loaded.full_repr() == semantic.full_repr());
        assert(loaded.disk_view.entries.dom()
            == semantic.disk_view.entries.dom());
        assert_maps_equal!(
            loaded.disk_view.entries,
            semantic.disk_view.entries,
            read_addr => {}
        );
        assert(exists |semantic_root: Address|
            pre.semantic_branch_roots().contains(semantic_root)
                && tight_branch_of(
                    loose_disk_for_summary(
                        pre.visible_sealed_branch_disk(),
                        pre.betree.branch_summary[semantic_root.au],
                    ),
                    semantic_root,
                    pre.betree.branch_summary[semantic_root.au],
                ).disk_view.entries.contains_key(addr)) by {
            assert(pre.semantic_branch_roots().contains(root));
        };
        assert(tight_branch_addrs(
            pre.visible_sealed_branch_disk(),
            pre.semantic_branch_roots(),
            pre.betree.branch_summary,
        ).contains(addr));
        assert(loose_disk_for_summary(
            pre.visible_sealed_branch_disk(),
            root_summary,
        ).entries.contains_key(addr));
        assert(pre.visible_sealed_branch_disk().entries.contains_key(addr));
        assert(pre.visible_sealed_branch_disk().entries[addr]
            == semantic.disk_view.entries[addr]);
        assert(pre.semantic_sealed_branch_disk().entries.contains_key(addr));
        assert(pre.semantic_sealed_branch_disk().entries[addr]
            == semantic.disk_view.entries[addr]);
    };
}

proof fn compactor_receipt_matches_semantic(
    pre: CachingDiskBranchBetree::State,
    input_idx: int,
)
    requires
        pre.refinement_inv(),
        0 <= input_idx < pre.betree.compactors.len(),
        crate::implementation::CachedBranchBetree_v::valid_loaded_sealed_branches(
            pre.betree.compactors[input_idx].input_buffers.addrs.to_set(),
            pre.betree.branch_summary,
            pre.betree.compactor_receipts[input_idx],
        ),
    ensures
        pre.betree.compactor_receipts[input_idx]
            <= pre.semantic_sealed_branch_disk().entries,
{
    let roots = pre.betree.compactors[input_idx]
        .input_buffers.addrs.to_set();
    let input_reads = pre.betree.compactor_receipts[input_idx];
    let visible_view = BranchDiskView {
        entries: to_branch_nodes(pre.disk.visible()),
    };
    assert(BranchDiskView { entries: input_reads }
        .agrees_with_disk(visible_view));

    assert forall |addr: Address| #[trigger] input_reads.contains_key(addr)
        implies pre.semantic_sealed_branch_disk().entries.contains_key(addr)
            && input_reads[addr]
                == pre.semantic_sealed_branch_disk().entries[addr]
    by {
        let root = choose |root: Address|
            roots.contains(root)
                && loaded_sealed_branch(
                    root,
                    input_reads.restrict(addresses_in_aus(
                        pre.betree.branch_summary[root.au],
                    )),
                ).disk_view.entries.contains_key(addr);
        let root_summary = pre.betree.branch_summary[root.au];
        let loaded = loaded_sealed_branch(
            root,
            input_reads.restrict(addresses_in_aus(root_summary)),
        );
        let semantic = tight_branch_of(
            loose_disk_for_summary(
                pre.visible_sealed_branch_disk(),
                root_summary,
            ),
            root,
            root_summary,
        );
        assert(pre.semantic_branch_roots().contains(root)) by {
            assert(CompactorInput::input_roots(pre.betree.compactors)
                .contains(root)) by {
                let root_sets = Seq::new(
                    pre.betree.compactors.len(),
                    |idx: int| pre.betree.compactors[idx]
                        .input_buffers.addrs.to_set(),
                );
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    root_sets,
                    input_idx,
                );
            };
        };
        assert(pre.betree.branch_summary.contains_key(root.au));
        tight_branch_of_is_candidate(
            loose_disk_for_summary(
                pre.visible_sealed_branch_disk(),
                root_summary,
            ),
            root,
            root_summary,
        );
        assert(input_reads.restrict(addresses_in_aus(root_summary)).restrict(
            addresses_in_aus(root_summary),
        ) == input_reads.restrict(addresses_in_aus(root_summary))) by {
            assert_maps_equal!(
                input_reads.restrict(addresses_in_aus(root_summary)).restrict(
                    addresses_in_aus(root_summary),
                ),
                input_reads.restrict(addresses_in_aus(root_summary)),
                read_addr => {}
            );
        };
        assert(loaded.valid_sealed_branch());
        assert(loaded.get_summary() == root_summary);
        assert(semantic.disk_view.entries <= loose_disk_for_summary(
            pre.visible_sealed_branch_disk(),
            root_summary,
        ).entries);
        assert(loaded.disk_view.agrees_with_disk(semantic.disk_view)) by {
            assert forall |read_addr: Address|
                #[trigger] loaded.disk_view.entries.contains_key(read_addr)
                    && semantic.disk_view.entries.contains_key(read_addr)
                implies loaded.disk_view.entries[read_addr]
                    == semantic.disk_view.entries[read_addr]
            by {
                assert(input_reads.contains_key(read_addr));
                assert(loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    root_summary,
                ).entries.contains_key(read_addr));
                assert(pre.visible_sealed_branch_disk().entries
                    .contains_key(read_addr));
                assert(to_branch_nodes(pre.disk.visible())
                    .contains_key(read_addr));
                assert(semantic.disk_view.entries[read_addr]
                    == loose_disk_for_summary(
                        pre.visible_sealed_branch_disk(),
                        root_summary,
                    ).entries[read_addr]);
                assert(loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    root_summary,
                ).entries[read_addr]
                    == to_branch_nodes(pre.disk.visible())[read_addr]);
                assert(loaded.disk_view.entries[read_addr]
                    == input_reads[read_addr]);
            };
        };
        agreeable_branches_same_reachable(
            loaded,
            semantic,
            loaded.the_ranking(),
            semantic.the_ranking(),
        );
        assert(loaded.full_repr() == semantic.full_repr());
        assert(loaded.disk_view.entries.dom()
            == semantic.disk_view.entries.dom());
        assert_maps_equal!(
            loaded.disk_view.entries,
            semantic.disk_view.entries,
            read_addr => {}
        );
        assert(exists |semantic_root: Address|
            pre.semantic_branch_roots().contains(semantic_root)
                && tight_branch_of(
                    loose_disk_for_summary(
                        pre.visible_sealed_branch_disk(),
                        pre.betree.branch_summary[semantic_root.au],
                    ),
                    semantic_root,
                    pre.betree.branch_summary[semantic_root.au],
                ).disk_view.entries.contains_key(addr)) by {
            assert(pre.semantic_branch_roots().contains(root));
        };
        assert(tight_branch_addrs(
            pre.visible_sealed_branch_disk(),
            pre.semantic_branch_roots(),
            pre.betree.branch_summary,
        ).contains(addr));
        assert(loose_disk_for_summary(
            pre.visible_sealed_branch_disk(),
            root_summary,
        ).entries.contains_key(addr));
        assert(pre.visible_sealed_branch_disk().entries.contains_key(addr));
        assert(pre.visible_sealed_branch_disk().entries[addr]
            == semantic.disk_view.entries[addr]);
        assert(pre.semantic_sealed_branch_disk().entries.contains_key(addr));
        assert(pre.semantic_sealed_branch_disk().entries[addr]
            == semantic.disk_view.entries[addr]);
    };
}

proof fn valid_branches_same_i_same_observations(
    left: LinkedBranch<Summary>,
    right: LinkedBranch<Summary>,
    key: crate::spec::KeyType_t::Key,
)
    requires
        left.inv(),
        right.inv(),
        left.i() == right.i(),
    ensures
        left.contains_internal(left.the_ranking(), key)
            == right.contains_internal(right.the_ranking(), key),
        left.query(key) == right.query(key),
{
    LinkedBranchRefinement::contains_internal_refines(
        left,
        left.the_ranking(),
        key,
        left.contains_internal(left.the_ranking(), key),
    );
    LinkedBranchRefinement::contains_internal_refines(
        right,
        right.the_ranking(),
        key,
        right.contains_internal(right.the_ranking(), key),
    );
    LinkedBranchRefinement::query_refines(left, key, left.query(key));
    LinkedBranchRefinement::query_refines(right, key, right.query(key));
}

proof fn valid_loaded_sealed_branches_disk_wf(
    roots: Set<Address>,
    summaries: Map<AU, Summary>,
    reads: crate::implementation::CachedBranch_v::LoadedBranch,
)
    requires
        crate::implementation::CachedBranchBetree_v::valid_loaded_sealed_branches(
            roots,
            summaries,
            reads,
        ),
    ensures
        (BufferDisk { entries: reads }).to_branch_disk().wf(),
{
    let disk = BranchDiskView { entries: reads };
    assert(disk.entries_wf()) by {
        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
            implies reads[addr].wf()
        by {
            let root = choose |root: Address|
                roots.contains(root)
                    && loaded_sealed_branch(
                        root,
                        reads.restrict(addresses_in_aus(
                            summaries[root.au],
                        )),
                    ).disk_view.entries.contains_key(addr);
            let local = loaded_sealed_branch(
                root,
                reads.restrict(addresses_in_aus(summaries[root.au])),
            );
            assert(reads.restrict(addresses_in_aus(
                summaries[root.au],
            )).restrict(addresses_in_aus(summaries[root.au]))
                == reads.restrict(addresses_in_aus(summaries[root.au]))) by {
                assert_maps_equal!(
                    reads.restrict(addresses_in_aus(
                        summaries[root.au],
                    )).restrict(addresses_in_aus(summaries[root.au])),
                    reads.restrict(addresses_in_aus(summaries[root.au])),
                    local_addr => {}
                );
            };
            assert(local.valid_sealed_branch());
            assert(local.disk_view.entries[addr] == reads[addr]);
            assert(local.disk_view.entries[addr].wf());
        };
    };
    assert(disk.no_dangling_address()) by {
        assert forall |addr: Address| #[trigger] reads.contains_key(addr)
            implies disk.node_has_valid_child_address(reads[addr])
        by {
            let root = choose |root: Address|
                roots.contains(root)
                    && loaded_sealed_branch(
                        root,
                        reads.restrict(addresses_in_aus(
                            summaries[root.au],
                        )),
                    ).disk_view.entries.contains_key(addr);
            let local = loaded_sealed_branch(
                root,
                reads.restrict(addresses_in_aus(summaries[root.au])),
            );
            assert(reads.restrict(addresses_in_aus(
                summaries[root.au],
            )).restrict(addresses_in_aus(summaries[root.au]))
                == reads.restrict(addresses_in_aus(summaries[root.au]))) by {
                assert_maps_equal!(
                    reads.restrict(addresses_in_aus(
                        summaries[root.au],
                    )).restrict(addresses_in_aus(summaries[root.au])),
                    reads.restrict(addresses_in_aus(summaries[root.au])),
                    local_addr => {}
                );
            };
            assert(local.valid_sealed_branch());
            assert(local.disk_view.entries[addr] == reads[addr]);
            if reads[addr] is Index {
                assert forall |idx: int|
                    0 <= idx < reads[addr]->children.len()
                    implies disk.valid_address(
                        #[trigger] reads[addr]->children[idx],
                    ) && !(disk.entries[reads[addr]->children[idx]]
                        is Auxiliary)
                by {
                    let child = reads[addr]->children[idx];
                    assert(local.disk_view.entries.contains_key(child));
                    assert(reads.contains_key(child));
                    assert(local.disk_view.entries[child] == reads[child]);
                };
            }
        };
    };
}

proof fn loaded_root_matches_big_buffer_observations(
    roots: Set<Address>,
    summaries: Map<AU, Summary>,
    reads: crate::implementation::CachedBranch_v::LoadedBranch,
    big: BufferDisk<BranchNode>,
    root: Address,
    key: crate::spec::KeyType_t::Key,
)
    requires
        crate::implementation::CachedBranchBetree_v::valid_loaded_sealed_branches(
            roots,
            summaries,
            reads,
        ),
        roots.contains(root),
        reads <= big.entries,
        big.to_branch_disk().wf(),
        big.get_branch(root).valid_sealed_branch(),
        big.get_branch(root).get_summary() == summaries[root.au],
    ensures
        (BufferDisk { entries: reads }).buffer_contains(root, key)
            == big.buffer_contains(root, key),
        (BufferDisk { entries: reads }).query(root, key)
            == big.query(root, key),
{
    let summary = summaries[root.au];
    let local_entries = reads.restrict(addresses_in_aus(summary));
    let local = loaded_sealed_branch(root, local_entries);
    let small = BufferDisk { entries: reads };
    let small_branch = small.get_branch(root);
    let big_branch = big.get_branch(root);

    assert(local_entries.restrict(addresses_in_aus(summary))
        == local_entries) by {
        assert_maps_equal!(
            local_entries.restrict(addresses_in_aus(summary)),
            local_entries,
            addr => {}
        );
    };
    assert(local.valid_sealed_branch());
    assert(local.get_summary() == summary);
    valid_loaded_sealed_branches_disk_wf(roots, summaries, reads);
    assert(small.to_branch_disk().wf());
    assert(local.disk_view.is_sub_disk(small.to_branch_disk()));
    assert(local.disk_view.is_sub_disk(big.to_branch_disk())) by {
        assert(local.disk_view.entries <= reads);
    };
    assert(local.disk_view.entries.dom() == local.full_repr()) by {
        assert(crate::allocation_layer::Likes_v::restrict_domain_au(
            local.disk_view.entries,
            summary,
        ) == local.disk_view.entries.dom()) by {
            assert forall |addr: Address|
                #[trigger] local.disk_view.entries.contains_key(addr)
                implies summary.contains(addr.au)
            by {
                assert(addresses_in_aus(summary).contains(addr));
            };
        };
    };

    assert forall |addr: Address|
        #[trigger] (small_branch.disk_view.representation()
            - local.disk_view.representation()).contains(addr)
        implies !summary.contains(addr.au)
    by {
        if summary.contains(addr.au) {
            assert(addresses_in_aus(summary).contains(addr));
            assert(local_entries.contains_key(addr));
            assert(local.disk_view.entries.contains_key(addr));
            assert(false);
        }
    };
    local.valid_subdisk_preserves_valid_sealed_branch(
        small_branch,
        summary,
    );
    assert(small_branch.valid_sealed_branch());
    assert(small_branch.i() == local.i());

    assert(local.disk_view.agrees_with_disk(big_branch.disk_view));
    agreeable_branches_same_reachable(
        local,
        big_branch,
        local.the_ranking(),
        big_branch.the_ranking(),
    );
    assert(local.full_repr() == big_branch.full_repr());
    assert forall |addr: Address|
        #[trigger] (big_branch.disk_view.representation()
            - local.disk_view.representation()).contains(addr)
        implies !summary.contains(addr.au)
    by {
        if summary.contains(addr.au) {
            assert(crate::allocation_layer::Likes_v::restrict_domain_au(
                big_branch.disk_view.entries,
                summary,
            ).contains(addr));
            assert(big_branch.full_repr().contains(addr));
            assert(local.full_repr().contains(addr));
            assert(local.disk_view.entries.contains_key(addr));
            assert(false);
        }
    };
    local.valid_subdisk_preserves_valid_sealed_branch(
        big_branch,
        summary,
    );
    assert(big_branch.i() == local.i());
    assert(small_branch.i() == big_branch.i());
    valid_branches_same_i_same_observations(
        small_branch,
        big_branch,
        key,
    );
    assert(small.entries.contains_key(root));
    assert(big.entries.contains_key(root));
    assert(small.entries[root] == big.entries[root]);
}

proof fn buffer_disk_query_from_same(
    left: BufferDisk<BranchNode>,
    right: BufferDisk<BranchNode>,
    buffers: LinkedSeq,
    key: crate::spec::KeyType_t::Key,
    start: int,
)
    requires
        left.valid_buffers(buffers),
        right.valid_buffers(buffers),
        0 <= start <= buffers.len(),
        forall |idx: int| start <= idx < buffers.len() ==>
            left.query(#[trigger] buffers[idx], key)
                == right.query(buffers[idx], key),
    ensures
        left.query_from(buffers, key, start)
            == right.query_from(buffers, key, start),
    decreases buffers.len() - start,
{
    if start < buffers.len() {
        buffer_disk_query_from_same(
            left,
            right,
            buffers,
            key,
            start + 1,
        );
    }
}

proof fn path_target_is_acyclic<T: Buffer>(path: Path<T>)
    requires path.valid()
    ensures
        path.target().has_root(),
        path.target().acyclic(),
    decreases path.depth,
{
    if path.depth > 0 {
        path_target_is_acyclic(path.subpath());
    }
}

proof fn compact_buffer_domains_same(
    left: BufferDisk<BranchNode>,
    right: BufferDisk<BranchNode>,
    target: crate::betree::LinkedBetree_v::BetreeNode,
    start: nat,
    end: nat,
)
    requires
        target.wf(),
        start < end <= target.buffers.len(),
        ({
            let slice = target.buffers.slice(start as int, end as int);
            forall |key: crate::spec::KeyType_t::Key, idx: int|
                0 <= idx < slice.len() ==>
                    left.buffer_contains(slice[idx], key)
                        == #[trigger] right.buffer_contains(slice[idx], key)
        }),
    ensures
        forall |key: crate::spec::KeyType_t::Key|
            left.valid_compact_key_domain(target, start, end, key)
                <==> #[trigger] right.valid_compact_key_domain(
                    target, start, end, key,
                ),
{
    let slice = target.buffers.slice(start as int, end as int);
    assert forall |key: crate::spec::KeyType_t::Key|
        left.valid_compact_key_domain(target, start, end, key)
            <==> #[trigger] right.valid_compact_key_domain(
                target, start, end, key,
            )
    by {
        let offsets = target.make_offset_map().decrement(start);
        assert forall |idx: int|
            left.key_in_buffer_filtered(slice, offsets, 0, key, idx)
                <==> right.key_in_buffer_filtered(
                    slice, offsets, 0, key, idx,
                )
        by {
            if left.key_in_buffer_filtered(slice, offsets, 0, key, idx)
                || right.key_in_buffer_filtered(slice, offsets, 0, key, idx)
            {
                assert(0 <= idx < slice.len());
            }
        };
        if left.valid_compact_key_domain(target, start, end, key) {
            let idx = choose |idx: int|
                #[trigger] left.key_in_buffer_filtered(
                    slice, offsets, 0, key, idx,
                );
            assert(right.key_in_buffer_filtered(
                slice, offsets, 0, key, idx,
            ));
        }
        if right.valid_compact_key_domain(target, start, end, key) {
            let idx = choose |idx: int|
                #[trigger] right.key_in_buffer_filtered(
                    slice, offsets, 0, key, idx,
                );
            assert(left.key_in_buffer_filtered(
                slice, offsets, 0, key, idx,
            ));
        }
    };
}

proof fn compact_buffer_values_same(
    left: BufferDisk<BranchNode>,
    right: BufferDisk<BranchNode>,
    target: crate::betree::LinkedBetree_v::BetreeNode,
    start: nat,
    end: nat,
)
    requires
        target.wf(),
        start < end <= target.buffers.len(),
        ({
            let slice = target.buffers.slice(start as int, end as int);
            &&& left.valid_buffers(slice)
            &&& right.valid_buffers(slice)
            &&& forall |key: crate::spec::KeyType_t::Key, idx: int|
                0 <= idx < slice.len() ==>
                    left.query(slice[idx], key)
                        == #[trigger] right.query(slice[idx], key)
        }),
    ensures
        forall |key: crate::spec::KeyType_t::Key|
            left.valid_compact_key_domain(target, start, end, key)
            ==> left.compact_key_value(target, start, end, key)
                == #[trigger] right.compact_key_value(
                    target, start, end, key,
                ),
{
    let slice = target.buffers.slice(start as int, end as int);
    assert forall |key: crate::spec::KeyType_t::Key|
        left.valid_compact_key_domain(target, start, end, key)
        implies left.compact_key_value(target, start, end, key)
            == #[trigger] right.compact_key_value(target, start, end, key)
    by {
        let from = if target.flushed_ofs(key) <= start {
            0
        } else {
            target.flushed_ofs(key) - start
        };
        buffer_disk_query_from_same(
            left,
            right,
            slice,
            key,
            from as int,
        );
    };
}

proof fn compact_input_root_observations(
    pre: CachingDiskBranchBetree::State,
    input_idx: int,
    path: Path<BranchNode>,
    start: nat,
    end: nat,
    input_reads: crate::implementation::CachedBranch_v::LoadedBranch,
)
    requires
        pre.refinement_inv(),
        0 <= input_idx < pre.betree.compactors.len(),
        path.valid(),
        pre.betree.compactors[input_idx].input_buffers
            == path.target().root().buffers.slice(start as int, end as int),
        start < end <= path.target().root().buffers.len(),
        ({
            let roots = pre.betree.compactors[input_idx]
                .input_buffers.addrs.to_set();
            &&& crate::implementation::CachedBranchBetree_v::valid_loaded_sealed_branches(
                roots,
                pre.betree.branch_summary,
                input_reads,
            )
            &&& input_reads <= pre.semantic_sealed_branch_disk().entries
        }),
    ensures ({
        let input_buffer = BufferDisk { entries: input_reads };
        let compact_slice = path.target().root().buffers.slice(
            start as int,
            end as int,
        );
        forall |key: crate::spec::KeyType_t::Key, idx: int|
            0 <= idx < compact_slice.len()
            ==> {
                &&& input_buffer.buffer_contains(compact_slice[idx], key)
                    == #[trigger] pre.linked_i().buffer_dv.buffer_contains(
                        compact_slice[idx],
                        key,
                    )
                &&& input_buffer.query(compact_slice[idx], key)
                    == pre.linked_i().buffer_dv.query(
                        compact_slice[idx],
                        key,
                    )
            }
    }),
{
    pre.linked_i_tight_tree_facts();
    let pre_linked = pre.linked_i();
    let pre_tree = pre.tight_betree_i();
    let compact_slice = path.target().root().buffers.slice(
        start as int,
        end as int,
    );
    let roots = compact_slice.addrs.to_set();
    let input_buffer = BufferDisk { entries: input_reads };
    assert(roots == pre.betree.compactors[input_idx]
        .input_buffers.addrs.to_set());
    valid_loaded_sealed_branches_disk_wf(
        roots,
        pre.betree.branch_summary,
        input_reads,
    );
    pre.i().inv_implies_wf_branch_dv();
    pre.i().inv_branch_summary_ensures();

    let semantic_roots = pre.semantic_branch_roots();
    let (_, branch_likes) = pre_linked.transitive_likes();
    pre_linked.tree_likes_domain(pre_linked.the_ranking());
    pre_linked.buffer_likes_domain(
        pre_linked.tree_likes(pre_linked.the_ranking()),
    );
    tight_betree_of_is_candidate(
        pre.betree.root,
        pre.visible_betree_entries(),
    );
    assert(pre_linked.dv == pre_tree.dv);
    assert(pre_linked.dv.entries.dom()
        == pre_linked.reachable_betree_addrs());
    assert(pre_tree.dv.entries.dom()
        == pre_tree.reachable_betree_addrs());
    assert(pre_linked.reachable_betree_addrs()
        == pre_tree.reachable_betree_addrs());
    pre_linked.same_reachable_betree_addrs_implies_same_buffer_addrs(
        pre_tree,
    );
    assert(branch_likes.dom() == pre_tree.reachable_buffer_addrs());
    assert(semantic_roots == branch_likes.dom()
        + CompactorInput::input_roots(pre.i().compactors));
    assert(pre_linked.buffer_dv.sealed_branch_roots(semantic_roots));
    assert(set_addrs_disjoint_aus(semantic_roots));

    assert forall |key: crate::spec::KeyType_t::Key, idx: int|
        0 <= idx < compact_slice.len()
        implies {
            &&& input_buffer.buffer_contains(compact_slice[idx], key)
                == #[trigger] pre_linked.buffer_dv.buffer_contains(
                    compact_slice[idx],
                    key,
                )
            &&& input_buffer.query(compact_slice[idx], key)
                == pre_linked.buffer_dv.query(compact_slice[idx], key)
        }
    by {
        let root = compact_slice[idx];
        assert(roots.contains(root));
        assert(CompactorInput::input_roots(pre.i().compactors)
            .contains(root)) by {
            let root_sets = Seq::new(
                pre.i().compactors.len(),
                |i: int| pre.i().compactors[i]
                    .input_buffers.addrs.to_set(),
            );
            crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                root_sets,
                input_idx,
            );
        };
        assert(semantic_roots.contains(root));
        pre_linked.buffer_dv.sealed_branch_roots_contains(
            semantic_roots,
            root,
        );
        pre_linked.buffer_dv.build_branch_summary_contains(
            semantic_roots,
            root,
        );
        assert(pre_linked.buffer_dv.get_branch(root).get_summary()
            == pre.betree.branch_summary[root.au]);
        loaded_root_matches_big_buffer_observations(
            roots,
            pre.betree.branch_summary,
            input_reads,
            pre_linked.buffer_dv,
            root,
            key,
        );
    };
}

proof fn compact_input_reads_match_semantic(
    pre: CachingDiskBranchBetree::State,
    input_idx: int,
    path: Path<BranchNode>,
    start: nat,
    end: nat,
    input_reads: crate::implementation::CachedBranch_v::LoadedBranch,
)
    requires
        pre.refinement_inv(),
        0 <= input_idx < pre.betree.compactors.len(),
        path.valid(),
        pre.betree.compactors[input_idx].input_buffers
            == path.target().root().buffers.slice(start as int, end as int),
        start < end <= path.target().root().buffers.len(),
        ({
            let roots = pre.betree.compactors[input_idx]
                .input_buffers.addrs.to_set();
            &&& crate::implementation::CachedBranchBetree_v::valid_loaded_sealed_branches(
                roots,
                pre.betree.branch_summary,
                input_reads,
            )
            &&& input_reads <= pre.semantic_sealed_branch_disk().entries
        }),
    ensures ({
        let input_buffer = BufferDisk { entries: input_reads };
        let target = path.target().root();
        &&& forall |key: crate::spec::KeyType_t::Key|
            input_buffer.valid_compact_key_domain(target, start, end, key)
                <==> #[trigger] pre.linked_i().buffer_dv
                    .valid_compact_key_domain(target, start, end, key)
        &&& forall |key: crate::spec::KeyType_t::Key|
            input_buffer.valid_compact_key_domain(target, start, end, key)
            ==> input_buffer.compact_key_value(target, start, end, key)
                == #[trigger] pre.linked_i().buffer_dv.compact_key_value(
                    target,
                    start,
                    end,
                    key,
                )
    }),
{
    compact_input_root_observations(
        pre,
        input_idx,
        path,
        start,
        end,
        input_reads,
    );
    let input_buffer = BufferDisk { entries: input_reads };
    let pre_buffer = pre.linked_i().buffer_dv;
    let target = path.target().root();
    let slice = target.buffers.slice(start as int, end as int);
    path_target_is_acyclic(path);
    assert(path.target().wf());
    assert(path.target().dv.entries_wf());
    assert(target.wf());
    assert(input_buffer.valid_buffers(slice));
    assert(pre_buffer.valid_buffers(slice));
    compact_buffer_domains_same(
        input_buffer,
        pre_buffer,
        target,
        start,
        end,
    );
    assert forall |key: crate::spec::KeyType_t::Key, idx: int|
        0 <= idx < slice.len()
        implies input_buffer.query(slice[idx], key)
            == #[trigger] pre_buffer.query(slice[idx], key)
    by {
        assert(input_buffer.buffer_contains(slice[idx], key)
            == pre_buffer.buffer_contains(slice[idx], key));
    };
    compact_buffer_values_same(
        input_buffer,
        pre_buffer,
        target,
        start,
        end,
    );
}

proof fn sealed_output_branch_observations_preserved(
    pre: CachingDiskBranchBetree::State,
    new_branch: LinkedBranch<Summary>,
)
    requires
        pre.refinement_inv(),
        new_branch.valid_sealed_branch(),
        new_branch.tight_disk_view_with_summary(),
        summary_aus(pre.betree.branch_summary).disjoint(
            new_branch.get_summary(),
        ),
    ensures ({
        let full = BufferDisk {
            entries: pre.linked_i().buffer_dv.entries.union_prefer_right(
                new_branch.disk_view.entries,
            ),
        };
        let local = BufferDisk { entries: new_branch.disk_view.entries };
        &&& forall |key: crate::spec::KeyType_t::Key|
            new_branch.root().linked_contains(full, new_branch.root, key)
                == #[trigger] new_branch.root().linked_contains(
                    local,
                    new_branch.root,
                    key,
                )
        &&& forall |key: crate::spec::KeyType_t::Key|
            new_branch.root().linked_query(full, new_branch.root, key)
                == #[trigger] new_branch.root().linked_query(
                    local,
                    new_branch.root,
                    key,
                )
    }),
{
    let pre_buffer = pre.linked_i().buffer_dv;
    let full = BufferDisk {
        entries: pre_buffer.entries.union_prefer_right(
            new_branch.disk_view.entries,
        ),
    };
    let local = BufferDisk { entries: new_branch.disk_view.entries };
    pre.i().inv_implies_wf_branch_dv();
    assert(full.to_branch_disk().wf()) by {
        assert forall |addr: Address| #[trigger] full.entries.contains_key(addr)
            implies new_branch.full_repr().contains(addr)
                || pre_buffer.entries.contains_key(addr)
        by {
            if new_branch.disk_view.entries.contains_key(addr) {
                assert(new_branch.disk_view.representation().contains(addr));
                assert(new_branch.full_repr()
                    == new_branch.disk_view.representation());
            }
        };
    };
    let full_branch = full.get_branch(new_branch.root);
    assert(new_branch.disk_view.is_sub_disk(full_branch.disk_view));
    assert forall |addr: Address|
        #[trigger] (full_branch.disk_view.representation()
            - new_branch.disk_view.representation()).contains(addr)
        implies !new_branch.get_summary().contains(addr.au)
    by {
        if new_branch.get_summary().contains(addr.au) {
            assert(pre_buffer.entries.contains_key(addr));
            assert(summary_aus(pre.i().branch_summary).contains(addr.au));
            assert(false);
        }
    };
    new_branch.valid_subdisk_preserves_valid_sealed_branch(
        full_branch,
        new_branch.get_summary(),
    );
    assert forall |key: crate::spec::KeyType_t::Key| true
        implies {
            &&& new_branch.root().linked_contains(full, new_branch.root, key)
                == #[trigger] new_branch.root().linked_contains(
                    local, new_branch.root, key,
                )
            &&& new_branch.root().linked_query(full, new_branch.root, key)
                == new_branch.root().linked_query(
                    local, new_branch.root, key,
                )
        }
    by {
        valid_branches_same_i_same_observations(
            new_branch,
            full_branch,
            key,
        );
        assert(local.get_branch(new_branch.root) == new_branch);
        assert(full.get_branch(new_branch.root) == full_branch);
        assert(new_branch.root().linked_contains(
            local,
            new_branch.root,
            key,
        ) == new_branch.contains_internal(
            new_branch.the_ranking(),
            key,
        ));
        assert(new_branch.root().linked_contains(
            full,
            new_branch.root,
            key,
        ) == full_branch.contains_internal(
            full_branch.the_ranking(),
            key,
        ));
        assert(new_branch.root().linked_query(
            local,
            new_branch.root,
            key,
        ) == new_branch.query(key));
        assert(new_branch.root().linked_query(
            full,
            new_branch.root,
            key,
        ) == full_branch.query(key));
    };
    assert forall |key: crate::spec::KeyType_t::Key|
        new_branch.root().linked_contains(full, new_branch.root, key)
            == #[trigger] new_branch.root().linked_contains(
                local, new_branch.root, key,
            )
    by {};
    assert forall |key: crate::spec::KeyType_t::Key|
        new_branch.root().linked_query(full, new_branch.root, key)
            == #[trigger] new_branch.root().linked_query(
                local, new_branch.root, key,
            )
    by {
        valid_branches_same_i_same_observations(
            new_branch,
            full_branch,
            key,
        );
        assert(new_branch.root().linked_query(
            local,
            new_branch.root,
            key,
        ) == new_branch.query(key));
        assert(new_branch.root().linked_query(
            full,
            new_branch.root,
            key,
        ) == full_branch.query(key));
    };
}

proof fn compact_reads_establish_can_compact(
    pre: CachingDiskBranchBetree::State,
    input_idx: int,
    path: Path<BranchNode>,
    start: nat,
    end: nat,
    new_addrs: TwoAddrs,
    input_reads: crate::implementation::CachedBranch_v::LoadedBranch,
    output_reads: crate::implementation::CachedBranch_v::LoadedBranch,
    new_branch: LinkedBranch<Summary>,
)
    requires
        pre.refinement_inv(),
        0 <= input_idx < pre.betree.compactors.len(),
        path.valid(),
        path.linked == pre.linked_i(),
        pre.betree.compactors[input_idx].input_buffers
            == path.target().root().buffers.slice(start as int, end as int),
        start < end <= path.target().root().buffers.len(),
        ({
            let input_roots = pre.betree.compactors[input_idx]
                .input_buffers.addrs.to_set();
            &&& crate::implementation::CachedBranchBetree_v::valid_loaded_sealed_branches(
                input_roots,
                pre.betree.branch_summary,
                input_reads,
            )
            &&& input_reads <= pre.semantic_sealed_branch_disk().entries
        }),
        new_branch.valid_sealed_branch(),
        new_branch.tight_disk_view_with_summary(),
        new_addrs.addr2 == new_branch.root,
        output_reads == new_branch.disk_view.entries,
        summary_aus(pre.betree.branch_summary).disjoint(
            new_branch.get_summary(),
        ),
        ({
            let input_buffer = BufferDisk { entries: input_reads };
            let output_buffer = BufferDisk { entries: output_reads };
            &&& forall |key: crate::spec::KeyType_t::Key|
                new_branch.root().linked_contains(
                    output_buffer,
                    new_branch.root,
                    key,
                ) <==> #[trigger] input_buffer.valid_compact_key_domain(
                    path.target().root(),
                    start,
                    end,
                    key,
                )
            &&& forall |key: crate::spec::KeyType_t::Key|
                new_branch.root().linked_contains(
                    output_buffer,
                    new_branch.root,
                    key,
                ) ==> #[trigger] new_branch.root().linked_query(
                    output_buffer,
                    new_branch.root,
                    key,
                ) == input_buffer.compact_key_value(
                    path.target().root(),
                    start,
                    end,
                    key,
                )
        }),
    ensures ({
        let full_buffer = BufferDisk {
            entries: pre.linked_i().buffer_dv.entries.union_prefer_right(
                new_branch.disk_view.entries,
            ),
        };
        path.target().can_compact(
            start,
            end,
            new_branch.root(),
            full_buffer,
            new_addrs,
        )
    }),
{
    compact_input_reads_match_semantic(
        pre,
        input_idx,
        path,
        start,
        end,
        input_reads,
    );
    sealed_output_branch_observations_preserved(pre, new_branch);
    let input_buffer = BufferDisk { entries: input_reads };
    let output_buffer = BufferDisk { entries: output_reads };
    let full_buffer = BufferDisk {
        entries: pre.linked_i().buffer_dv.entries.union_prefer_right(
            new_branch.disk_view.entries,
        ),
    };
    let target = path.target().root();
    path_target_is_acyclic(path);
    path.target_ensures();
    assert(path.target().wf());
    assert(path.target().has_root());
    assert(path.target().buffer_dv == pre.linked_i().buffer_dv);
    assert(new_addrs.addr2 == new_branch.root);
    assert(target.wf());
    assert forall |key: crate::spec::KeyType_t::Key|
        new_branch.root().linked_contains(
            full_buffer,
            new_branch.root,
            key,
        ) <==> #[trigger] pre.linked_i().buffer_dv
            .valid_compact_key_domain(target, start, end, key)
    by {
        assert(new_branch.root().linked_contains(
            full_buffer,
            new_branch.root,
            key,
        ) == new_branch.root().linked_contains(
            output_buffer,
            new_branch.root,
            key,
        ));
        assert(input_buffer.valid_compact_key_domain(
            target, start, end, key,
        ) <==> pre.linked_i().buffer_dv.valid_compact_key_domain(
            target, start, end, key,
        ));
    };
    assert forall |key: crate::spec::KeyType_t::Key|
        new_branch.root().linked_contains(
            full_buffer,
            new_branch.root,
            key,
        ) implies #[trigger] new_branch.root().linked_query(
            full_buffer,
            new_branch.root,
            key,
        ) == pre.linked_i().buffer_dv.compact_key_value(
            target, start, end, key,
        )
    by {
        assert(new_branch.root().linked_contains(
            output_buffer,
            new_branch.root,
            key,
        ));
        assert(new_branch.root().linked_query(
            full_buffer,
            new_branch.root,
            key,
        ) == new_branch.root().linked_query(
            output_buffer,
            new_branch.root,
            key,
        ));
        assert(input_buffer.valid_compact_key_domain(
            target, start, end, key,
        ));
        assert(input_buffer.compact_key_value(target, start, end, key)
            == pre.linked_i().buffer_dv.compact_key_value(
                target, start, end, key,
            ));
    };
    assert(path.target().compact_buffer_valid_domain(
        start,
        end,
        new_branch.root(),
        full_buffer,
        new_addrs.addr2,
    ));
    assert(path.target().compact_buffer_valid_range(
        start,
        end,
        new_branch.root(),
        full_buffer,
        new_addrs.addr2,
    ));
    assert(path.target().can_compact(
        start,
        end,
        new_branch.root(),
        full_buffer,
        new_addrs,
    ));
}

proof fn semantic_sealed_branch_disk_prune(
    pre: CachingDiskBranchBetree::State,
    post: CachingDiskBranchBetree::State,
    pre_roots: Set<Address>,
    post_roots: Set<Address>,
    branch_deallocs: Set<AU>,
    deallocs: Set<AU>,
)
    requires
        pre.refinement_inv(),
        pre_roots == pre.semantic_branch_roots(),
        post_roots == post.semantic_branch_roots(),
        post_roots <= pre_roots,
        to_aus(pre_roots - post_roots) == branch_deallocs,
        post.betree.branch_summary
            == pre.betree.branch_summary.remove_keys(branch_deallocs),
        deallocs == summary_aus(
            pre.betree.branch_summary.restrict(branch_deallocs),
        ),
        post.visible_sealed_branch_disk().entries
            == pre.visible_sealed_branch_disk().entries.restrict(
                addresses_in_aus(summary_aus(post.betree.branch_summary)),
            ),
    ensures ({
        let post_summary_aus = summary_aus(post.betree.branch_summary);
        let kept_domain = crate::allocation_layer::Likes_v::restrict_domain_au(
            pre.semantic_sealed_branch_disk().entries,
            post_summary_aus,
        );
        let expected = BufferDisk {
            entries: pre.semantic_sealed_branch_disk().entries.restrict(
                kept_domain,
            ),
        };
        &&& post.tight_branches_exist()
        &&& post.semantic_sealed_branch_disk() == expected
    }),
{
    let pre_buffer = pre.semantic_sealed_branch_disk();
    let post_summary = post.betree.branch_summary;
    let post_summary_aus = summary_aus(post_summary);
    let kept_domain = crate::allocation_layer::Likes_v::restrict_domain_au(
        pre_buffer.entries,
        post_summary_aus,
    );
    let expected = BufferDisk {
        entries: pre_buffer.entries.restrict(kept_domain),
    };

    pre.i().inv_branch_summary_ensures();
    pre.i().inv_implies_wf_branch_dv();
    assert(pre.i().inv());
    let pre_linked = pre.linked_i();
    let (pre_tree_likes, pre_branch_likes) = pre_linked.transitive_likes();
    let model_pre_roots = pre_branch_likes.dom()
        + CompactorInput::input_roots(pre.i().compactors);
    pre.linked_i_tight_tree_facts();
    pre_linked.tree_likes_domain(pre_linked.the_ranking());
    pre_linked.buffer_likes_domain(pre_tree_likes);
    assert(pre_linked.dv == pre.tight_betree_i().dv);
    assert(pre_linked.reachable_betree_addrs()
        == pre.tight_betree_i().reachable_betree_addrs()) by {
        assert(pre_linked.dv.entries.dom()
            == pre_linked.reachable_betree_addrs());
        tight_betree_of_is_candidate(
            pre.betree.root,
            pre.visible_betree_entries(),
        );
        assert(pre.tight_betree_i().dv.entries.dom()
            == pre.tight_betree_i().reachable_betree_addrs());
    };
    pre_linked.same_reachable_betree_addrs_implies_same_buffer_addrs(
        pre.tight_betree_i(),
    );
    assert(pre_branch_likes.dom()
        == pre.tight_betree_i().reachable_buffer_addrs());
    assert(model_pre_roots == pre.semantic_branch_roots());
    assert(pre_roots == model_pre_roots);
    assert(pre.i().betree.linked.buffer_dv == pre_buffer);
    assert(pre_roots == pre.semantic_branch_roots());
    assert(pre_roots.finite());
    assert(set_addrs_disjoint_aus(pre_roots));
    assert(pre_buffer.to_branch_disk().wf());
    assert(pre_buffer.sealed_branch_roots(pre_roots));
    assert(crate::allocation_layer::AllocationBranchBetree_v::map_with_disjoint_values(
        pre.betree.branch_summary,
    ));
    assert(crate::disk::GenericDisk_v::addrs_closed(
        pre_buffer.entries.dom(),
        summary_aus(pre.betree.branch_summary),
    ));
    assert(pre.betree.branch_summary
        == pre_buffer.build_branch_summary(pre_roots));
    pre_buffer.build_branch_summary_remove(
        pre.betree.branch_summary,
        pre_roots,
        post_roots,
    );
    assert(post_summary == pre.betree.branch_summary.remove_keys(
        to_aus(pre_roots - post_roots),
    ));
    assert(expected.to_branch_disk().wf());
    assert(expected.sealed_branch_roots(post_roots));
    assert(post_summary == expected.build_branch_summary(post_roots));
    assert(set_addrs_disjoint_aus(post_roots)) by {
        assert(post_roots <= pre_roots);
    };

    pre_buffer.build_branch_summary_finite(pre_roots);
    crate::betree::Utils_v::lemma_subset_finite(
        pre.betree.branch_summary.dom(),
        post_summary.dom(),
    );
    lemma_values_finite(post_summary);

    assert forall |root: Address| #[trigger] post_roots.contains(root)
        implies {
            &&& post_summary.contains_key(root.au)
            &&& tight_branch_exists(
                loose_disk_for_summary(
                    post.visible_sealed_branch_disk(),
                    post_summary[root.au],
                ),
                root,
                post_summary[root.au],
            )
            &&& tight_branch_of(
                loose_disk_for_summary(
                    post.visible_sealed_branch_disk(),
                    post_summary[root.au],
                ),
                root,
                post_summary[root.au],
            ) == tight_branch_of(
                loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    pre.betree.branch_summary[root.au],
                ),
                root,
                pre.betree.branch_summary[root.au],
            )
        }
    by {
        expected.build_branch_summary_contains(post_roots, root);
        assert(post_summary.contains_key(root.au));
        assert(!branch_deallocs.contains(root.au));
        assert(post_summary[root.au]
            == pre.betree.branch_summary[root.au]);
        let root_summary = post_summary[root.au];
        assert(post_summary.values().contains(root_summary));
        crate::betree::Utils_v::lemma_union_set_of_sets_subset(
            post_summary.values(),
            root_summary,
        );
        let pre_root_loose = loose_disk_for_summary(
            pre.visible_sealed_branch_disk(),
            root_summary,
        );
        let post_root_loose = loose_disk_for_summary(
            post.visible_sealed_branch_disk(),
            root_summary,
        );
        assert(post_root_loose == pre_root_loose) by {
            assert_maps_equal!(
                post_root_loose.entries,
                pre_root_loose.entries,
                addr => {
                    if addresses_in_aus(root_summary).contains(addr) {
                        assert(addresses_in_aus(post_summary_aus).contains(addr));
                    }
                }
            );
        };
        assert(pre.tight_branches_exist());
        assert(pre_roots.contains(root));
        tight_branch_of_is_candidate(pre_root_loose, root, root_summary);
        let old_branch = tight_branch_of(
            pre_root_loose,
            root,
            root_summary,
        );
        assert(tight_branch_in_loose_disk(
            post_root_loose,
            root,
            root_summary,
            old_branch,
        ));
        tight_branch_of_equals_candidate(
            post_root_loose,
            root,
            root_summary,
            old_branch,
        );
    };
    assert(post.tight_branches_exist());

    lemma_values_finite(pre.betree.branch_summary);
    crate::betree::Utils_v::lemma_subset_finite(
        pre.betree.branch_summary.dom(),
        pre.betree.branch_summary.restrict(branch_deallocs).dom(),
    );
    lemma_values_finite(
        pre.betree.branch_summary.restrict(branch_deallocs),
    );
    summary_partition_disjoint(
        pre.betree.branch_summary,
        branch_deallocs,
    );
    assert(post_summary_aus.disjoint(deallocs));

    assert_maps_equal!(
        post.semantic_sealed_branch_disk().entries,
        expected.entries,
        addr => {
            if post.semantic_sealed_branch_disk().entries.contains_key(addr) {
                let root = choose |root: Address|
                    post_roots.contains(root)
                        && tight_branch_of(
                            loose_disk_for_summary(
                                post.visible_sealed_branch_disk(),
                                post_summary[root.au],
                            ),
                            root,
                            post_summary[root.au],
                        ).disk_view.entries.contains_key(addr);
                assert(pre_roots.contains(root));
                assert(pre.semantic_sealed_branch_disk().entries
                    .contains_key(addr));
                tight_branch_of_is_candidate(
                    loose_disk_for_summary(
                        post.visible_sealed_branch_disk(),
                        post_summary[root.au],
                    ),
                    root,
                    post_summary[root.au],
                );
                let branch = tight_branch_of(
                    loose_disk_for_summary(
                        post.visible_sealed_branch_disk(),
                        post_summary[root.au],
                    ),
                    root,
                    post_summary[root.au],
                );
                assert(branch.full_repr().contains(addr));
                assert(branch.get_summary().contains(addr.au));
                assert(post_summary_aus.contains(addr.au));
                assert(kept_domain.contains(addr));
            }
            if expected.entries.contains_key(addr) {
                assert(pre.semantic_sealed_branch_disk().entries
                    .contains_key(addr));
                assert(post_summary_aus.contains(addr.au));
                let old_root = choose |root: Address|
                    pre_roots.contains(root)
                        && tight_branch_of(
                            loose_disk_for_summary(
                                pre.visible_sealed_branch_disk(),
                                pre.betree.branch_summary[root.au],
                            ),
                            root,
                            pre.betree.branch_summary[root.au],
                        ).disk_view.entries.contains_key(addr);
                if !post_roots.contains(old_root) {
                    assert((pre_roots - post_roots).contains(old_root));
                    crate::disk::GenericDisk_v::to_aus_domain(
                        pre_roots - post_roots,
                    );
                    assert(branch_deallocs.contains(old_root.au));
                    let old_summary = pre.betree.branch_summary[old_root.au];
                    let dropped = pre.betree.branch_summary.restrict(
                        branch_deallocs,
                    );
                    assert(dropped.contains_key(old_root.au));
                    assert(dropped.values().contains(old_summary));
                    tight_branch_of_is_candidate(
                        loose_disk_for_summary(
                            pre.visible_sealed_branch_disk(),
                            old_summary,
                        ),
                        old_root,
                        old_summary,
                    );
                    let old_branch = tight_branch_of(
                        loose_disk_for_summary(
                            pre.visible_sealed_branch_disk(),
                            old_summary,
                        ),
                        old_root,
                        old_summary,
                    );
                    assert(old_branch.full_repr().contains(addr));
                    assert(old_summary.contains(addr.au));
                    crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                        dropped.values(),
                        old_summary,
                    );
                    assert(deallocs.contains(addr.au));
                    assert(false);
                }
                assert(post_roots.contains(old_root));
                assert(post.semantic_sealed_branch_disk().entries
                    .contains_key(addr));
            }
        }
    );
}

proof fn reachable_betree_addrs_closed_under_children(
    tree: LinkedBetree<BranchNode>,
    ranking: crate::disk::GenericDisk_v::Ranking,
    addr: Address,
)
    requires
        tree.valid_ranking(ranking),
        tree.reachable_betree_addrs_using_ranking(ranking).contains(addr),
    ensures
        forall |idx: nat|
            tree.dv.entries[addr].valid_child_index(idx)
                && tree.dv.entries[addr].children[idx as int] is Some
            ==> tree.reachable_betree_addrs_using_ranking(ranking).contains(
                tree.dv.entries[addr].children[idx as int].unwrap(),
            ),
    decreases tree.get_rank(ranking),
{
    tree.reachable_betree_addrs_using_ranking_closed(ranking);
    if Some(addr) == tree.root {
        assert(tree.has_root());
        tree.reachable_betree_addrs_using_ranking_recur_lemma(ranking, 0);
        assert forall |idx: nat|
            tree.dv.entries[addr].valid_child_index(idx)
                && tree.dv.entries[addr].children[idx as int] is Some
            implies tree.reachable_betree_addrs_using_ranking(ranking).contains(
                tree.dv.entries[addr].children[idx as int].unwrap(),
            )
        by {
            let child = tree.child_at_idx(idx);
            assert(child.valid_ranking(ranking));
            child.reachable_betree_addrs_using_ranking_closed(ranking);
            assert(child.has_root());
            assert(child.root.unwrap()
                == tree.dv.entries[addr].children[idx as int].unwrap());
            assert(child.reachable_betree_addrs_using_ranking(ranking)
                <= tree.reachable_betree_addrs_using_ranking_recur(
                    ranking, 0,
                ));
        };
    } else {
        assert(tree.exists_child_subtree_contains_addr(ranking, addr, 0));
        let child_idx = tree.child_containing_reachable_addr(
            ranking,
            addr,
            0,
        );
        let child = tree.child_at_idx(child_idx);
        assert(child.valid_ranking(ranking));
        assert(child.reachable_betree_addrs_using_ranking(ranking)
            .contains(addr));
        assert(tree.root().valid_child_index(child_idx));
        assert(child.get_rank(ranking) < tree.get_rank(ranking));
        reachable_betree_addrs_closed_under_children(
            child,
            ranking,
            addr,
        );
        tree.reachable_betree_addrs_using_ranking_recur_lemma(ranking, 0);
        assert(child.reachable_betree_addrs_using_ranking(ranking)
            <= tree.reachable_betree_addrs_using_ranking_recur(ranking, 0));
        assert forall |idx: nat|
            tree.dv.entries[addr].valid_child_index(idx)
                && tree.dv.entries[addr].children[idx as int] is Some
            implies tree.reachable_betree_addrs_using_ranking(ranking).contains(
                tree.dv.entries[addr].children[idx as int].unwrap(),
            )
        by {
            assert(child.dv == tree.dv);
            assert(child.dv.entries[addr] == tree.dv.entries[addr]);
            assert(child.reachable_betree_addrs_using_ranking(ranking).contains(
                child.dv.entries[addr].children[idx as int].unwrap(),
            ));
        };
    }
}

pub open spec fn reachable_tight_betree(
    tree: LinkedBetree<BranchNode>,
) -> LinkedBetree<BranchNode>
    recommends tree.acyclic()
{
    LinkedBetree {
        root: tree.root,
        dv: BetreeDiskView {
            entries: tree.dv.entries.restrict(
                tree.reachable_betree_addrs(),
            ),
        },
        buffer_dv: BufferDisk::<BranchNode>::empty_disk(),
    }
}

proof fn reachable_tight_betree_facts(
    tree: LinkedBetree<BranchNode>,
)
    requires tree.acyclic()
    ensures ({
        let candidate = reachable_tight_betree(tree);
        &&& candidate.root == tree.root
        &&& candidate.dv.is_sub_disk(tree.dv)
        &&& candidate.buffer_dv == BufferDisk::<BranchNode>::empty_disk()
        &&& candidate.acyclic()
        &&& candidate.reachable_betree_addrs()
            == tree.reachable_betree_addrs()
        &&& candidate.dv.entries.dom()
            == candidate.reachable_betree_addrs()
    }),
{
    let ranking = tree.the_ranking();
    let reachable = tree.reachable_betree_addrs_using_ranking(ranking);
    let candidate = reachable_tight_betree(tree);
    tree.reachable_betree_addrs_using_ranking_closed(ranking);

    assert(candidate.dv.entries_wf()) by {
        assert forall |addr: Address|
            #[trigger] candidate.dv.entries.contains_key(addr)
            implies candidate.dv.entries[addr].wf()
        by {
            assert(tree.dv.entries.contains_key(addr));
            assert(candidate.dv.entries[addr] == tree.dv.entries[addr]);
        };
    };
    assert(candidate.dv.healthy_child_ptrs()) by {
        assert forall |addr: Address|
            #[trigger] candidate.dv.entries.contains_key(addr)
            implies {
                &&& candidate.dv.node_has_nondangling_child_ptrs(
                    candidate.dv.entries[addr],
                )
                &&& candidate.dv.node_has_linked_children(
                    candidate.dv.entries[addr],
                )
            }
        by {
            assert(reachable.contains(addr));
            reachable_betree_addrs_closed_under_children(
                tree,
                ranking,
                addr,
            );
            assert forall |idx: nat|
                #[trigger] candidate.dv.entries[addr].valid_child_index(idx)
                implies candidate.dv.is_nondangling_ptr(
                    candidate.dv.entries[addr].children[idx as int],
                )
            by {
                if candidate.dv.entries[addr].children[idx as int] is Some {
                    let child_addr = candidate.dv.entries[addr]
                        .children[idx as int].unwrap();
                    assert(tree.dv.entries[addr]
                        == candidate.dv.entries[addr]);
                    assert(reachable.contains(child_addr));
                    assert(candidate.dv.entries.contains_key(child_addr));
                }
            };
            assert(candidate.dv.node_has_nondangling_child_ptrs(
                candidate.dv.entries[addr],
            ));
            assert forall |idx: nat|
                #[trigger] candidate.dv.entries[addr].valid_child_index(idx)
                implies candidate.dv.child_linked(
                    candidate.dv.entries[addr],
                    idx,
                )
            by {
                let child_ptr = candidate.dv.entries[addr]
                    .children[idx as int];
                if child_ptr is Some {
                    let child_addr = child_ptr.unwrap();
                    assert(candidate.dv.entries.contains_key(child_addr));
                    assert(candidate.dv.entries[child_addr]
                        == tree.dv.entries[child_addr]);
                    assert(candidate.dv.entries[addr]
                        == tree.dv.entries[addr]);
                    assert(tree.dv.child_linked(tree.dv.entries[addr], idx));
                }
            };
        };
    };
    assert(candidate.dv.entries.dom() <= tree.dv.entries.dom());
    assert(candidate.dv.entries.dom().finite());
    assert(candidate.dv.wf());
    assert(candidate.dv.is_nondangling_ptr(candidate.root)) by {
        if candidate.root is Some {
            assert(tree.has_root());
            assert(reachable.contains(candidate.root.unwrap()));
            assert(candidate.dv.entries.contains_key(candidate.root.unwrap()));
        }
    };
    assert(candidate.wf());
    assert(candidate.valid_ranking(ranking)) by {
        assert(candidate.dv.valid_ranking(ranking)) by {
            assert forall |addr: Address|
                #[trigger] candidate.dv.entries.contains_key(addr)
                    && ranking.contains_key(addr)
                implies candidate.dv.node_children_respects_rank(
                    ranking,
                    addr,
                )
            by {
                assert(tree.dv.node_children_respects_rank(ranking, addr));
                assert(candidate.dv.entries[addr] == tree.dv.entries[addr]);
            };
        };
    };
    assert(candidate.acyclic());
    assert(candidate.dv.agrees_with(tree.dv));
    agreeable_betrees_same_reachable(
        tree,
        candidate,
        ranking,
        ranking,
    );
    assert(candidate.reachable_betree_addrs_using_ranking(ranking)
        == reachable);
    broadcast use LinkedBetree::reachable_betree_addrs_ignore_ranking;
    assert(candidate.reachable_betree_addrs() == reachable);
    assert(candidate.dv.entries.dom() == reachable);
}

proof fn reachable_tight_betree_is_candidate(
    tree: LinkedBetree<BranchNode>,
    root: crate::disk::GenericDisk_v::Pointer,
    bounded_entries: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
)
    requires
        tree.acyclic(),
        tree.root == root,
        tree.has_root() ==> tree.root().my_domain()
            == crate::betree::Domain_v::total_domain(),
        tree.dv.entries.restrict(tree.reachable_betree_addrs())
            <= bounded_entries,
    ensures
        tight_betree_candidate(
            root,
            bounded_entries,
            reachable_tight_betree(tree),
        ),
{
    reachable_tight_betree_facts(tree);
}

pub open spec fn tight_betree_candidate(
    root: crate::disk::GenericDisk_v::Pointer,
    bounded_entries: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    candidate: LinkedBetree<BranchNode>,
) -> bool {
    &&& candidate.root == root
    &&& candidate.dv.entries <= bounded_entries
    &&& candidate.buffer_dv == BufferDisk::<BranchNode>::empty_disk()
    &&& candidate.acyclic()
    &&& candidate.has_root() ==> candidate.root().my_domain()
        == crate::betree::Domain_v::total_domain()
    &&& candidate.dv.entries.dom() == candidate.reachable_betree_addrs()
}

pub open spec fn tight_betree_exists(
    root: crate::disk::GenericDisk_v::Pointer,
    bounded_entries: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
) -> bool {
    exists |candidate: LinkedBetree<BranchNode>| #[trigger] tight_betree_candidate(
        root,
        bounded_entries,
        candidate,
    )
}

pub open spec fn tight_betree_of(
    root: crate::disk::GenericDisk_v::Pointer,
    bounded_entries: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
) -> LinkedBetree<BranchNode> {
    if tight_betree_exists(root, bounded_entries) {
        choose |candidate: LinkedBetree<BranchNode>| tight_betree_candidate(
            root,
            bounded_entries,
            candidate,
        )
    } else {
        LinkedBetree {
            root,
            dv: BetreeDiskView{entries: Map::empty()},
            buffer_dv: BufferDisk::<BranchNode>::empty_disk(),
        }
    }
}

pub proof fn tight_betree_of_is_candidate(
    root: crate::disk::GenericDisk_v::Pointer,
    bounded_entries: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
)
    requires tight_betree_exists(root, bounded_entries)
    ensures tight_betree_candidate(
        root,
        bounded_entries,
        tight_betree_of(root, bounded_entries),
    )
{
}

pub proof fn tight_betree_unique(
    root: crate::disk::GenericDisk_v::Pointer,
    bounded_entries: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    left: LinkedBetree<BranchNode>,
    right: LinkedBetree<BranchNode>,
)
    requires
        tight_betree_candidate(root, bounded_entries, left),
        tight_betree_candidate(root, bounded_entries, right),
    ensures left == right
{
    assert(left.root == right.root);
    assert(left.buffer_dv == right.buffer_dv);
    assert(left.dv.agrees_with(right.dv)) by {
        assert forall |addr: Address| #[trigger] left.dv.entries.contains_key(addr)
            && right.dv.entries.contains_key(addr)
            implies left.dv.entries[addr] == right.dv.entries[addr]
        by {
            assert(bounded_entries.contains_key(addr));
            assert(left.dv.entries[addr] == bounded_entries[addr]);
            assert(right.dv.entries[addr] == bounded_entries[addr]);
        }
    };

    let ranking = left.finite_ranking();
    left.finite_ranking_ensures();
    assert(right.valid_ranking(ranking)) by {
        if right.has_root() {
            assert(left.has_root());
            assert(ranking.contains_key(right.root.unwrap()));
        }
        assert forall |addr: Address| #[trigger] right.dv.entries.contains_key(addr)
            && ranking.contains_key(addr)
            implies right.dv.node_children_respects_rank(ranking, addr)
        by {
            assert(left.dv.entries.contains_key(addr));
            assert(left.dv.entries[addr] == right.dv.entries[addr]);
            assert(left.dv.node_children_respects_rank(ranking, addr));
        }
    };
    left.agreeable_disks_same_reachable_betree_addrs(right, ranking);
    left.reachable_betree_addrs_ignore_ranking(left.the_ranking(), ranking);
    right.reachable_betree_addrs_ignore_ranking(right.the_ranking(), ranking);
    assert(left.reachable_betree_addrs() == right.reachable_betree_addrs());
    assert(left.dv.entries.dom() == right.dv.entries.dom());
    assert_maps_equal!(left.dv.entries, right.dv.entries, addr => {
        if left.dv.entries.contains_key(addr) {
            assert(right.dv.entries.contains_key(addr));
            assert(bounded_entries.contains_key(addr));
            assert(left.dv.entries[addr] == bounded_entries[addr]);
            assert(right.dv.entries[addr] == bounded_entries[addr]);
        }
        if right.dv.entries.contains_key(addr) {
            assert(left.dv.entries.contains_key(addr));
        }
    });
}

pub proof fn tight_betree_of_equals_candidate(
    root: crate::disk::GenericDisk_v::Pointer,
    bounded_entries: Map<Address, crate::betree::LinkedBetree_v::BetreeNode>,
    candidate: LinkedBetree<BranchNode>,
)
    requires tight_betree_candidate(root, bounded_entries, candidate)
    ensures tight_betree_of(root, bounded_entries) == candidate
{
    assert(tight_betree_exists(root, bounded_entries));
    tight_betree_of_is_candidate(root, bounded_entries);
    tight_betree_unique(
        root,
        bounded_entries,
        tight_betree_of(root, bounded_entries),
        candidate,
    );
}

pub proof fn tight_branch_of_is_candidate(
    loose_disk: BufferDisk<BranchNode>,
    root: Address,
    summary: Summary,
)
    requires tight_branch_exists(loose_disk, root, summary)
    ensures tight_branch_in_loose_disk(
        loose_disk,
        root,
        summary,
        tight_branch_of(loose_disk, root, summary),
    )
{
}

pub open spec fn staged_nodes_aligned(
    disk: CachingDisk::State,
    cached: CachedBulkBranch,
) -> bool {
    cached.is_sealed()
        || cached.staged_nodes()
            == to_branch_nodes(disk.visible()).restrict(
                mini_allocator_allocated_addrs(cached.mini_allocator),
            )
}

proof fn transfer_staged_nodes_alignment(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    pre_cached: CachedBulkBranch,
    post_cached: CachedBulkBranch,
)
    requires
        staged_nodes_aligned(pre_disk, pre_cached),
        post_cached.is_building(),
        pre_cached.is_building(),
        post_cached.staged_nodes() == pre_cached.staged_nodes(),
        mini_allocator_allocated_addrs(post_cached.mini_allocator)
            == mini_allocator_allocated_addrs(pre_cached.mini_allocator),
        to_branch_nodes(post_disk.visible()).restrict(
            mini_allocator_allocated_addrs(pre_cached.mini_allocator),
        ) == to_branch_nodes(pre_disk.visible()).restrict(
            mini_allocator_allocated_addrs(pre_cached.mini_allocator),
        ),
    ensures staged_nodes_aligned(post_disk, post_cached),
{
}

proof fn empty_mini_allocator_has_no_allocated_addrs(aus: Set<AU>)
    ensures
        mini_allocator_allocated_addrs(
            MiniAllocator::empty().add_aus(aus),
        ).is_empty(),
{
    assert(MiniAllocator::empty().wf());
    assert(MiniAllocator::empty().all_aus().is_empty());
    mini_allocator_add_aus_preserves_allocated_addrs(
        MiniAllocator::empty(),
        aus,
    );
    assert(mini_allocator_allocated_addrs(
        MiniAllocator::empty(),
    ).is_empty());
}

impl CachingDiskBranchBetree::State {
    pub proof fn freeze_as_next_facts(
        state: Self,
        image: crate::implementation::CachedBranchBetree_v::FrozenBranchBetree,
    )
        requires CachingDiskBranchBetree::State::next(
            state,
            state,
            CachingDiskBranchBetree::Label::FreezeAs{image},
        )
        ensures
            state.betree.memtable.is_empty(),
            image.root == state.betree.root,
            image.seq_end == state.betree.memtable.seq_end,
    {
        reveal(CachingDiskBranchBetree::State::next);
        reveal(CachingDiskBranchBetree::State::next_by);
        let step = choose |step: CachingDiskBranchBetree::Step|
            CachingDiskBranchBetree::State::next_by(
                state,
                state,
                CachingDiskBranchBetree::Label::FreezeAs{image},
                step,
            );
        match step {
            CachingDiskBranchBetree::Step::freeze_as() => {
                CachingDiskBranchBetree::State::freeze_as_effect(
                    state,
                    state,
                    CachingDiskBranchBetree::Label::FreezeAs{image},
                );
                reveal(CachedBranchBetree::State::next);
                reveal(CachedBranchBetree::State::next_by);
                let cached_step = choose |cached_step: CachedBranchBetree::Step|
                    CachedBranchBetree::State::next_by(
                        state.betree,
                        state.betree,
                        CachedBranchBetree::Label::FreezeAs{image},
                        cached_step,
                    );
                match cached_step {
                    CachedBranchBetree::Step::freeze_as() => {},
                    _ => { assert(false); },
                }
            }
            _ => {
                assert(false);
            }
        }
    }

    pub proof fn next_refines_cached(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
    )
        requires CachingDiskBranchBetree::State::next(pre, post, lbl)
        ensures CachedBranchBetree::State::next(
            pre.betree,
            post.betree,
            lbl.cached_i(),
        )
    {
        reveal(CachingDiskBranchBetree::State::next);
        reveal(CachingDiskBranchBetree::State::next_by);
        let step = choose |step: CachingDiskBranchBetree::Step|
            CachingDiskBranchBetree::State::next_by(
                pre, post, lbl, step,
            );
        match step {
            CachingDiskBranchBetree::Step::disk_internal(_) => {
                assert(CachedBranchBetree::State::internal_noop(
                    pre.betree, post.betree, lbl.cached_i(),
                ));
                assert(CachedBranchBetree::State::next_by(
                    pre.betree,
                    post.betree,
                    lbl.cached_i(),
                    CachedBranchBetree::Step::internal_noop(),
                )) by {
                    reveal(CachedBranchBetree::State::next_by);
                }
                reveal(CachedBranchBetree::State::next);
            }
            _ => {}
        }
    }

    pub proof fn next_wip_alloc_aus_subset(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::next(pre, post, lbl),
        ensures
            cached_bulk_branch_alloc_aus(post.betree.wip_branches)
                <= cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
                    + lbl.allocs(),
    {
        Self::next_refines_cached(pre, post, lbl);
        assert forall |idx: int| 0 <= idx < pre.betree.wip_branches.len()
            implies (#[trigger] pre.betree.wip_branches[idx])
                .mini_allocator.wf()
        by {
            assert(pre.i().wip_branches_inv());
            assert(pre.i().wip_branches == pre.wip_branches_i());
            assert(pre.i().wip_branches[idx] == pre.wip_branch_i(idx));
            assert(pre.i().wip_branches[idx].inv());
            assert(pre.wip_branch_i(idx).inv());
            assert(pre.wip_branch_i(idx).mini_allocator
                == pre.betree.wip_branches[idx].mini_allocator);
        };
        CachedBranchBetree::State::next_wip_alloc_aus_subset(
            pre.betree,
            post.betree,
            lbl.cached_i(),
        );
        assert(lbl.cached_i().allocs() == lbl.allocs());
    }

    pub proof fn next_preserves_guarded_visible_aus(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        stable_aus: Set<AU>,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::next(pre, post, lbl),
            !(lbl is FreezeAs),
            stable_aus.disjoint(lbl.allocs()),
            lbl is InternalAllocAccess ==>
                stable_aus <= lbl.arrow_InternalAllocAccess_guard_aus(),
            cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
                .disjoint(stable_aus),
        ensures
            post.disk.visible().restrict(addresses_in_aus(stable_aus))
                == pre.disk.visible().restrict(addresses_in_aus(stable_aus)),
    {
        reveal(CachingDiskBranchBetree::State::next);
        reveal(CachingDiskBranchBetree::State::next_by);
        let step = choose |step: CachingDiskBranchBetree::Step|
            CachingDiskBranchBetree::State::next_by(
                pre,
                post,
                lbl,
                step,
            );
        let stable_addrs = addresses_in_aus(stable_aus);
        match step {
            CachingDiskBranchBetree::Step::disk_internal(new_disk) => {
                CachingDisk::State::internal_visible_unchanged(
                    pre.disk,
                    new_disk,
                );
            }
            CachingDiskBranchBetree::Step::query() => {
            }
            CachingDiskBranchBetree::Step::put(new_betree) => {
            }
            CachingDiskBranchBetree::Step::freeze_as() => {
                assert(false);
            }
            CachingDiskBranchBetree::Step::internal_access(
                new_betree,
                new_disk,
            ) => {
                let access = lbl.arrow_InternalAccess_access();
                CachingDiskBranchBetree::State::internal_access_effect(
                    pre, post, lbl, new_betree, new_disk,
                );
                reveal(CachedBranchBetree::State::next);
                reveal(CachedBranchBetree::State::next_by);
                let cached_step = choose |cached_step: CachedBranchBetree::Step|
                    CachedBranchBetree::State::next_by(
                        pre.betree,
                        new_betree,
                        lbl.cached_i(),
                        cached_step,
                    );
                match cached_step {
                    CachedBranchBetree::Step::compact_begin(..) => {},
                    CachedBranchBetree::Step::compact_scan_page(..) => {},
                    _ => { assert(false); },
                }
                access.cached_read_only_is_read_only();
                CachingDisk::State::access_visible_effect(
                    pre.disk,
                    new_disk,
                    access.reads(),
                    access.writes(),
                );
                assert(new_disk.visible() == pre.disk.visible());
            }
            CachingDiskBranchBetree::Step::internal_alloc_access(
                new_betree,
                new_disk,
            ) => {
                let access = lbl.arrow_InternalAllocAccess_access();
                CachingDiskBranchBetree::State::internal_alloc_access_effect(
                    pre, post, lbl, new_betree, new_disk,
                );
                reveal(CachedBranchBetree::State::next);
                reveal(CachedBranchBetree::State::next_by);
                let cached_step = choose |cached_step: CachedBranchBetree::Step|
                    CachedBranchBetree::State::next_by(
                        pre.betree,
                        new_betree,
                        lbl.cached_i(),
                        cached_step,
                    );
                match cached_step {
                    CachedBranchBetree::Step::branch_begin()
                    | CachedBranchBetree::Step::branch_fill(..)
                    | CachedBranchBetree::Step::branch_abort(..)
                    | CachedBranchBetree::Step::compact_abort(..) => {
                        access.cached_empty_is_empty();
                    }
                    CachedBranchBetree::Step::branch_build(
                        idx,
                        post_branch,
                        event,
                    ) => {
                        let selected_aus = pre.betree.wip_branches[idx]
                            .mini_allocator.all_aus();
                        let allocator_sets = Seq::new(
                            pre.betree.wip_branches.len(),
                            |i: int| pre.betree.wip_branches[i]
                                .mini_allocator.all_aus(),
                        );
                        crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                            allocator_sets,
                            idx,
                        );
                        assert(selected_aus <= cached_bulk_branch_alloc_aus(
                            pre.betree.wip_branches,
                        ));
                        assert(selected_aus.disjoint(stable_aus));
                        match event {
                            CachedBulkBranchEvent::StagePage{addr, ..} => {
                                Self::branch_stage_page_refines(
                                    pre,
                                    post,
                                    lbl,
                                    new_betree,
                                    new_disk,
                                    idx,
                                    post_branch,
                                    addr,
                                    access,
                                );
                            }
                            CachedBulkBranchEvent::BulkSeal{
                                root,
                                aux_ptr,
                                ..
                            } => {
                                Self::branch_bulk_seal_refines(
                                    pre,
                                    post,
                                    lbl,
                                    new_betree,
                                    new_disk,
                                    idx,
                                    post_branch,
                                    root,
                                    aux_ptr,
                                    access,
                                );
                            }
                        }
                        addresses_in_aus_preserves_disjointness(
                            stable_aus,
                            selected_aus,
                        );
                    }
                    CachedBranchBetree::Step::flush_memtable(
                        branch_idx,
                        new_root_addr,
                        ..
                    ) => {
                        Self::flush_memtable_refines(
                            pre, post, lbl, new_betree, new_disk,
                            branch_idx, new_root_addr, access,
                        );
                        addresses_in_aus_preserves_disjointness(
                            stable_aus, lbl.allocs(),
                        );
                    }
                    CachedBranchBetree::Step::grow(new_root_addr, ..) => {
                        Self::grow_refines(
                            pre, post, lbl, new_betree, new_disk,
                            new_root_addr, access,
                        );
                        addresses_in_aus_preserves_disjointness(
                            stable_aus, lbl.allocs(),
                        );
                    }
                    CachedBranchBetree::Step::split(
                        path, request, new_addrs, path_addrs, ..
                    ) => {
                        Self::split_refines(
                            pre, post, lbl, new_betree, new_disk,
                            path, request, new_addrs, path_addrs, access,
                        );
                        addresses_in_aus_preserves_disjointness(
                            stable_aus, lbl.allocs(),
                        );
                    }
                    CachedBranchBetree::Step::flush(
                        path, child_idx, buffer_gc, new_addrs, path_addrs, ..
                    ) => {
                        Self::flush_refines(
                            pre, post, lbl, new_betree, new_disk,
                            path, child_idx, buffer_gc, new_addrs,
                            path_addrs, access,
                        );
                        addresses_in_aus_preserves_disjointness(
                            stable_aus, lbl.allocs(),
                        );
                    }
                    CachedBranchBetree::Step::compact_complete(
                        input_idx, branch_idx, path, start, end,
                        new_node_addr, path_addrs, ..
                    ) => {
                        Self::compact_complete_refines(
                            pre, post, lbl, new_betree, new_disk,
                            input_idx, branch_idx, path, start, end,
                            new_node_addr, path_addrs, access,
                        );
                        addresses_in_aus_preserves_disjointness(
                            stable_aus, lbl.allocs(),
                        );
                    }
                    _ => { assert(false); },
                }
                assert(stable_addrs.disjoint(access.writes().dom()));
                disk_access_for_alloc_visible_on_stable(
                    pre.disk,
                    new_disk,
                    lbl.allocs(),
                    lbl.arrow_InternalAllocAccess_deallocs(),
                    lbl.arrow_InternalAllocAccess_guard_aus(),
                    access.reads(),
                    access.writes(),
                    stable_addrs,
                );
            }
            CachingDiskBranchBetree::Step::internal_noop() => {
            }
            _ => {
                assert(false);
            }
        }
    }

    proof fn branch_build_nonseal_preserves_shared_state(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        event: BranchBuildEvent,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                event.cached_event(access),
            ),
            lbl.arrow_InternalAllocAccess_allocs().is_empty(),
            lbl.arrow_InternalAllocAccess_deallocs().is_empty(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx].mini_allocator.all_aus(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.linked_i() == pre.linked_i(),
            post.visible_sealed_branch_entries()
                == pre.visible_sealed_branch_entries(),
            forall |j: int| 0 <= j < pre.betree.wip_branches.len() && j != idx
                ==> #[trigger] post.wip_branch_i(j) == pre.wip_branch_i(j),
            forall |j: int|
                0 <= j < pre.betree.wip_branches.len()
                && j != idx
                && post.betree.wip_branches[j].is_building()
                ==> #[trigger] post.betree.wip_branches[j].staged_nodes()
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[j]
                                .mini_allocator,
                        ),
                    ),
    {

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let selected = pre.betree.wip_branches[idx];
        let selected_aus = selected.mini_allocator.all_aus();
        let betree_addrs = addresses_in_aus(pre.betree.betree_aus.dom());
        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );

        disk_access_without_alloc_or_dealloc(
            pre.disk,
            new_disk,
            guard_aus,
            reads,
            writes,
        );
        pre.wip_alloc_aus_agree();
        AllocationBulkBranch::alloc_aus_ensures(pre.i().wip_branches, idx);
        assert(selected_aus <= pre.i().branch_allocator_aus());
        assert(pre.i().betree_aus.dom()
            .disjoint(pre.i().branch_allocator_aus()));
        assert(summary_aus(pre.i().branch_summary)
            .disjoint(pre.i().branch_allocator_aus()));
        addresses_in_aus_preserves_disjointness(
            pre.betree.betree_aus.dom(),
            selected_aus,
        );
        addresses_in_aus_preserves_disjointness(
            summary_aus(pre.betree.branch_summary),
            selected_aus,
        );
        assert(betree_addrs.disjoint(writes.dom()));
        assert(sealed_addrs.disjoint(writes.dom()));
        disk_access_empty_alloc_visible_stable(
            pre.disk,
            new_disk,
            deallocs,
            guard_aus,
            reads,
            writes,
            betree_addrs,
        );
        disk_access_empty_alloc_visible_stable(
            pre.disk,
            new_disk,
            deallocs,
            guard_aus,
            reads,
            writes,
            sealed_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            betree_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            sealed_addrs,
        );
        assert(post.visible_betree_entries() == pre.visible_betree_entries());
        assert(post.visible_sealed_branch_entries()
            == pre.visible_sealed_branch_entries());
        assert(post.linked_i() == pre.linked_i());

        assert forall |j: int|
            0 <= j < pre.betree.wip_branches.len() && j != idx
            implies {
                &&& #[trigger] post.wip_branch_i(j)
                    == pre.wip_branch_i(j)
                &&& post.betree.wip_branches[j].is_building()
                    ==> post.betree.wip_branches[j].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[j]
                                    .mini_allocator,
                            ),
                        )
            }
        by {
            assert(post.betree.wip_branches[j]
                == pre.betree.wip_branches[j]);
            let cached = pre.betree.wip_branches[j];
            let stable = mini_allocator_allocated_addrs(cached.mini_allocator);
            assert(pre.i().wip_branches_disjoint());
            assert(pre.i().wip_branches[j].mini_allocator
                == cached.mini_allocator);
            assert(pre.i().wip_branches[idx].mini_allocator
                == selected.mini_allocator);
            assert(cached.mini_allocator.all_aus().disjoint(selected_aus));
            mini_allocator_allocated_addrs_subset_all_aus(cached.mini_allocator);
            addresses_in_aus_preserves_disjointness(
                cached.mini_allocator.all_aus(),
                selected_aus,
            );
            assert(stable.disjoint(writes.dom()));
            disk_access_empty_alloc_visible_stable(
                pre.disk,
                new_disk,
                deallocs,
                guard_aus,
                reads,
                writes,
                stable,
            );
            to_branch_nodes_restrict_agrees(
                new_disk.visible(),
                pre.disk.visible(),
                stable,
            );
            if post.betree.wip_branches[j].is_building() {
                assert(pre.betree.wip_branches[j].is_building());
                assert(pre.betree.wip_branches[j].staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                assert(post.betree.wip_branches[j].staged_nodes()
                    == to_branch_nodes(post.disk.visible()).restrict(
                        stable,
                    ));
            }
        };
        assert forall |j: int|
            0 <= j < pre.betree.wip_branches.len()
            && j != idx
            && post.betree.wip_branches[j].is_building()
            implies #[trigger]
                post.betree.wip_branches[j].staged_nodes()
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[j]
                                .mini_allocator,
                        ),
                    ) by {
            assert(post.wip_branch_i(j) == pre.wip_branch_i(j));
        }
    }

    proof fn rooted_branch_build_preserves_staged_nodes(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        event: BranchBuildEvent,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                event.cached_event(access),
            ),
            lbl.arrow_InternalAllocAccess_allocs().is_empty(),
            lbl.arrow_InternalAllocAccess_deallocs()
                <= pre.betree.wip_branches[idx]
                    .mini_allocator.all_aus(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx]
                    .mini_allocator.all_aus(),
            ),
            post_branch.is_sealed(),
        ensures
            post.staged_nodes_inv(),
    {

        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let selected_aus = pre.betree.wip_branches[idx]
            .mini_allocator.all_aus();
        let writes = access.writes();
        let reads = access.reads();
        assert(post.betree.wip_branches
            == pre.betree.wip_branches.update(idx, post_branch));
        assert(post.disk == new_disk);
        assert(post.staged_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_building()
                implies #[trigger]
                    post.betree.wip_branches[j].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[j]
                                    .mini_allocator,
                            ),
                        ) by {
                assert(j != idx);
                let source = pre.betree.wip_branches[j];
                let target = post.betree.wip_branches[j];
                let stable = mini_allocator_allocated_addrs(
                    source.mini_allocator,
                );
                assert(target == source);
                assert(source.is_building());
                assert(source.staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                assert(pre.i().wip_branches_disjoint());
                assert(pre.i().wip_branches[j].mini_allocator
                    == source.mini_allocator);
                assert(pre.i().wip_branches[idx].mini_allocator
                    == pre.betree.wip_branches[idx]
                        .mini_allocator);
                assert(source.mini_allocator.all_aus()
                    .disjoint(selected_aus));
                mini_allocator_allocated_addrs_subset_all_aus(
                    source.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    source.mini_allocator.all_aus(),
                    selected_aus,
                );
                assert(stable.disjoint(writes.dom()));
                assert((deallocs - guard_aus) <= selected_aus);
                assert(stable.disjoint(addresses_in_aus(
                    deallocs - guard_aus,
                )));
                disk_access_empty_alloc_visible_stable(
                    pre.disk,
                    new_disk,
                    deallocs,
                    guard_aus,
                    reads,
                    writes,
                    stable,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    stable,
                );
                transfer_staged_nodes_alignment(
                    pre.disk,
                    new_disk,
                    source,
                    target,
                );
            }
        }
    }

    proof fn unchanged_wips_preserve_staged_nodes_after_access(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_disk: CachingDisk::State,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            post.disk == new_disk,
            post.betree.wip_branches == pre.betree.wip_branches,
            disk_access_for_alloc(
                pre.disk,
                new_disk,
                lbl.arrow_InternalAllocAccess_allocs(),
                lbl.arrow_InternalAllocAccess_deallocs(),
                lbl.arrow_InternalAllocAccess_guard_aus(),
                access.reads(),
                access.writes(),
            ),
            cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
                .disjoint(lbl.arrow_InternalAllocAccess_allocs()),
            cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
                .disjoint(lbl.arrow_InternalAllocAccess_deallocs()),
            access.writes().dom() <= addresses_in_aus(
                lbl.arrow_InternalAllocAccess_allocs(),
            ),
        ensures
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
    {
        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let allocator_sets = Seq::new(
            pre.betree.wip_branches.len(),
            |i: int| pre.betree.wip_branches[i]
                .mini_allocator.all_aus(),
        );
        assert(post.staged_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_building()
                implies #[trigger]
                    post.betree.wip_branches[idx].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[idx]
                                    .mini_allocator,
                            ),
                        ) by {
                let cached = pre.betree.wip_branches[idx];
                let stable = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                assert(post.betree.wip_branches[idx] == cached);
                assert(cached.is_building());
                assert(cached.staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached.mini_allocator.all_aus().disjoint(allocs));
                assert(cached.mini_allocator.all_aus().disjoint(deallocs));
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    allocs,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    deallocs,
                );
                disk_access_for_alloc_visible_outside_alloc_dealloc(
                    pre.disk,
                    new_disk,
                    allocs,
                    deallocs,
                    guard_aus,
                    access.reads(),
                    access.writes(),
                    stable,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    stable,
                );
                transfer_staged_nodes_alignment(
                    pre.disk,
                    new_disk,
                    cached,
                    cached,
                );
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[idx].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[idx]
                                .mini_allocator,
                        ),
                    ) by {
                let cached = pre.betree.wip_branches[idx];
                let stable = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                assert(post.betree.wip_branches[idx] == cached);
                assert(cached.is_sealed());
                assert(cached.sealed_branch().disk_view.entries
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached.mini_allocator.all_aus().disjoint(allocs));
                assert(cached.mini_allocator.all_aus().disjoint(deallocs));
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    allocs,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    deallocs,
                );
                disk_access_for_alloc_visible_outside_alloc_dealloc(
                    pre.disk,
                    new_disk,
                    allocs,
                    deallocs,
                    guard_aus,
                    access.reads(),
                    access.writes(),
                    stable,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    stable,
                );
            }
        }
    }

    proof fn removed_wip_preserves_staged_nodes_after_access(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_disk: CachingDisk::State,
        access: PageAccess,
        removed_idx: int,
    )
        requires
            pre.refinement_inv(),
            0 <= removed_idx < pre.betree.wip_branches.len(),
            post.disk == new_disk,
            post.betree.wip_branches
                == pre.betree.wip_branches.remove(removed_idx),
            disk_access_for_alloc(
                pre.disk,
                new_disk,
                lbl.arrow_InternalAllocAccess_allocs(),
                lbl.arrow_InternalAllocAccess_deallocs(),
                lbl.arrow_InternalAllocAccess_guard_aus(),
                access.reads(),
                access.writes(),
            ),
            cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
                .disjoint(lbl.arrow_InternalAllocAccess_allocs()),
            cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
                .disjoint(lbl.arrow_InternalAllocAccess_deallocs()),
            access.writes().dom() <= addresses_in_aus(
                lbl.arrow_InternalAllocAccess_allocs(),
            ),
        ensures
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
    {
        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let allocator_sets = Seq::new(
            pre.betree.wip_branches.len(),
            |i: int| pre.betree.wip_branches[i]
                .mini_allocator.all_aus(),
        );
        assert(post.staged_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_building()
                implies #[trigger]
                    post.betree.wip_branches[idx].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[idx]
                                    .mini_allocator,
                            ),
                        ) by {
                let pre_idx = if idx < removed_idx { idx } else { idx + 1 };
                let cached = pre.betree.wip_branches[pre_idx];
                let stable = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                assert(post.betree.wip_branches[idx] == cached);
                assert(cached.is_building());
                assert(cached.staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    pre_idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached.mini_allocator.all_aus().disjoint(allocs));
                assert(cached.mini_allocator.all_aus().disjoint(deallocs));
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    allocs,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    deallocs,
                );
                disk_access_for_alloc_visible_outside_alloc_dealloc(
                    pre.disk,
                    new_disk,
                    allocs,
                    deallocs,
                    guard_aus,
                    access.reads(),
                    access.writes(),
                    stable,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    stable,
                );
                transfer_staged_nodes_alignment(
                    pre.disk,
                    new_disk,
                    cached,
                    cached,
                );
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[idx].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[idx]
                                .mini_allocator,
                        ),
                    ) by {
                let pre_idx = if idx < removed_idx { idx } else { idx + 1 };
                let cached = pre.betree.wip_branches[pre_idx];
                let stable = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                assert(post.betree.wip_branches[idx] == cached);
                assert(cached.is_sealed());
                assert(cached.sealed_branch().disk_view.entries
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    pre_idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached.mini_allocator.all_aus().disjoint(allocs));
                assert(cached.mini_allocator.all_aus().disjoint(deallocs));
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    allocs,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    deallocs,
                );
                disk_access_for_alloc_visible_outside_alloc_dealloc(
                    pre.disk,
                    new_disk,
                    allocs,
                    deallocs,
                    guard_aus,
                    access.reads(),
                    access.writes(),
                    stable,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    stable,
                );
            }
        }
    }

    proof fn unchanged_wips_preserve_staged_nodes_after_forget(
        pre: Self,
        post: Self,
        forgotten_aus: Set<AU>,
    )
        requires
            pre.refinement_inv(),
            post.betree.wip_branches == pre.betree.wip_branches,
            CachingDisk::State::next(
                pre.disk,
                post.disk,
                CachingDisk::Label::Forget{aus: forgotten_aus},
            ),
            cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
                .disjoint(forgotten_aus),
        ensures
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
    {
        let allocator_sets = Seq::new(
            pre.betree.wip_branches.len(),
            |i: int| pre.betree.wip_branches[i]
                .mini_allocator.all_aus(),
        );
        assert(post.staged_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_building()
                implies #[trigger]
                    post.betree.wip_branches[idx].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[idx]
                                    .mini_allocator,
                            ),
                        ) by {
                let cached = pre.betree.wip_branches[idx];
                let stable = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                assert(post.betree.wip_branches[idx] == cached);
                assert(cached.is_building());
                assert(cached.staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached.mini_allocator.all_aus()
                    .disjoint(forgotten_aus));
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    forgotten_aus,
                    cached.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk,
                    post.disk,
                    forgotten_aus,
                    stable,
                );
                to_branch_nodes_restrict_agrees(
                    post.disk.visible(),
                    pre.disk.visible(),
                    stable,
                );
                transfer_staged_nodes_alignment(
                    pre.disk,
                    post.disk,
                    cached,
                    cached,
                );
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[idx].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[idx]
                                .mini_allocator,
                        ),
                    ) by {
                let cached = pre.betree.wip_branches[idx];
                let stable = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                assert(post.betree.wip_branches[idx] == cached);
                assert(cached.is_sealed());
                assert(cached.sealed_branch().disk_view.entries
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached.mini_allocator.all_aus()
                    .disjoint(forgotten_aus));
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    forgotten_aus,
                    cached.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk,
                    post.disk,
                    forgotten_aus,
                    stable,
                );
                to_branch_nodes_restrict_agrees(
                    post.disk.visible(),
                    pre.disk.visible(),
                    stable,
                );
            }
        }
    }

    pub proof fn wip_alloc_aus_agree(self)
        ensures
            AllocationBulkBranch::alloc_aus(self.wip_branches_i())
                == cached_bulk_branch_alloc_aus(self.betree.wip_branches),
    {
        let target_aus = Seq::new(
            self.wip_branches_i().len(),
            |idx: int| self.wip_branches_i()[idx].mini_allocator.all_aus(),
        );
        let source_aus = Seq::new(
            self.betree.wip_branches.len(),
            |idx: int| self.betree.wip_branches[idx].mini_allocator.all_aus(),
        );
        assert_seqs_equal!(target_aus, source_aus, idx => {
            assert(self.wip_branches_i()[idx].mini_allocator
                == self.betree.wip_branches[idx].mini_allocator);
        });
    }

    pub open spec fn visible_betree_entries(self) -> Map<Address, crate::betree::LinkedBetree_v::BetreeNode> {
        to_betree_nodes(self.disk.visible()).restrict(
            addresses_in_aus(self.betree.betree_aus.dom()),
        )
    }

    pub open spec fn visible_sealed_branch_entries(self) -> Map<Address, BranchNode> {
        to_branch_nodes(self.disk.visible()).restrict(
            addresses_in_aus(summary_aus(self.betree.branch_summary)),
        )
    }

    pub open spec fn visible_sealed_branch_disk(self) -> BufferDisk<BranchNode> {
        visible_branch_disk(self.disk, self.betree.branch_summary)
    }

    pub open spec fn tight_betree_exists(self) -> bool {
        tight_betree_exists(
            self.betree.root,
            self.visible_betree_entries(),
        )
    }

    pub open spec fn tight_betree_i(self) -> LinkedBetree<BranchNode> {
        tight_betree_of(
            self.betree.root,
            self.visible_betree_entries(),
        )
    }

    pub open spec fn semantic_branch_roots(self) -> Set<Address> {
        self.tight_betree_i().reachable_buffer_addrs()
            + CompactorInput::input_roots(self.betree.compactors)
    }

    pub open spec fn tight_branches_exist(self) -> bool {
        forall |root: Address| #[trigger] self.semantic_branch_roots().contains(root) ==> {
            &&& self.betree.branch_summary.contains_key(root.au)
            &&& tight_branch_exists(
                loose_disk_for_summary(
                    self.visible_sealed_branch_disk(),
                    self.betree.branch_summary[root.au],
                ),
                root,
                self.betree.branch_summary[root.au],
            )
        }
    }

    pub open spec fn semantic_sealed_branch_disk(self) -> BufferDisk<BranchNode> {
        tight_sealed_branch_disk(
            self.visible_sealed_branch_disk(),
            self.semantic_branch_roots(),
            self.betree.branch_summary,
        )
    }

    pub open spec fn linked_i(self) -> LinkedBetree<BranchNode> {
        LinkedBetree {
            root: self.tight_betree_i().root,
            dv: self.tight_betree_i().dv,
            buffer_dv: self.semantic_sealed_branch_disk(),
        }
    }

    pub open spec fn wip_branch_i(self, idx: int) -> AllocationBulkBranch
        recommends 0 <= idx < self.betree.wip_branches.len()
    {
        let cached = self.betree.wip_branches[idx];
        let entries = to_branch_nodes(self.disk.visible()).restrict(
            mini_allocator_allocated_addrs(cached.mini_allocator),
        );
        AllocationBulkBranch {
            phase: if cached.is_sealed() {
                BulkBranchPhase::Sealed {
                    branch: cached.sealed_branch(),
                }
            } else {
                BulkBranchPhase::Building
            },
            mini_allocator: cached.mini_allocator,
        }
    }

    pub open spec fn wip_branches_i(self) -> Seq<AllocationBulkBranch> {
        Seq::new(
            self.betree.wip_branches.len(),
            |idx: int| self.wip_branch_i(idx),
        )
    }

    pub open spec fn i(self) -> AllocationBranchBetree::State {
        AllocationBranchBetree::State {
            betree: LinkedBetreeVars::State {
                memtable: self.betree.memtable,
                linked: self.linked_i(),
            },
            betree_aus: self.betree.betree_aus,
            branch_aus: self.betree.branch_aus,
            branch_summary: self.betree.branch_summary,
            compactors: self.betree.compactors,
            wip_branches: self.wip_branches_i(),
        }
    }

    pub open spec fn semantic_selector_inv(self) -> bool {
        &&& self.tight_betree_exists()
        &&& self.tight_branches_exist()
        &&& set_addrs_disjoint_aus(
            self.tight_betree_i().dv.entries.dom(),
        )
    }

    pub open spec fn refinement_inv(self) -> bool {
        &&& self.inv()
        &&& self.semantic_selector_inv()
        &&& self.staged_nodes_inv()
        &&& self.sealed_wip_nodes_inv()
        &&& self.compactor_receipts_inv()
        &&& self.i().inv()
    }

    pub open spec fn staged_nodes_inv(self) -> bool {
        forall |idx: int|
            0 <= idx < self.betree.wip_branches.len()
            && self.betree.wip_branches[idx].is_building()
            ==> #[trigger] self.betree.wip_branches[idx].staged_nodes()
                == to_branch_nodes(self.disk.visible()).restrict(
                    mini_allocator_allocated_addrs(
                        self.betree.wip_branches[idx].mini_allocator,
                    ),
                )
    }

    pub open spec fn sealed_wip_nodes_inv(self) -> bool {
        forall |idx: int|
            0 <= idx < self.betree.wip_branches.len()
            && self.betree.wip_branches[idx].is_sealed()
            ==> #[trigger] self.betree.wip_branches[idx].sealed_branch()
                    .disk_view.entries
                == to_branch_nodes(self.disk.visible()).restrict(
                    mini_allocator_allocated_addrs(
                        self.betree.wip_branches[idx].mini_allocator,
                    ),
                )
    }

    pub open spec fn compactor_receipts_inv(self) -> bool {
        &&& self.betree.compactor_receipts.len()
            == self.betree.compactors.len()
        &&& forall |idx: int| 0 <= idx < self.betree.compactors.len() ==> {
            let receipt = #[trigger] self.betree.compactor_receipts[idx];
            &&& receipt.dom() <= addresses_in_aus(
                self.betree.compactor_input_aus(idx),
            )
            &&& BranchDiskView { entries: receipt }.agrees_with_disk(
                BranchDiskView {
                    entries: to_branch_nodes(self.disk.visible()),
                },
            )
        }
    }

    pub proof fn linked_i_is_tight_candidate(self)
        requires self.refinement_inv()
        ensures tight_betree_candidate(
            self.betree.root,
            self.visible_betree_entries(),
            self.tight_betree_i(),
        )
    {
        tight_betree_of_is_candidate(
            self.betree.root,
            self.visible_betree_entries(),
        );
    }
}

impl CachingDiskBranchBetree::Label {
    pub open spec fn allocs(self) -> Set<AU> {
        match self {
            CachingDiskBranchBetree::Label::InternalAllocAccess{allocs, ..} =>
                allocs,
            _ => Set::empty(),
        }
    }

    pub open spec fn cached_i(self) -> CachedBranchBetree::Label {
        match self {
            CachingDiskBranchBetree::Label::Query{
                end_lsn,
                key,
                value,
                access,
            } => CachedBranchBetree::Label::Query{
                end_lsn,
                key,
                value,
                access: access.cached_access(),
            },
            CachingDiskBranchBetree::Label::Put{puts} =>
                CachedBranchBetree::Label::Put{puts},
            CachingDiskBranchBetree::Label::FreezeAs{image} =>
                CachedBranchBetree::Label::FreezeAs{image},
            CachingDiskBranchBetree::Label::Internal =>
                CachedBranchBetree::Label::Internal,
            CachingDiskBranchBetree::Label::InternalAccess{access} =>
                CachedBranchBetree::Label::InternalAccess{
                    access: access.cached_access(),
                },
            CachingDiskBranchBetree::Label::InternalAllocAccess{
                allocs,
                deallocs,
                access,
                ..
            } => CachedBranchBetree::Label::InternalAllocAccess{
                allocs,
                deallocs,
                access: access.cached_access(),
            },
        }
    }

    pub open spec fn i(
        self,
        pre: CachingDiskBranchBetree::State,
    ) -> AllocationBranchBetree::Label {
        match self {
            CachingDiskBranchBetree::Label::Query{
                end_lsn,
                key,
                value,
                ..
            } => {
                AllocationBranchBetree::Label::Label {
                    linked_lbl: LinkedBetreeVars::Label::Query{end_lsn, key, value},
                }
            }
            CachingDiskBranchBetree::Label::Put{puts} => {
                AllocationBranchBetree::Label::Label {
                    linked_lbl: LinkedBetreeVars::Label::Put{puts},
                }
            }
            CachingDiskBranchBetree::Label::FreezeAs{image} => {
                AllocationBranchBetree::Label::Label {
                    linked_lbl: LinkedBetreeVars::Label::FreezeAs {
                        stamped_betree: Stamped {
                            value: pre.i().betree.linked.i_bdv(),
                            seq_end: image.seq_end,
                        },
                    },
                }
            }
            CachingDiskBranchBetree::Label::Internal => {
                AllocationBranchBetree::Label::Internal
            }
            CachingDiskBranchBetree::Label::InternalAccess{..} => {
                AllocationBranchBetree::Label::Internal
            }
            CachingDiskBranchBetree::Label::InternalAllocAccess{..} => {
                AllocationBranchBetree::Label::Internal
            }
        }
    }
}

pub open spec fn allocation_compact_complete_conditions(
    pre: AllocationBranchBetree::State,
    post: AllocationBranchBetree::State,
    lbl: AllocationBranchBetree::Label,
    new_betree: LinkedBetreeVars::State<BranchNode>,
    path: Path<BranchNode>,
    start: nat,
    end: nat,
    input_idx: int,
    branch_idx: int,
    new_node_addr: Address,
    path_addrs: PathAddrs,
) -> bool {
    let new_branch = pre.wip_branches[branch_idx].sealed_branch();
    let linked_new_addrs = TwoAddrs {
        addr1: new_node_addr,
        addr2: new_branch.root,
    };
    let new_compactors = pre.compactors.remove(input_idx);
    let compacted = LinkedBetreeVars::State::post_compact(
        path,
        start,
        end,
        new_branch.root(),
        linked_new_addrs,
        path_addrs,
    );
    let (new_betree_aus, new_branch_aus) =
        crate::allocation_layer::AllocationBetree_v::AllocationBetree::State::internal_compact_complete_au_likes(
            path,
            start,
            end,
            linked_new_addrs,
            path_addrs,
            pre.betree_aus,
            pre.branch_aus,
        );
    let tree_deallocs = pre.betree_aus.dom() - new_betree_aus.dom();
    let branch_deallocs = pre.branch_summary.dom()
        - new_branch_aus.dom()
        - read_ref_aus(new_compactors);
    let new_branch_summary = pre.branch_summary.insert(
        new_branch.root.au,
        new_branch.get_summary(),
    ).remove_keys(branch_deallocs);
    let new_summary_aus = summary_aus(new_branch_summary);
    let dealloc_branch_summary = pre.branch_summary.restrict(
        branch_deallocs,
    );
    let summary_deallocs_aus = summary_aus(dealloc_branch_summary);
    let full_buffer_dv = pre.betree.linked.buffer_dv.entries
        .union_prefer_right(new_branch.disk_view.entries);
    let post_buffer_domain =
        crate::allocation_layer::Likes_v::restrict_domain_au(
            full_buffer_dv,
            new_summary_aus,
        );
    let allocs =
        seq_addrs_to_aus(path_addrs).insert(new_node_addr.au);

    &&& lbl is Internal
    &&& pre.is_fresh(allocs)
    &&& !seq_addrs_to_aus(path_addrs).contains(new_node_addr.au)
    &&& seq_addrs_disjoint_aus(path_addrs)
    &&& 0 <= input_idx < pre.compactors.len()
    &&& AllocationBranchBetree::State::valid_compactor_input(
        path,
        start,
        end,
        pre.compactors[input_idx],
    )
    &&& 0 <= branch_idx < pre.wip_branches.len()
    &&& pre.wip_branches[branch_idx].is_sealed()
    &&& LinkedBetreeVars::State::internal_compact(
        pre.betree,
        new_betree,
        crate::allocation_layer::AllocationBranchBetree_v::Internal,
        new_betree.linked,
        path,
        start,
        end,
        new_branch.root(),
        linked_new_addrs,
        path_addrs,
    )
    &&& crate::allocation_layer::Likes_v::restrict_domain_au(
        compacted.dv.entries,
        new_betree_aus.dom(),
    ) == new_betree.linked.dv.entries.dom()
    &&& new_betree.linked.buffer_dv.entries
        == full_buffer_dv.restrict(post_buffer_domain)
    &&& post == AllocationBranchBetree::State {
        betree: new_betree,
        betree_aus: new_betree_aus,
        branch_aus: new_branch_aus,
        branch_summary: new_branch_summary,
        compactors: new_compactors,
        wip_branches: pre.wip_branches.remove(branch_idx),
    }
}

proof fn allocation_compact_complete_intro(
    pre: AllocationBranchBetree::State,
    post: AllocationBranchBetree::State,
    lbl: AllocationBranchBetree::Label,
    new_betree: LinkedBetreeVars::State<BranchNode>,
    path: Path<BranchNode>,
    start: nat,
    end: nat,
    input_idx: int,
    branch_idx: int,
    new_node_addr: Address,
    path_addrs: PathAddrs,
)
    requires
        allocation_compact_complete_conditions(
            pre,
            post,
            lbl,
            new_betree,
            path,
            start,
            end,
            input_idx,
            branch_idx,
            new_node_addr,
            path_addrs,
        ),
    ensures
        AllocationBranchBetree::State::internal_compact_complete(
            pre,
            post,
            lbl,
            new_betree,
            path,
            start,
            end,
            input_idx,
            branch_idx,
            new_node_addr,
            path_addrs,
        ),
{
}

pub open spec fn initial_tight_tree(
    initial_betree: LinkedBetreeVars::State<BranchNode>,
) -> LinkedBetree<BranchNode> {
    LinkedBetree {
        root: initial_betree.linked.root,
        dv: initial_betree.linked.dv,
        buffer_dv: BufferDisk::<BranchNode>::empty_disk(),
    }
}

pub open spec fn initial_allocation_state(
    initial_betree: LinkedBetreeVars::State<BranchNode>,
    betree_aus: crate::allocation_layer::Likes_v::AULikes,
    branch_aus: crate::allocation_layer::Likes_v::AULikes,
    branch_summary: Map<AU, Summary>,
) -> AllocationBranchBetree::State {
    AllocationBranchBetree::State {
        betree: initial_betree,
        betree_aus,
        branch_aus,
        branch_summary,
        compactors: Seq::empty(),
        wip_branches: Seq::empty(),
    }
}

pub open spec fn initial_refinement_witness_valid(
    disk: CachingDisk::State,
    root: crate::disk::GenericDisk_v::Pointer,
    seq_end: crate::abstract_system::StampedMap_v::LSN,
    betree_aus: crate::allocation_layer::Likes_v::AULikes,
    branch_aus: crate::allocation_layer::Likes_v::AULikes,
    branch_summary: Map<AU, Summary>,
    initial_betree: LinkedBetreeVars::State<BranchNode>,
) -> bool {
    let tree = initial_tight_tree(initial_betree);
    let visible_tree = to_betree_nodes(disk.visible()).restrict(
        addresses_in_aus(betree_aus.dom()),
    );
    let loose_branches = visible_branch_disk(disk, branch_summary);
    let roots = tree.reachable_buffer_addrs();
    let target = initial_allocation_state(
        initial_betree,
        betree_aus,
        branch_aus,
        branch_summary,
    );

    &&& initial_betree.memtable
        == crate::betree::Memtable_v::Memtable::empty_memtable(seq_end)
    &&& tight_betree_candidate(root, visible_tree, tree)
    &&& set_addrs_disjoint_aus(tree.dv.entries.dom())
    &&& forall |branch_root: Address| #[trigger] roots.contains(branch_root) ==> {
        &&& branch_summary.contains_key(branch_root.au)
        &&& tight_branch_exists(
            loose_disk_for_summary(
                loose_branches,
                branch_summary[branch_root.au],
            ),
            branch_root,
            branch_summary[branch_root.au],
        )
    }
    &&& tight_sealed_branch_disk(
        loose_branches,
        roots,
        branch_summary,
    ) == initial_betree.linked.buffer_dv
    &&& AllocationBranchBetree::State::initialize(
        target,
        initial_betree,
    )
}

pub open spec fn durable_recovery_disk(
    state: CachingDiskBranchBetree::State,
) -> CachingDisk::State {
    CachingDisk::State {
        cache: Map::empty(),
        persistent: state.disk.visible().restrict(
            addresses_in_aus(state.betree.durable_aus()),
        ),
        status: Map::empty(),
    }
}

pub proof fn durable_recovery_witness_valid(
    state: CachingDiskBranchBetree::State,
)
    requires
        state.refinement_inv(),
        state.betree.memtable.is_empty(),
        state.betree.compactors.len() == 0,
        state.betree.wip_branches.len() == 0,
    ensures
        initial_refinement_witness_valid(
            durable_recovery_disk(state),
            state.betree.root,
            state.betree.memtable.seq_end,
            state.betree.betree_aus,
            state.betree.branch_aus,
            state.betree.branch_summary,
            state.i().betree,
        ),
{
    let disk = durable_recovery_disk(state);
    let initial = state.i().betree;
    let durable_addrs = addresses_in_aus(
        state.betree.durable_aus(),
    );
    let betree_addrs = addresses_in_aus(
        state.betree.betree_aus.dom(),
    );
    let branch_addrs = addresses_in_aus(
        summary_aus(state.betree.branch_summary),
    );
    CachingDisk::State::persistent_only_inv(disk.persistent);
    assert(state.betree.betree_aus.dom()
        <= state.betree.durable_aus());
    assert(summary_aus(state.betree.branch_summary)
        <= state.betree.durable_aus());
    assert(betree_addrs <= durable_addrs) by {
        assert forall |addr: Address|
            #[trigger] betree_addrs.contains(addr)
            implies durable_addrs.contains(addr) by {
            assert(state.betree.betree_aus.dom().contains(addr.au));
            assert(state.betree.durable_aus().contains(addr.au));
        };
    }
    assert(branch_addrs <= durable_addrs) by {
        assert forall |addr: Address|
            #[trigger] branch_addrs.contains(addr)
            implies durable_addrs.contains(addr) by {
            assert(summary_aus(
                state.betree.branch_summary,
            ).contains(addr.au));
            assert(state.betree.durable_aus().contains(addr.au));
        };
    }

    assert(to_betree_nodes(disk.visible()).restrict(betree_addrs)
        == state.visible_betree_entries()) by {
        assert_maps_equal!(
            to_betree_nodes(disk.visible()).restrict(betree_addrs),
            state.visible_betree_entries(),
            addr => {
                if betree_addrs.contains(addr) {
                    assert(durable_addrs.contains(addr));
                    assert(disk.visible().contains_key(addr)
                        <==> state.disk.visible().contains_key(addr));
                    if state.disk.visible().contains_key(addr) {
                        assert(disk.visible()[addr]
                            == state.disk.visible()[addr]);
                    }
                }
            }
        );
    }
    assert(visible_branch_disk(
        disk,
        state.betree.branch_summary,
    ) == state.visible_sealed_branch_disk()) by {
        assert_maps_equal!(
            visible_branch_disk(
                disk,
                state.betree.branch_summary,
            ).entries,
            state.visible_sealed_branch_disk().entries,
            addr => {
                if branch_addrs.contains(addr) {
                    assert(durable_addrs.contains(addr));
                    assert(disk.visible().contains_key(addr)
                        <==> state.disk.visible().contains_key(addr));
                    if state.disk.visible().contains_key(addr) {
                        assert(disk.visible()[addr]
                            == state.disk.visible()[addr]);
                    }
                }
            }
        );
    }

    state.linked_i_is_tight_candidate();
    assert(initial_tight_tree(initial)
        == state.tight_betree_i());
    assert(initial.linked.buffer_dv
        == state.semantic_sealed_branch_disk());
    assert(CompactorInput::input_roots(
        state.betree.compactors,
    ) == Set::<Address>::empty());
    assert(state.semantic_branch_roots()
        == state.tight_betree_i().reachable_buffer_addrs());
    assert(initial_tight_tree(initial).reachable_buffer_addrs()
        == state.semantic_branch_roots());
    assert(initial.memtable
        == crate::betree::Memtable_v::Memtable::empty_memtable(
            state.betree.memtable.seq_end,
        ));
    assert(initial.linked.buffer_dv
        == tight_sealed_branch_disk(
            visible_branch_disk(
                disk,
                state.betree.branch_summary,
            ),
            initial_tight_tree(initial).reachable_buffer_addrs(),
            state.betree.branch_summary,
        ));

    assert(initial.linked.inv());
    assert(LinkedBetreeVars::State::initialize(
        initial,
        initial,
    ));
    assert(state.i().betree_aus
        == to_au_likes(initial.linked.transitive_likes().0));
    assert(state.i().branch_aus
        == to_au_likes(initial.linked.transitive_likes().1));
    assert(state.i().compactors == Seq::<CompactorInput>::empty());
    assert(state.i().wip_branches
        == Seq::<AllocationBulkBranch>::empty()) by {
        assert_seqs_equal!(
            state.i().wip_branches,
            Seq::<AllocationBulkBranch>::empty(),
            idx => {}
        );
    }
    assert(CompactorInput::input_roots(state.i().compactors)
        == Set::<Address>::empty());
    assert(state.i().branch_summary =~=
        initial.linked.buffer_dv.build_branch_summary(
            initial.linked.transitive_likes().1.dom()
                + CompactorInput::input_roots(state.i().compactors),
        ));
    assert(initial.linked.transitive_likes().1.dom()
        + CompactorInput::input_roots(state.i().compactors)
        =~= initial.linked.transitive_likes().1.dom());
    assert(state.i().branch_summary =~=
        initial.linked.buffer_dv.build_branch_summary(
            initial.linked.transitive_likes().1.dom(),
        ));
    assert_maps_equal!(
        state.i().branch_summary,
        initial.linked.buffer_dv.build_branch_summary(
            initial.linked.transitive_likes().1.dom(),
        ),
        au => {}
    );
    assert(AllocationBranchBetree::State::initialize(
        state.i(),
        initial,
    ));
}

// -------------------------------------------------------------------------
// Step refinements
// -------------------------------------------------------------------------

impl CachingDiskBranchBetree::State {
    pub proof fn init_refines(
        post: Self,
        disk: CachingDisk::State,
        betree: CachedBranchBetree::State,
        root: crate::disk::GenericDisk_v::Pointer,
        seq_end: crate::abstract_system::StampedMap_v::LSN,
        betree_aus: crate::allocation_layer::Likes_v::AULikes,
        branch_aus: crate::allocation_layer::Likes_v::AULikes,
        branch_summary: Map<AU, Summary>,
        initial_betree: LinkedBetreeVars::State<BranchNode>,
    )
        requires
            CachingDiskBranchBetree::State::initialize(
                post,
                disk,
                betree,
            ),
            CachedBranchBetree::State::initialize(
                betree,
                root,
                seq_end,
                betree_aus,
                branch_aus,
                branch_summary,
            ),
            initial_refinement_witness_valid(
                disk,
                root,
                seq_end,
                betree_aus,
                branch_aus,
                branch_summary,
                initial_betree,
            ),
        ensures
            post.refinement_inv(),
            post.i().betree == initial_betree,
            AllocationBranchBetree::State::initialize(post.i(), post.i().betree),
    {

        let tree = initial_tight_tree(initial_betree);
        let visible_tree = to_betree_nodes(disk.visible()).restrict(
            addresses_in_aus(betree_aus.dom()),
        );
        let loose_branches = visible_branch_disk(disk, branch_summary);
        let roots = tree.reachable_buffer_addrs();
        let target = initial_allocation_state(
            initial_betree,
            betree_aus,
            branch_aus,
            branch_summary,
        );

        assert(post.disk == disk);
        assert(post.betree == betree);
        assert(post.betree.root == root);
        assert(post.betree.betree_aus == betree_aus);
        assert(post.betree.branch_aus == branch_aus);
        assert(post.betree.branch_summary == branch_summary);
        assert(post.betree.compactors == Seq::<CompactorInput>::empty());
        assert(post.betree.wip_branches == Seq::<CachedBulkBranch>::empty());
        assert(post.visible_betree_entries() == visible_tree);
        assert(tight_betree_candidate(root, visible_tree, tree));
        assert(post.tight_betree_exists()) by {
            assert(exists |candidate: LinkedBetree<BranchNode>|
                tight_betree_candidate(root, visible_tree, candidate)) by {
                assert(tight_betree_candidate(root, visible_tree, tree));
            };
        };
        tight_betree_of_equals_candidate(root, visible_tree, tree);
        assert(post.tight_betree_i() == tree);

        assert(post.semantic_branch_roots() == roots);
        assert(post.visible_sealed_branch_disk() == loose_branches);
        assert(post.tight_branches_exist()) by {
            assert forall |branch_root: Address|
                #[trigger] post.semantic_branch_roots().contains(branch_root)
                implies {
                    &&& post.betree.branch_summary.contains_key(branch_root.au)
                    &&& tight_branch_exists(
                        loose_disk_for_summary(
                            post.visible_sealed_branch_disk(),
                            post.betree.branch_summary[branch_root.au],
                        ),
                        branch_root,
                        post.betree.branch_summary[branch_root.au],
                    )
                }
            by {
                assert(roots.contains(branch_root));
            };
        };
        assert(post.semantic_sealed_branch_disk()
            == initial_betree.linked.buffer_dv);
        assert(post.linked_i() == initial_betree.linked);
        assert(post.i() == target);

        assert(AllocationBranchBetree::State::initialize(
            target,
            initial_betree,
        ));
        AllocationBranchBetree::State::inv_init(target, initial_betree);
        assert(post.i().inv());
        assert(post.inv());
        assert(post.semantic_selector_inv());
    }

    pub proof fn linked_i_tight_tree_facts(self)
        requires self.refinement_inv()
        ensures
            self.linked_i().dv.entries.dom()
                == self.linked_i().reachable_betree_addrs(),
            self.linked_i().dv.entries <= self.visible_betree_entries(),
    {
        self.linked_i_is_tight_candidate();
        let tree = self.tight_betree_i();
        let linked = self.linked_i();
        let ranking = tree.the_ranking();
        assert(linked.valid_ranking(ranking));
        tree.agreeable_disks_same_reachable_betree_addrs(linked, ranking);
        tree.reachable_betree_addrs_ignore_ranking(tree.the_ranking(), ranking);
        linked.reachable_betree_addrs_ignore_ranking(linked.the_ranking(), ranking);
        assert(tree.reachable_betree_addrs() == linked.reachable_betree_addrs());
    }

    proof fn query_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        receipt: LoadedBetreeQueryReceipt,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            lbl is Query,
            access == lbl.arrow_Query_access(),
            CachingDiskBranchBetree::State::query(pre, post, lbl),
            CachedBranchBetree::State::query(
                pre.betree,
                post.betree,
                lbl.cached_i(),
                receipt,
                access.loaded_betree_reads(),
                access.loaded_branch_reads(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::au_likes_noop(
                pre.i(),
                post.i(),
                lbl.i(pre),
                post.i().betree,
            ),
    {
        access.cached_wf_is_wf();
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);

        let reads = access.reads();
        let betree_reads = access.betree_reads;
        let branch_reads = access.branch_reads;
        let linked = pre.linked_i();
        let linked_receipt = loaded_query_receipt_i(receipt, linked);
        let line_count = receipt.path.lines.len();
        let (_, branch_likes) = linked.transitive_likes();
        let compactor_roots = CompactorInput::input_roots(pre.betree.compactors);

        CachingDisk::State::access_effect(
            pre.disk,
            pre.disk,
            reads,
            access.writes(),
        );
        assert(reads <= pre.disk.cache);
        assert(betree_reads <= reads);
        assert(branch_reads <= reads);
        assert(betree_reads <= pre.disk.cache) by {
            assert forall |addr: Address| #[trigger] betree_reads.contains_key(addr)
                implies pre.disk.cache.contains_key(addr)
                    && betree_reads[addr] == pre.disk.cache[addr]
            by {
                assert(reads.contains_key(addr));
                assert(betree_reads[addr] == reads[addr]);
            };
        }
        assert(branch_reads <= pre.disk.cache) by {
            assert forall |addr: Address| #[trigger] branch_reads.contains_key(addr)
                implies pre.disk.cache.contains_key(addr)
                    && branch_reads[addr] == pre.disk.cache[addr]
            by {
                assert(reads.contains_key(addr));
                assert(branch_reads[addr] == reads[addr]);
            };
        }
        assert(access.writes().is_empty());
        assert(post == pre);
        assert(receipt.valid_for(
            pre.betree.root,
            lbl.arrow_Query_key(),
            access.loaded_betree_reads(),
            access.loaded_branch_reads(),
        ));
        if linked.root is None {
            assert(receipt.path.lines.len() == 0);
            assert(receipt.buffer_receipts.len() == 0);
            assert(line_count == 0);
            assert(linked_receipt.lines.len() == 1);
            assert(linked_receipt.lines[0].linked == linked);
            assert(linked_receipt.lines[0].result
                == Message::Define { value: default_value() });
            assert(linked_receipt.structure()) by {
                assert(linked.wf());
            }
            assert(linked_receipt.all_lines_wf()) by {
                assert(linked.acyclic());
            }
            assert(linked_receipt.valid_for(
                linked,
                receipt.path.key,
            ));
            assert(linked_receipt.result() == receipt.result());
            assert(LinkedBetreeVars::State::query(
                pre.i().betree,
                post.i().betree,
                lbl.i(pre)->linked_lbl,
                linked_receipt,
            ));
            assert(LinkedBetreeVars::State::next_by(
                pre.i().betree,
                post.i().betree,
                lbl.i(pre)->linked_lbl,
                LinkedBetreeVars::Step::query(linked_receipt),
            ));
            assert(LinkedBetreeVars::State::next(
                pre.i().betree,
                post.i().betree,
                lbl.i(pre)->linked_lbl,
            ));
            assert(post.semantic_selector_inv());
            return;
        }
        assert(receipt.path.valid_for(
            linked.root,
            to_betree_nodes(betree_reads),
        ));
        pre.linked_i_is_tight_candidate();
        pre.linked_i_tight_tree_facts();
        assert(linked.dv.entries <= to_betree_nodes(pre.disk.visible())) by {
            assert(linked.dv == pre.tight_betree_i().dv);
            assert(pre.tight_betree_i().dv.entries <= pre.visible_betree_entries());
            assert forall |addr: Address| #[trigger] linked.dv.entries.contains_key(addr)
                implies to_betree_nodes(pre.disk.visible()).contains_key(addr)
                    && linked.dv.entries[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]
            by {
                assert(pre.visible_betree_entries().contains_key(addr));
                assert(linked.dv.entries[addr] == pre.visible_betree_entries()[addr]);
            };
        }
        assert(linked.buffer_dv.entries <= to_branch_nodes(pre.disk.visible())) by {
            assert(linked.buffer_dv.entries
                <= pre.visible_sealed_branch_disk().entries);
            assert(pre.visible_sealed_branch_disk().entries
                <= to_branch_nodes(pre.disk.visible()));
        }

        linked.tree_likes_domain(linked.the_ranking());
        linked.buffer_likes_domain(linked.tree_likes(linked.the_ranking()));
        assert(branch_likes.dom() == linked.reachable_buffer_addrs());
        assert(linked.buffer_dv.sealed_branch_roots(
            branch_likes.dom() + compactor_roots,
        ));

        assert forall |i: int| 0 <= i < line_count implies {
            let line = #[trigger] receipt.path.lines[i];
            let path = Path{linked, key: receipt.path.key, depth: i as nat};
            &&& path.valid()
            &&& path.target().root == Some(line.addr)
            &&& path.target().root() == line.node
            &&& path.target().dv == linked.dv
            &&& path.target().buffer_dv == linked.buffer_dv
        } by {
            assert(i as nat <= receipt.path.depth());
            loaded_betree_path_matches_linked(
                pre.disk,
                linked,
                betree_reads,
                receipt.path,
                i as nat,
            );
        };

        assert(linked_receipt.structure()) by {
            assert(line_count > 0);
            assert(linked_receipt.lines.len() == line_count + 1);
            assert(Path{linked, key: receipt.path.key, depth: 0}.target() == linked);
            assert forall |i: nat| i < linked_receipt.lines.len()
                implies (#[trigger] linked_receipt.lines[i as int].linked.dv) == linked.dv
            by {
                if i < line_count {
                    loaded_betree_path_matches_linked(
                        pre.disk, linked, betree_reads, receipt.path, i,
                    );
                }
            };
            assert forall |i: nat| i < linked_receipt.lines.len()
                implies (#[trigger] linked_receipt.lines[i as int].linked.buffer_dv)
                    == linked.buffer_dv
            by {
                if i < line_count {
                    loaded_betree_path_matches_linked(
                        pre.disk, linked, betree_reads, receipt.path, i,
                    );
                }
            };
            assert forall |i: nat| i < linked_receipt.lines.len()
                implies ((#[trigger] linked_receipt.lines[i as int].linked.has_root())
                    <==> i < linked_receipt.lines.len() - 1)
            by {
                assert(linked_receipt.lines.len() - 1 == line_count);
                if i < line_count {
                    loaded_betree_path_matches_linked(
                        pre.disk, linked, betree_reads, receipt.path, i,
                    );
                    assert(linked_receipt.lines[i as int].linked
                        == Path{linked, key: receipt.path.key, depth: i}.target());
                    assert(linked_receipt.lines[i as int].linked.root is Some);
                    assert(linked_receipt.lines[i as int].linked.has_root());
                } else {
                    assert(i == line_count);
                    assert(linked_receipt.lines[i as int].linked.root is None);
                    assert(!linked_receipt.lines[i as int].linked.has_root());
                }
            };
        }

        assert forall |i: int| 0 <= i < line_count implies {
            let line = #[trigger] receipt.path.lines[i];
            let node = line.node;
            &&& node.buffers.addrs.to_set() <= linked.reachable_buffer_addrs()
            &&& linked.buffer_dv.valid_buffers(node.buffers)
            &&& linked.buffer_dv.sealed_branch_roots(node.buffers.addrs.to_set())
        } by {
            let node = receipt.path.lines[i].node;
            let tree_addr = receipt.path.lines[i].addr;
            loaded_betree_path_matches_linked(
                pre.disk, linked, betree_reads, receipt.path, i as nat,
            );
            assert(linked.reachable_betree_addrs().contains(tree_addr)) by {
                assert(linked.dv.entries.contains_key(tree_addr));
                assert(linked.dv.entries.dom()
                    == linked.reachable_betree_addrs());
            }
            assert forall |root: Address| #[trigger] node.buffers.addrs.to_set().contains(root)
                implies linked.reachable_buffer_addrs().contains(root)
            by {
                assert(node.buffers.contains(root));
                assert(linked.reachable_buffer(tree_addr, root));
            };
            assert(node.buffers.addrs.to_set() <= branch_likes.dom() + compactor_roots);
            linked.buffer_dv.sealed_branch_roots_subset(
                branch_likes.dom() + compactor_roots,
                node.buffers.addrs.to_set(),
            );
            assert(node.buffers.addrs.to_set() <= linked.buffer_dv.repr()) by {
                assert(node.buffers.addrs.to_set()
                    <= linked.reachable_buffer_addrs());
                assert(linked.no_dangling_buffer_ptr());
            }
        };

        assert(linked_receipt.all_lines_wf()) by {
            assert forall |i: int| 0 <= i < linked_receipt.lines.len()
                implies (#[trigger] linked_receipt.lines[i].wf())
            by {
                if i < line_count {
                    loaded_query_result_is_define(receipt, i);
                }
            };
            assert forall |i: int| 0 <= i < linked_receipt.lines.len()
                implies (#[trigger] linked_receipt.lines[i].linked.acyclic())
            by {
                if i < line_count {
                    loaded_betree_path_matches_linked(
                        pre.disk, linked, betree_reads, receipt.path, i as nat,
                    );
                } else {
                    let final_linked = linked_receipt.lines[i].linked;
                    assert(final_linked.wf());
                    assert(final_linked.valid_ranking(linked.the_ranking()));
                    assert(final_linked.acyclic());
                }
            };
            assert forall |i: int| 0 <= i < linked_receipt.lines.len() - 1
                implies #[trigger] linked.buffer_dv.valid_buffers(linked_receipt.node(i).buffers)
            by {
                assert(linked_receipt.node(i) == receipt.path.lines[i].node);
            };
            assert forall |i: int| 0 <= i < linked_receipt.lines.len() - 1
                implies (#[trigger] linked_receipt.node(i).key_in_domain(linked_receipt.key))
            by {
                assert(linked_receipt.node(i) == receipt.path.lines[i].node);
            };
        }

        assert forall |i: int| 0 <= i < linked_receipt.lines.len() - 1
            implies #[trigger] linked_receipt.child_linked_at(i)
        by {
            assert(linked_receipt.node(i) == receipt.path.lines[i].node);
            if i < line_count - 1 {
                loaded_betree_path_wf_child(receipt.path, i);
                assert(Path{linked, key: receipt.path.key, depth: (i + 1) as nat}.valid());
                assert(linked_receipt.lines[i + 1].linked.root
                    == Some(receipt.path.lines[i + 1].addr));
            } else {
                assert(i == line_count - 1);
                assert(receipt.path.lines[i].node.child_ptr(receipt.path.key) is None);
            }
        };

        assert forall |i: int| 0 <= i < linked_receipt.lines.len() - 1
            implies #[trigger] linked_receipt.result_linked_at(i)
        by {
            let node = receipt.path.lines[i].node;
            let receipts = receipt.buffer_receipts[i];
            assert(branch_receipts_valid(
                node.buffers,
                node.flushed_ofs(receipt.path.key),
                receipts,
                receipt.path.key,
                to_branch_nodes(branch_reads),
            ));
            branch_receipts_match_query_from(
                pre.disk,
                linked.buffer_dv,
                node.buffers,
                node.flushed_ofs(receipt.path.key),
                receipts,
                receipt.path.key,
                branch_reads,
                0,
            );
            if i < line_count - 1 {
                assert(linked_receipt.lines[i + 1].result == receipt.result_at(i + 1));
            } else {
                assert(i == line_count - 1);
                assert(linked_receipt.lines[i + 1].result
                    == Message::Define{value: default_value()});
            }
        };

        assert(linked_receipt.valid_for(linked, receipt.path.key));
        assert(linked_receipt.result() == receipt.result());
        assert(LinkedBetreeVars::State::query(
            pre.i().betree,
            post.i().betree,
            lbl.i(pre)->linked_lbl,
            linked_receipt,
        ));
        assert(LinkedBetreeVars::State::next_by(
            pre.i().betree,
            post.i().betree,
            lbl.i(pre)->linked_lbl,
            LinkedBetreeVars::Step::query(linked_receipt),
        ));
        assert(LinkedBetreeVars::State::next(
            pre.i().betree,
            post.i().betree,
            lbl.i(pre)->linked_lbl,
        ));
    }

    proof fn unchanged_compactor_receipts_preserve_inv(
        pre: Self,
        post: Self,
    )
        requires
            pre.refinement_inv(),
            post.betree.compactors == pre.betree.compactors,
            post.betree.compactor_receipts
                == pre.betree.compactor_receipts,
            post.betree.branch_summary == pre.betree.branch_summary,
            post.visible_sealed_branch_entries()
                == pre.visible_sealed_branch_entries(),
        ensures post.compactor_receipts_inv(),
    {
        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );
        pre.i().inv_branch_summary_finite();
        assert(pre.betree.branch_summary.dom().finite());
        assert(post.betree.compactor_receipts.len()
            == post.betree.compactors.len());
        assert forall |idx: int|
            0 <= idx < post.betree.compactors.len()
            implies {
                let receipt = #[trigger]
                    post.betree.compactor_receipts[idx];
                &&& receipt.dom() <= addresses_in_aus(
                    post.betree.compactor_input_aus(idx),
                )
                &&& BranchDiskView { entries: receipt }
                    .agrees_with_disk(BranchDiskView {
                        entries: to_branch_nodes(post.disk.visible()),
                    })
            }
        by {
            let receipt = pre.betree.compactor_receipts[idx];
            let roots = pre.betree.compactors[idx]
                .input_buffers.addrs.to_set();
            assert(post.betree.compactor_receipts[idx] == receipt);
            assert(post.betree.compactor_input_aus(idx)
                == pre.betree.compactor_input_aus(idx));
            assert(receipt.dom() <= addresses_in_aus(
                pre.betree.compactor_input_aus(idx),
            ));
            summary_aus_restrict_subset(
                pre.betree.branch_summary,
                to_aus(roots),
            );
            assert(pre.betree.compactor_input_aus(idx)
                <= summary_aus(pre.betree.branch_summary));
            assert(addresses_in_aus(
                pre.betree.compactor_input_aus(idx),
            ) <= sealed_addrs) by {
                assert forall |addr: Address|
                    #[trigger] addresses_in_aus(
                        pre.betree.compactor_input_aus(idx),
                    ).contains(addr)
                    implies sealed_addrs.contains(addr)
                by {
                }
            }
            assert(BranchDiskView { entries: receipt }
                .agrees_with_disk(BranchDiskView {
                    entries: to_branch_nodes(post.disk.visible()),
                })) by {
                assert forall |addr: Address|
                    #[trigger] receipt.contains_key(addr)
                        && to_branch_nodes(post.disk.visible())
                            .contains_key(addr)
                    implies receipt[addr]
                        == to_branch_nodes(post.disk.visible())[addr]
                by {
                    assert(sealed_addrs.contains(addr));
                    assert(post.visible_sealed_branch_entries()
                        .contains_key(addr));
                    assert(post.visible_sealed_branch_entries()[addr]
                        == to_branch_nodes(post.disk.visible())[addr]);
                    assert(pre.visible_sealed_branch_entries()
                        .contains_key(addr));
                    assert(pre.visible_sealed_branch_entries()[addr]
                        == to_branch_nodes(pre.disk.visible())[addr]);
                    assert(to_branch_nodes(pre.disk.visible())
                        .contains_key(addr));
                    assert(to_branch_nodes(post.disk.visible())[addr]
                        == to_branch_nodes(pre.disk.visible())[addr]);
                    assert(BranchDiskView { entries: receipt }
                        .agrees_with_disk(BranchDiskView {
                            entries: to_branch_nodes(pre.disk.visible()),
                        }));
                }
            }
        }
    }

    proof fn unchanged_compactor_receipts_preserve_selected_views(
        pre: Self,
        post: Self,
    )
        requires
            pre.compactor_receipts_inv(),
            post.betree.compactors == pre.betree.compactors,
            post.betree.compactor_receipts
                == pre.betree.compactor_receipts,
            forall |idx: int|
                0 <= idx < pre.betree.compactors.len()
                ==> {
                    let aus = #[trigger]
                        pre.betree.compactor_input_aus(idx);
                    &&& post.betree.compactor_input_aus(idx) == aus
                    &&& to_branch_nodes(post.disk.visible()).restrict(
                        addresses_in_aus(aus),
                    ) == to_branch_nodes(pre.disk.visible()).restrict(
                        addresses_in_aus(aus),
                    )
                },
        ensures post.compactor_receipts_inv(),
    {
        assert(post.betree.compactor_receipts.len()
            == post.betree.compactors.len());
        assert forall |idx: int|
            0 <= idx < post.betree.compactors.len()
            implies {
                let receipt = #[trigger]
                    post.betree.compactor_receipts[idx];
                &&& receipt.dom() <= addresses_in_aus(
                    post.betree.compactor_input_aus(idx),
                )
                &&& BranchDiskView { entries: receipt }
                    .agrees_with_disk(BranchDiskView {
                        entries: to_branch_nodes(post.disk.visible()),
                    })
            }
        by {
            let receipt = pre.betree.compactor_receipts[idx];
            let aus = pre.betree.compactor_input_aus(idx);
            let addrs = addresses_in_aus(aus);
            assert(post.betree.compactor_receipts[idx] == receipt);
            assert(post.betree.compactor_input_aus(idx) == aus);
            assert(receipt.dom() <= addrs);
            assert(BranchDiskView { entries: receipt }
                .agrees_with_disk(BranchDiskView {
                    entries: to_branch_nodes(post.disk.visible()),
                })) by {
                assert forall |addr: Address|
                    #[trigger] receipt.contains_key(addr)
                        && to_branch_nodes(post.disk.visible())
                            .contains_key(addr)
                    implies receipt[addr]
                        == to_branch_nodes(post.disk.visible())[addr]
                by {
                    assert(addrs.contains(addr));
                    assert(to_branch_nodes(post.disk.visible()).restrict(
                        addrs,
                    ).contains_key(addr));
                    assert(to_branch_nodes(pre.disk.visible()).restrict(
                        addrs,
                    ).contains_key(addr));
                    assert(to_branch_nodes(post.disk.visible()).restrict(
                        addrs,
                    )[addr] == to_branch_nodes(post.disk.visible())[addr]);
                    assert(to_branch_nodes(pre.disk.visible()).restrict(
                        addrs,
                    )[addr] == to_branch_nodes(pre.disk.visible())[addr]);
                    assert(to_branch_nodes(post.disk.visible())[addr]
                        == to_branch_nodes(pre.disk.visible())[addr]);
                }
            }
        }
    }

    proof fn removed_compactor_receipt_preserves_selected_views(
        pre: Self,
        post: Self,
        removed_idx: int,
    )
        requires
            pre.compactor_receipts_inv(),
            0 <= removed_idx < pre.betree.compactors.len(),
            post.betree.compactors
                == pre.betree.compactors.remove(removed_idx),
            post.betree.compactor_receipts
                == pre.betree.compactor_receipts.remove(removed_idx),
            forall |idx: int|
                0 <= idx < post.betree.compactors.len()
                ==> {
                    let pre_idx = if idx < removed_idx {
                        idx
                    } else {
                        idx + 1
                    };
                    let aus = pre.betree.compactor_input_aus(pre_idx);
                    &&& (#[trigger] post.betree.compactor_input_aus(idx))
                        == aus
                    &&& to_branch_nodes(post.disk.visible()).restrict(
                        addresses_in_aus(aus),
                    ) == to_branch_nodes(pre.disk.visible()).restrict(
                        addresses_in_aus(aus),
                    )
                },
        ensures post.compactor_receipts_inv(),
    {
        assert(post.betree.compactor_receipts.len()
            == post.betree.compactors.len());
        assert forall |idx: int|
            0 <= idx < post.betree.compactors.len()
            implies {
                let receipt = #[trigger]
                    post.betree.compactor_receipts[idx];
                &&& receipt.dom() <= addresses_in_aus(
                    post.betree.compactor_input_aus(idx),
                )
                &&& BranchDiskView { entries: receipt }
                    .agrees_with_disk(BranchDiskView {
                        entries: to_branch_nodes(post.disk.visible()),
                    })
            }
        by {
            let pre_idx = if idx < removed_idx { idx } else { idx + 1 };
            let receipt = pre.betree.compactor_receipts[pre_idx];
            let aus = pre.betree.compactor_input_aus(pre_idx);
            let addrs = addresses_in_aus(aus);
            assert(post.betree.compactor_receipts[idx] == receipt);
            assert(post.betree.compactor_input_aus(idx) == aus);
            assert(receipt.dom() <= addrs);
            assert(BranchDiskView { entries: receipt }
                .agrees_with_disk(BranchDiskView {
                    entries: to_branch_nodes(post.disk.visible()),
                })) by {
                assert forall |addr: Address|
                    #[trigger] receipt.contains_key(addr)
                        && to_branch_nodes(post.disk.visible())
                            .contains_key(addr)
                    implies receipt[addr]
                        == to_branch_nodes(post.disk.visible())[addr]
                by {
                    assert(addrs.contains(addr));
                    assert(to_branch_nodes(post.disk.visible()).restrict(
                        addrs,
                    ).contains_key(addr));
                    assert(to_branch_nodes(pre.disk.visible()).restrict(
                        addrs,
                    ).contains_key(addr));
                    assert(to_branch_nodes(post.disk.visible()).restrict(
                        addrs,
                    )[addr] == to_branch_nodes(post.disk.visible())[addr]);
                    assert(to_branch_nodes(pre.disk.visible()).restrict(
                        addrs,
                    )[addr] == to_branch_nodes(pre.disk.visible())[addr]);
                    assert(to_branch_nodes(post.disk.visible())[addr]
                        == to_branch_nodes(pre.disk.visible())[addr]);
                }
            }
        }
    }

    proof fn removed_compactor_receipt_preserves_inv(
        pre: Self,
        post: Self,
        removed_idx: int,
    )
        requires
            pre.refinement_inv(),
            0 <= removed_idx < pre.betree.compactors.len(),
            post.betree.compactors
                == pre.betree.compactors.remove(removed_idx),
            post.betree.compactor_receipts
                == pre.betree.compactor_receipts.remove(removed_idx),
            forall |au: AU|
                #[trigger] read_ref_aus(post.betree.compactors).contains(au)
                ==>
                    post.betree.branch_summary.contains_key(au)
                    && pre.betree.branch_summary.contains_key(au)
                    && post.betree.branch_summary[au]
                        == pre.betree.branch_summary[au],
            post.betree.branch_summary.dom().finite(),
            to_branch_nodes(post.disk.visible()).restrict(
                addresses_in_aus(summary_aus(
                    post.betree.branch_summary,
                )),
            ) == to_branch_nodes(pre.disk.visible()).restrict(
                addresses_in_aus(summary_aus(
                    post.betree.branch_summary,
                )),
            ),
        ensures post.compactor_receipts_inv(),
    {
        let post_summary_aus = summary_aus(post.betree.branch_summary);
        assert forall |idx: int|
            0 <= idx < post.betree.compactors.len()
            implies {
                let pre_idx = if idx < removed_idx {
                    idx
                } else {
                    idx + 1
                };
                let input_aus = pre.betree.compactor_input_aus(pre_idx);
                &&& (#[trigger] post.betree.compactor_input_aus(idx))
                    == input_aus
                &&& to_branch_nodes(post.disk.visible()).restrict(
                    addresses_in_aus(input_aus),
                ) == to_branch_nodes(pre.disk.visible()).restrict(
                    addresses_in_aus(input_aus),
                )
            }
        by {
            let pre_idx = if idx < removed_idx { idx } else { idx + 1 };
            let roots = post.betree.compactors[idx]
                .input_buffers.addrs.to_set();
            let root_aus = to_aus(roots);
            let root_sets = Seq::new(
                post.betree.compactors.len(),
                |i: int| post.betree.compactors[i]
                    .input_buffers.addrs.to_set(),
            );
            assert(post.betree.compactors[idx]
                == pre.betree.compactors[pre_idx]);
            crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                root_sets,
                idx,
            );
            crate::disk::GenericDisk_v::to_aus_preserves_lte(
                roots,
                CompactorInput::input_roots(post.betree.compactors),
            );
            assert(root_aus <= read_ref_aus(post.betree.compactors)) by {
                assert forall |au: AU| #[trigger] root_aus.contains(au)
                    implies read_ref_aus(post.betree.compactors).contains(au)
                by {
                    let root = choose |root: Address|
                        roots.contains(root) && root.au == au;
                    assert(CompactorInput::input_roots(
                        post.betree.compactors,
                    ).contains(root));
                }
            }
            assert(post.betree.branch_summary.restrict(root_aus)
                == pre.betree.branch_summary.restrict(root_aus)) by {
                assert_maps_equal!(
                    post.betree.branch_summary.restrict(root_aus),
                    pre.betree.branch_summary.restrict(root_aus),
                    au => {}
                );
            }
            assert(post.betree.compactor_input_aus(idx)
                == pre.betree.compactor_input_aus(pre_idx));
            summary_aus_restrict_subset(
                post.betree.branch_summary,
                root_aus,
            );
            let input_aus = pre.betree.compactor_input_aus(pre_idx);
            assert(input_aus <= post_summary_aus);
            assert(addresses_in_aus(input_aus)
                <= addresses_in_aus(post_summary_aus)) by {
                assert forall |addr: Address|
                    #[trigger] addresses_in_aus(input_aus).contains(addr)
                    implies addresses_in_aus(post_summary_aus)
                        .contains(addr)
                by {
                }
            }
            map_restrict_equal_on_subset(
                to_branch_nodes(post.disk.visible()),
                to_branch_nodes(pre.disk.visible()),
                addresses_in_aus(post_summary_aus),
                addresses_in_aus(input_aus),
            );
        }
        Self::removed_compactor_receipt_preserves_selected_views(
            pre,
            post,
            removed_idx,
        );
    }

    proof fn disk_internal_stutters(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_disk: CachingDisk::State,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::disk_internal(
                pre,
                post,
                lbl,
                new_disk,
            ),
        ensures
            post.i() == pre.i(),
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::internal_noop(
                pre.i(), post.i(), lbl.i(pre),
            ),
    {
        CachingDisk::State::internal_visible_unchanged(pre.disk, new_disk);
        assert(post.disk.visible() == pre.disk.visible());
        assert(post.betree == pre.betree);
        assert(post.visible_betree_entries() == pre.visible_betree_entries());
        assert(post.visible_sealed_branch_entries()
            == pre.visible_sealed_branch_entries());
        assert(post.wip_branches_i() == pre.wip_branches_i());
        assert(post.i() == pre.i());
        assert(post.staged_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_building()
                implies #[trigger]
                    post.betree.wip_branches[idx].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[idx]
                                    .mini_allocator,
                            ),
                        ) by {
                assert(post.betree.wip_branches[idx]
                    == pre.betree.wip_branches[idx]);
                assert(pre.betree.wip_branches[idx].staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            pre.betree.wip_branches[idx]
                                .mini_allocator,
                        ),
                    ));
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[idx].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[idx].mini_allocator,
                        ),
                    ) by {
                assert(post.betree.wip_branches[idx]
                    == pre.betree.wip_branches[idx]);
            }
        }
        assert(post.compactor_receipts_inv());
    }

    proof fn internal_noop_stutters(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_noop(pre, post, lbl),
        ensures
            post.i() == pre.i(),
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::internal_noop(
                pre.i(), post.i(), lbl.i(pre),
            ),
    {
        assert(post == pre);
        assert(post.staged_nodes_inv());
        assert(post.sealed_wip_nodes_inv());
        assert(post.compactor_receipts_inv());
    }

    pub proof fn reclaim_guarded_aus_refines_stutter(
        pre: Self,
        post: Self,
        deallocs: Set<AU>,
        guard_aus: Set<AU>,
    )
        requires
            pre.refinement_inv(),
            reclaim_guarded_aus(pre, post, deallocs, guard_aus),
            (deallocs - guard_aus).disjoint(pre.betree.owned_aus()),
        ensures
            post.i() == pre.i(),
            post.refinement_inv(),
    {
        let aus = deallocs - guard_aus;
        let betree_addrs =
            addresses_in_aus(pre.betree.betree_aus.dom());
        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );
        assert(aus.disjoint(pre.betree.betree_aus.dom()));
        assert(aus.disjoint(summary_aus(pre.betree.branch_summary)));
        addresses_in_aus_preserves_disjointness(
            aus,
            pre.betree.betree_aus.dom(),
        );
        addresses_in_aus_preserves_disjointness(
            aus,
            summary_aus(pre.betree.branch_summary),
        );
        disk_forget_visible_outside_aus(
            pre.disk, post.disk, aus, betree_addrs,
        );
        disk_forget_visible_outside_aus(
            pre.disk, post.disk, aus, sealed_addrs,
        );
        to_betree_nodes_restrict_agrees(
            post.disk.visible(), pre.disk.visible(), betree_addrs,
        );
        to_branch_nodes_restrict_agrees(
            post.disk.visible(), pre.disk.visible(), sealed_addrs,
        );
        assert(post.visible_betree_entries()
            == pre.visible_betree_entries());
        assert(post.visible_sealed_branch_entries()
            == pre.visible_sealed_branch_entries());
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i(),
            idx => {
                let cached = pre.betree.wip_branches[idx];
                let allocated = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                let allocator_sets = Seq::new(
                    pre.betree.wip_branches.len(),
                    |i: int| pre.betree.wip_branches[i]
                        .mini_allocator.all_aus(),
                );
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached_bulk_branch_alloc_aus(
                    pre.betree.wip_branches,
                ) <= pre.betree.owned_aus());
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    aus,
                    cached.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk, post.disk, aus, allocated,
                );
                to_branch_nodes_restrict_agrees(
                    post.disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        );
        assert(post.i() == pre.i());
        assert(post.betree == pre.betree);
        assert(post.staged_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_building()
                implies #[trigger]
                    post.betree.wip_branches[idx].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[idx]
                                    .mini_allocator,
                            ),
                        ) by {
                let cached = pre.betree.wip_branches[idx];
                let allocated = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                let allocator_sets = Seq::new(
                    pre.betree.wip_branches.len(),
                    |i: int| pre.betree.wip_branches[i]
                        .mini_allocator.all_aus(),
                );
                assert(post.betree.wip_branches[idx] == cached);
                assert(cached.is_building());
                assert(cached.staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        allocated,
                    ));
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached_bulk_branch_alloc_aus(
                    pre.betree.wip_branches,
                ) <= pre.betree.owned_aus());
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    aus,
                    cached.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk,
                    post.disk,
                    aus,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    post.disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[idx].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[idx].mini_allocator,
                        ),
                    ) by {
                let cached = pre.betree.wip_branches[idx];
                let allocated = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                let allocator_sets = Seq::new(
                    pre.betree.wip_branches.len(),
                    |i: int| pre.betree.wip_branches[i]
                        .mini_allocator.all_aus(),
                );
                assert(post.betree.wip_branches[idx] == cached);
                assert(cached.is_sealed());
                assert(cached.sealed_branch().disk_view.entries
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        allocated,
                    ));
                crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                    allocator_sets,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= cached_bulk_branch_alloc_aus(
                        pre.betree.wip_branches,
                    ));
                assert(cached_bulk_branch_alloc_aus(
                    pre.betree.wip_branches,
                ) <= pre.betree.owned_aus());
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    aus,
                    cached.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk,
                    post.disk,
                    aus,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    post.disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        }
        Self::unchanged_compactor_receipts_preserve_inv(pre, post);
        reclaim_guarded_aus_preserves_inv(
            pre,
            post,
            deallocs,
            guard_aus,
        );
        assert(post.refinement_inv());
    }

    pub proof fn internal_betree_unchanged_preserves_i(
        pre: Self,
        post: Self,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::next(
                pre,
                post,
                CachingDiskBranchBetree::Label::Internal,
            ),
            post.betree == pre.betree,
        ensures
            post.refinement_inv(),
            post.i() == pre.i(),
    {
        reveal(CachingDiskBranchBetree::State::next);
        reveal(CachingDiskBranchBetree::State::next_by);
        let step = choose |step: CachingDiskBranchBetree::Step|
            CachingDiskBranchBetree::State::next_by(
                pre,
                post,
                CachingDiskBranchBetree::Label::Internal,
                step,
            );
        match step {
            CachingDiskBranchBetree::Step::disk_internal(new_disk) => {
                Self::disk_internal_stutters(
                    pre,
                    post,
                    CachingDiskBranchBetree::Label::Internal,
                    new_disk,
                );
            }
            CachingDiskBranchBetree::Step::internal_noop() => {
                Self::internal_noop_stutters(
                    pre,
                    post,
                    CachingDiskBranchBetree::Label::Internal,
                );
            }
            _ => {
                assert(false);
            }
        }
        CachingDiskBranchBetree::State::inv_next(
            pre,
            post,
            CachingDiskBranchBetree::Label::Internal,
        );
        assert(post.refinement_inv());
    }

    proof fn put_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::put(
                pre,
                post,
                lbl,
                new_betree,
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::au_likes_noop(
                pre.i(),
                post.i(),
                lbl.i(pre),
                post.i().betree,
            ),
    {
        CachingDiskBranchBetree::State::put_effect(
            pre, post, lbl, new_betree,
        );
        reveal(CachedBranchBetree::State::next);
        reveal(CachedBranchBetree::State::next_by);
        let cached_step = choose |cached_step: CachedBranchBetree::Step|
            CachedBranchBetree::State::next_by(
                pre.betree, new_betree, lbl.cached_i(), cached_step,
            );
        match cached_step {
            CachedBranchBetree::Step::put() => {},
            _ => { assert(false); },
        }
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);

        assert(post.disk == pre.disk);
        assert(post.linked_i() == pre.linked_i());
        assert(post.wip_branches_i() == pre.wip_branches_i());
        assert(post.staged_nodes_inv());
        assert(post.sealed_wip_nodes_inv());
        assert(post.compactor_receipts_inv());
        assert(LinkedBetreeVars::State::next_by(
            pre.i().betree,
            post.i().betree,
            lbl.i(pre)->linked_lbl,
            LinkedBetreeVars::Step::put(),
        ));
        assert(LinkedBetreeVars::State::next(
            pre.i().betree,
            post.i().betree,
            lbl.i(pre)->linked_lbl,
        ));
    }

    proof fn freeze_as_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::freeze_as(pre, post, lbl),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::au_likes_noop(
                pre.i(),
                post.i(),
                lbl.i(pre),
                post.i().betree,
            ),
    {
        CachingDiskBranchBetree::State::freeze_as_effect(pre, post, lbl);
        reveal(CachedBranchBetree::State::next);
        reveal(CachedBranchBetree::State::next_by);
        let cached_step = choose |cached_step: CachedBranchBetree::Step|
            CachedBranchBetree::State::next_by(
                pre.betree, pre.betree, lbl.cached_i(), cached_step,
            );
        match cached_step {
            CachedBranchBetree::Step::freeze_as() => {},
            _ => { assert(false); },
        }
        reveal(LinkedBetreeVars::State::next);
        reveal(LinkedBetreeVars::State::next_by);

        assert(post == pre);
        assert(post.staged_nodes_inv());
        assert(post.sealed_wip_nodes_inv());
        assert(post.compactor_receipts_inv());
        assert(LinkedBetreeVars::State::next_by(
            pre.i().betree,
            post.i().betree,
            lbl.i(pre)->linked_lbl,
            LinkedBetreeVars::Step::freeze_as(),
        ));
        assert(LinkedBetreeVars::State::next(
            pre.i().betree,
            post.i().betree,
            lbl.i(pre)->linked_lbl,
        ));
    }

    proof fn grow_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        new_root_addr: Address,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::grow(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                new_root_addr,
                access.loaded_betree_writes(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            access.writes().dom() <= addresses_in_aus(lbl.allocs()),
            AllocationBranchBetree::State::internal_grow(
                pre.i(),
                post.i(),
                lbl.i(pre),
                post.i().betree,
                new_root_addr,
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        access.cached_only_betree_is_only_betree();

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let pre_tree = pre.tight_betree_i();
        let grown_tree = pre_tree.grow(new_root_addr);
        let pre_linked = pre.linked_i();
        let grown = pre_linked.grow(new_root_addr);
        let grown_vars = LinkedBetreeVars::State {
            memtable: pre.betree.memtable,
            linked: grown,
        };
        let witness = disk_access_for_alloc_witness(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
        );

        pre.linked_i_is_tight_candidate();
        assert(allocs == set![new_root_addr.au]);
        assert(deallocs.is_empty());
        assert(access.only_betree());
        assert(access.loaded_betree_writes()
            == grow_writes(pre.betree.root, new_root_addr));
        assert(to_betree_nodes(writes)
            == grow_writes(pre.betree.root, new_root_addr));
        assert(writes.dom() == set![new_root_addr]);
        assert(writes.dom() <= addresses_in_aus(allocs));
        pre.wip_alloc_aus_agree();
        assert(pre.i().is_fresh(allocs));

        assert(pre_linked.dv.is_fresh(set![new_root_addr])) by {
            assert(pre_linked.dv.entries.dom()
                <= addresses_in_aus(pre.betree.betree_aus.dom()));
            assert(pre.betree.betree_aus.dom().disjoint(allocs));
        }
        assert(LinkedBetreeVars::State::internal_grow(
            pre.i().betree,
            grown_vars,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            new_root_addr,
        ));
        LinkedBetreeVars::State::internal_grow_inductive(
            pre.i().betree,
            grown_vars,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            new_root_addr,
        );
        assert(grown.inv());
        grow_preserves_tight_domain(pre_tree, new_root_addr);

        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );
        addresses_in_aus_preserves_disjointness(
            summary_aus(pre.betree.branch_summary),
            allocs,
        );
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            sealed_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            sealed_addrs,
        );
        assert(post.visible_sealed_branch_disk()
            == pre.visible_sealed_branch_disk());

        let old_addrs = addresses_in_aus(pre.betree.betree_aus.dom());
        addresses_in_aus_preserves_disjointness(
            pre.betree.betree_aus.dom(),
            allocs,
        );
        disk_extend_visible_outside_allocs(
            pre.disk,
            witness.expanded,
            allocs,
            old_addrs,
        );
        to_betree_nodes_restrict_agrees(
            witness.expanded.visible(),
            pre.disk.visible(),
            old_addrs,
        );

        assert(grown.dv.entries <= post.visible_betree_entries()) by {
            assert forall |addr: Address| #[trigger] grown.dv.entries.contains_key(addr)
                implies post.visible_betree_entries().contains_key(addr)
                    && grown.dv.entries[addr] == post.visible_betree_entries()[addr]
            by {
                assert(post.betree.betree_aus.dom()
                    == pre.betree.betree_aus.dom().insert(new_root_addr.au));
                assert(addresses_in_aus(post.betree.betree_aus.dom()).contains(addr)) by {
                    if addr == new_root_addr {
                    } else {
                        assert(pre_linked.dv.entries.contains_key(addr));
                        assert(addresses_in_aus(pre.betree.betree_aus.dom()).contains(addr));
                    }
                }
                if addr == new_root_addr {
                    assert(writes.contains_key(addr));
                    assert(witness.accessed.visible().contains_key(addr));
                    assert(witness.accessed.visible()[addr] == writes[addr]);
                    assert(new_disk.visible().contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible())[addr]
                        == to_betree_nodes(writes)[addr]);
                } else {
                    assert(pre_linked.dv.entries.contains_key(addr));
                    assert(pre_linked.dv.entries <= pre.visible_betree_entries());
                    assert(pre.visible_betree_entries().contains_key(addr));
                    assert(pre_linked.dv.entries[addr]
                        == pre.visible_betree_entries()[addr]);
                    assert(to_betree_nodes(pre.disk.visible()).restrict(old_addrs)
                        .contains_key(addr));
                    assert(old_addrs.contains(addr));
                    assert(pre.disk.visible().restrict(old_addrs).contains_key(addr));
                    assert(witness.expanded.visible().restrict(old_addrs).contains_key(addr));
                    assert(!writes.contains_key(addr));
                    assert(witness.expanded.visible().contains_key(addr));
                    assert(witness.accessed.visible()[addr]
                        == witness.expanded.visible()[addr]);
                    assert(new_disk.visible()[addr]
                        == witness.accessed.visible()[addr]);
                    assert(pre_linked.dv.entries[addr]
                        == to_betree_nodes(witness.expanded.visible())[addr]) by {
                        assert(to_betree_nodes(pre.disk.visible()).restrict(old_addrs)[addr]
                            == to_betree_nodes(witness.expanded.visible()).restrict(old_addrs)[addr]);
                    }
                }
            }
        }
        assert(tight_betree_candidate(
            post.betree.root,
            post.visible_betree_entries(),
            grown_tree,
        ));
        tight_betree_of_equals_candidate(
            post.betree.root,
            post.visible_betree_entries(),
            grown_tree,
        );
        assert(post.tight_betree_i() == grown_tree);
        assert(post.semantic_branch_roots() == pre.semantic_branch_roots()) by {
            assert(post.betree.compactors == pre.betree.compactors);
            assert(grown_tree.reachable_buffer_addrs()
                == pre_tree.reachable_buffer_addrs());
        }
        assert(post.betree.branch_summary == pre.betree.branch_summary);
        assert(post.semantic_sealed_branch_disk()
            == pre.semantic_sealed_branch_disk());
        assert(post.linked_i() == grown);

        assert_seqs_equal!(post.wip_branches_i(), pre.wip_branches_i(), idx => {
            let cached = pre.betree.wip_branches[idx];
            let allocated = mini_allocator_allocated_addrs(cached.mini_allocator);
            mini_allocator_allocated_addrs_subset_all_aus(cached.mini_allocator);
            AllocationBulkBranch::alloc_aus_ensures(pre.i().wip_branches, idx);
            assert(cached.mini_allocator.all_aus()
                <= cached_bulk_branch_alloc_aus(pre.betree.wip_branches));
            assert(allocs.disjoint(cached.mini_allocator.all_aus()));
            addresses_in_aus_preserves_disjointness(
                cached.mini_allocator.all_aus(),
                allocs,
            );
            disk_access_for_alloc_visible_outside_alloc_dealloc(
                pre.disk,
                new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
                allocated,
            );
            to_branch_nodes_restrict_agrees(
                new_disk.visible(),
                pre.disk.visible(),
                allocated,
            );
        });

        assert(post.i().betree == grown_vars);
        assert(post.i().betree_aus == pre.i().betree_aus.insert(new_root_addr.au));
        assert(post.i().branch_aus == pre.i().branch_aus);
        assert(post.i().branch_summary == pre.i().branch_summary);
        assert(post.i().compactors == pre.i().compactors);
        assert(post.i().wip_branches == pre.i().wip_branches);
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(allocs)) by {
            assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
                == pre.i().branch_allocator_aus());
            assert(pre.i().is_fresh(allocs));
        }
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(deallocs));
        Self::unchanged_wips_preserve_staged_nodes_after_access(
            pre,
            post,
            lbl,
            new_disk,
            access,
        );
        Self::unchanged_compactor_receipts_preserve_inv(pre, post);
    }

    proof fn flush_memtable_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        branch_idx: int,
        new_root_addr: Address,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::flush_memtable(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                branch_idx,
                new_root_addr,
                access.loaded_betree_reads(),
                access.loaded_betree_writes(),
                access.loaded_branch_reads(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            access.writes().dom() <= addresses_in_aus(lbl.allocs()),
            AllocationBranchBetree::State::internal_flush_memtable(
                pre.i(),
                post.i(),
                lbl.i(pre),
                post.i().betree,
                branch_idx,
                new_root_addr,
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        access.cached_wf_is_wf();
        access.cached_branch_writes_empty();

        pre.linked_i_is_tight_candidate();
        assert(post.disk == new_disk);
        assert(post.betree == new_betree);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let betree_reads = access.loaded_betree_reads();
        let betree_writes = access.loaded_betree_writes();
        let cached_branch = pre.betree.wip_branches[branch_idx];
        let allocation_branch = pre.wip_branch_i(branch_idx);
        let new_branch = cached_branch.sealed_branch();
        let branch_root = new_branch.root;
        let new_addrs = TwoAddrs {
            addr1: new_root_addr,
            addr2: branch_root,
        };
        let pushed = pre.linked_i().push_memtable(
            new_branch.root(),
            new_addrs,
        );
        let witness = disk_access_for_alloc_witness(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
        );

        assert(0 <= branch_idx < pre.betree.wip_branches.len());
        assert(pre.i().wip_branches_inv());
        assert(allocation_branch == pre.i().wip_branches[branch_idx]);
        assert(allocation_branch.inv());
        assert(allocation_branch.is_sealed());
                assert(new_branch.valid_sealed_branch());
        assert(new_branch.tight_disk_view_with_summary());
        assert(cached_branch.sealed_root() == branch_root);
        assert(cached_branch.summary() == new_branch.get_summary());

        let (_, pre_branch_likes) = pre.i().betree.linked.transitive_likes();
        let pre_compactor_roots = CompactorInput::input_roots(
            pre.i().compactors,
        );
        let pre_branch_roots = pre_branch_likes.dom() + pre_compactor_roots;
        CompactorInput::input_roots_finite(pre.i().compactors);
        pre.i().betree.linked.buffer_dv
            .build_branch_summary_finite(pre_branch_roots);
        assert(pre.i().branch_summary =~=
            pre.i().betree.linked.buffer_dv
                .build_branch_summary(pre_branch_roots));
        assert(pre.betree.branch_summary.values().finite());

        assert(allocs == set![new_root_addr.au]);
        assert(access.branch_writes.is_empty());
        assert(betree_reads == to_betree_nodes(access.betree_reads));
        assert(betree_writes == to_betree_nodes(writes));
        assert(betree_writes == crate::implementation::CachedBranchBetree_v::flush_memtable_writes(
            pre.betree.root,
            branch_root,
            new_root_addr,
            betree_reads,
        ));
        assert(writes.dom() == set![new_root_addr]);
        assert(writes.dom() <= addresses_in_aus(allocs));
        pre.wip_alloc_aus_agree();
        assert(pre.i().is_fresh(allocs));

        let branch_allocated = mini_allocator_allocated_addrs(
            cached_branch.mini_allocator,
        );
        mini_allocator_allocated_addrs_subset_all_aus(
            cached_branch.mini_allocator,
        );
        AllocationBulkBranch::alloc_aus_ensures(
            pre.i().wip_branches,
            branch_idx,
        );
        assert(cached_branch.mini_allocator.all_aus()
            <= pre.i().branch_allocator_aus());
        assert(pre.i().betree_aus.dom()
            .disjoint(pre.i().branch_allocator_aus()));
        assert(cached_branch.mini_allocator.all_aus().disjoint(allocs));
        assert(cached_branch.mini_allocator.all_aus().disjoint(deallocs)) by {
            assert(deallocs <= pre.betree.betree_aus.dom());
        };
        addresses_in_aus_preserves_disjointness(
            cached_branch.mini_allocator.all_aus(),
            allocs,
        );
        addresses_in_aus_preserves_disjointness(
            cached_branch.mini_allocator.all_aus(),
            deallocs,
        );
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            branch_allocated,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            branch_allocated,
        );

        let post_loose = visible_branch_disk(
            new_disk,
            new_betree.branch_summary,
        );
        let branch_loose = loose_disk_for_summary(
            post_loose,
            cached_branch.summary(),
        );
        assert(tight_branch_in_loose_disk(
            branch_loose,
            branch_root,
            cached_branch.summary(),
            new_branch,
        )) by {
            assert(new_branch.get_summary() == cached_branch.summary());
            assert(new_branch.disk_view.entries <= branch_loose.entries) by {
                assert forall |addr: Address|
                    #[trigger] new_branch.disk_view.entries.contains_key(addr)
                    implies branch_loose.entries.contains_key(addr)
                        && branch_loose.entries[addr]
                            == new_branch.disk_view.entries[addr]
                by {
                    assert(allocation_branch.sealed_branch().disk_view.entries
                        == to_branch_nodes(pre.disk.visible()).restrict(
                            branch_allocated,
                        ));
                    assert(branch_allocated.contains(addr));
                    assert(to_branch_nodes(new_disk.visible()).restrict(
                        branch_allocated,
                    )[addr] == new_branch.disk_view.entries[addr]);
                    assert(new_betree.branch_summary.contains_key(branch_root.au));
                    assert(new_betree.branch_summary[branch_root.au]
                        == cached_branch.summary());
                    assert(new_betree.branch_summary == post.i().branch_summary);
                    assert(new_betree.branch_summary
                        == pre.betree.branch_summary.insert(
                            branch_root.au,
                            cached_branch.summary(),
                        ));
                    lemma_values_finite(new_betree.branch_summary);
                    assert(new_betree.branch_summary.values().finite());
                    assert(summary_aus(new_betree.branch_summary)
                        .contains(addr.au)) by {
                        assert(new_betree.branch_summary.values()
                            .contains(cached_branch.summary()));
                        assert(new_betree.branch_summary.values()
                            .contains(cached_branch.summary()));
                        crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                            new_betree.branch_summary.values(),
                            cached_branch.summary(),
                        );
                        assert(summary_aus(new_betree.branch_summary)
                            .contains(addr.au));
                    };
                    assert(post_loose.entries.contains_key(addr));
                    assert(addresses_in_aus(cached_branch.summary())
                        .contains(addr));
                };
            };
        };
        tight_branch_of_equals_candidate(
            branch_loose,
            branch_root,
            cached_branch.summary(),
            new_branch,
        );
        assert(tight_branch_of(
            branch_loose,
            branch_root,
            cached_branch.summary(),
        ) == new_branch);
        if pre.betree.root is Some {
            let old_root = pre.betree.root.unwrap();
            assert(betree_reads.contains_key(old_root));
            assert(access.betree_reads.contains_key(old_root));
            assert(!access.branch_reads.contains_key(old_root)) by {
                assert(access.betree_reads.dom().disjoint(
                    access.branch_reads.dom(),
                ));
            };
            assert(reads.contains_key(old_root));
            assert(reads[old_root] == access.betree_reads[old_root]);
            assert(!allocs.contains(old_root.au));
            assert(!addresses_in_aus(allocs).contains(old_root));
            assert(witness.expanded.cache.contains_key(old_root));
            assert(pre.disk.cache.contains_key(old_root)) by {
                if !pre.disk.cache.contains_key(old_root) {
                    assert((witness.expanded.cache.dom() - pre.disk.cache.dom())
                        .contains(old_root));
                }
            };
            assert(witness.expanded.cache[old_root] == pre.disk.cache[old_root]);
            assert(reads[old_root] == pre.disk.cache[old_root]);
            assert(pre.tight_betree_i().dv.entries.contains_key(old_root));
            assert(pre.tight_betree_i().dv.entries
                <= pre.visible_betree_entries());
            assert(pre.visible_betree_entries().contains_key(old_root));
            assert(pre.disk.visible().contains_key(old_root));
            let root_read = access.betree_reads.restrict(set![old_root]);
            assert(root_read <= pre.disk.cache);
            betree_read_node_matches_visible(pre.disk, root_read, old_root);
            assert(root_read[old_root] == access.betree_reads[old_root]);
            assert(betree_reads[old_root] == pre.tight_betree_i().root());
        }
        assert(betree_writes[new_root_addr] == pushed.root());
        assert(writes.contains_key(new_root_addr));

        let loaded_branch = loaded_sealed_branch(
            branch_root,
            access.loaded_branch_reads().restrict(
                addresses_in_aus(cached_branch.summary()),
            ),
        );
        assert(loaded_branch.i().i() == pre.betree.memtable.buffer);
        assert(loaded_branch.valid_sealed_branch());
        assert(loaded_branch.tight_disk_view_with_summary()) by {
            assert(loaded_branch.disk_view.entries.dom()
                <= addresses_in_aus(cached_branch.summary()));
            assert(loaded_branch.disk_view.entries.restrict(
                addresses_in_aus(cached_branch.summary()),
            ) == loaded_branch.disk_view.entries);
            assert(loaded_branch.disk_view.representation()
                == loaded_branch.disk_view.entries.dom());
            assert(loaded_branch.disk_view.entries.dom()
                == loaded_branch.full_repr()) by {
                assert(crate::allocation_layer::Likes_v::restrict_domain_au(
                    loaded_branch.disk_view.entries,
                    cached_branch.summary(),
                ) == loaded_branch.full_repr());
                assert(crate::allocation_layer::Likes_v::restrict_domain_au(
                    loaded_branch.disk_view.entries,
                    cached_branch.summary(),
                ) == loaded_branch.disk_view.entries.dom());
            };
        };
        assert(loaded_branch.get_summary() == cached_branch.summary());
        assert(loaded_branch.disk_view.agrees_with_disk(new_branch.disk_view)) by {
            assert forall |addr: Address|
                #[trigger] loaded_branch.disk_view.entries.contains_key(addr)
                    && new_branch.disk_view.entries.contains_key(addr)
                implies loaded_branch.disk_view.entries[addr]
                    == new_branch.disk_view.entries[addr]
            by {
                assert(access.loaded_branch_reads().contains_key(addr));
                assert(access.branch_reads.contains_key(addr));
                assert(access.reads().contains_key(addr));
                assert(addresses_in_aus(cached_branch.summary()).contains(addr));
                assert(!addresses_in_aus(allocs).contains(addr));
                assert(!addresses_in_aus(deallocs).contains(addr));
                assert(witness.expanded.cache.contains_key(addr));
                assert(pre.disk.cache.contains_key(addr)) by {
                    if !pre.disk.cache.contains_key(addr) {
                        assert((witness.expanded.cache.dom()
                            - pre.disk.cache.dom()).contains(addr));
                    }
                };
                assert(witness.expanded.cache[addr] == pre.disk.cache[addr]);
                assert(access.reads()[addr] == access.branch_reads[addr]) by {
                    assert(!access.betree_reads.contains_key(addr));
                };
                assert(access.branch_reads[addr] == pre.disk.cache[addr]);
                assert(pre.disk.visible().contains_key(addr));
                let one_read = access.branch_reads.restrict(set![addr]);
                assert(one_read <= pre.disk.cache);
                query_read_node_matches_visible(pre.disk, one_read, addr);
                assert(new_branch.disk_view.entries[addr]
                    == to_branch_nodes(pre.disk.visible())[addr]);
                assert(loaded_branch.disk_view.entries[addr]
                    == to_branch_nodes(one_read)[addr]);
            };
        };
        agreeable_branches_same_reachable(
            loaded_branch,
            new_branch,
            loaded_branch.the_ranking(),
            new_branch.the_ranking(),
        );
        assert(loaded_branch.full_repr() == new_branch.full_repr());
        assert(loaded_branch.disk_view.entries.dom()
            == new_branch.disk_view.entries.dom());
        assert(loaded_branch == new_branch) by {
            assert_maps_equal!(
                loaded_branch.disk_view.entries,
                new_branch.disk_view.entries,
                addr => {}
            );
        };
        assert(new_branch.i().i() == pre.betree.memtable.buffer);

        assert(new_addrs.no_duplicates()) by {
            assert(pre.i().branch_allocator_aus().contains(branch_root.au)) by {
                AllocationBulkBranch::alloc_aus_ensures(
                    pre.i().wip_branches,
                    branch_idx,
                );
            };
            assert(pre.i().is_fresh(allocs));
        };
        assert(pre.linked_i().is_fresh(new_addrs.repr())) by {
            assert forall |addr: Address| #[trigger] new_addrs.repr().contains(addr)
                implies !pre.linked_i().dv.entries.contains_key(addr)
                    && !pre.linked_i().buffer_dv.entries.contains_key(addr)
            by {
                if addr == new_root_addr {
                    assert(allocs.contains(addr.au));
                    assert(pre.i().is_fresh(allocs));
                } else {
                    assert(addr == branch_root);
                    AllocationBulkBranch::alloc_aus_ensures(
                        pre.i().wip_branches,
                        branch_idx,
                    );
                    assert(pre.i().branch_allocator_aus().contains(addr.au));
                    assert(pre.i().betree_aus.dom().disjoint(
                        pre.i().branch_allocator_aus(),
                    ));
                    assert(summary_aus(pre.i().branch_summary).disjoint(
                        pre.i().branch_allocator_aus(),
                    ));
                }
            };
        };
        pre.linked_i().push_memtable_ensures(
            new_branch.root(),
            new_addrs,
        );
        assert(pushed.acyclic());

        let model_post_linked = LinkedBetree {
            root: pushed.root,
            dv: pushed.dv,
            buffer_dv: BufferDisk {
                entries: new_branch.disk_view.entries,
            },
        };
        let model_post_vars = LinkedBetreeVars::State {
            memtable: pre.i().betree.memtable.drain(),
            linked: model_post_linked,
        };
        assert(pushed.valid_view(model_post_linked)) by {
            assert(model_post_linked.wf());
            assert(model_post_linked.dv.is_sub_disk(pushed.dv));
            assert(model_post_linked.buffer_dv.agrees_with(pushed.buffer_dv)) by {
                assert forall |addr: Address|
                    #[trigger] model_post_linked.buffer_dv.entries.contains_key(addr)
                        && pushed.buffer_dv.entries.contains_key(addr)
                    implies model_post_linked.buffer_dv.entries[addr]
                        == pushed.buffer_dv.entries[addr]
                by {
                    if addr == branch_root {
                        assert(pushed.buffer_dv.entries[addr]
                            == new_branch.root());
                    } else {
                        assert(pre.linked_i().buffer_dv.entries.contains_key(addr));
                        assert(new_branch.disk_view.entries.contains_key(addr));
                        assert(false) by {
                            assert(pre.i().branch_summary.dom()
                                .disjoint(pre.i().branch_allocator_aus()));
                            assert(pre.i().branch_allocator_aus()
                                .contains(addr.au));
                            assert(summary_aus(pre.i().branch_summary)
                                .contains(addr.au));
                        };
                    }
                };
            };
        };
        assert(new_branch.root().i(
            model_post_linked.buffer_dv,
            branch_root,
        ) == pre.i().betree.memtable.buffer) by {
            assert(new_branch.i().i() == pre.betree.memtable.buffer);
        };
        assert(LinkedBetreeVars::State::internal_flush_memtable(
            pre.i().betree,
            model_post_vars,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            new_branch.root(),
            model_post_linked,
            new_addrs,
        ));
        crate::allocation_layer::LikesBetree_v::LikesBetree::State::push_memtable_likes_ensures(
            pre.i().betree,
            model_post_vars,
            new_branch.root(),
            new_addrs,
        );
        pre.i().betree.internal_flush_memtable_aus_ensures(
            model_post_vars,
            new_branch.root(),
            new_addrs,
        );
        let (pre_tree_likes, _) = pre.linked_i().transitive_likes();
        let (pushed_tree_likes, _) = pushed.transitive_likes();
        assert(pre.i().betree_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                pre_tree_likes,
            ));
        assert(pushed_tree_likes
            == pre_tree_likes.sub(pre.linked_i().root_likes())
                .add(model_post_linked.root_likes()));
        let model_post_betree_aus =
            crate::allocation_layer::Likes_v::to_au_likes(
                pushed_tree_likes,
            );
        let (expected_betree_aus, _) =
            crate::allocation_layer::AllocationBetree_v::AllocationBetree::State::flush_memtable_au_likes(
                pre.i().betree,
                model_post_vars,
                new_addrs,
                pre.i().betree_aus,
                pre.i().branch_aus,
            );
        assert(expected_betree_aus == model_post_betree_aus);
        if pre.linked_i().has_root() {
            crate::allocation_layer::Likes_v::to_au_likes_singleton(
                pre.linked_i().root.unwrap(),
            );
        }
        crate::allocation_layer::Likes_v::to_au_likes_singleton(
            new_root_addr,
        );
        assert(model_post_linked.root_likes()
            == Multiset::singleton(new_root_addr));
        assert(post.betree.betree_aus == expected_betree_aus);
        assert(post.betree.betree_aus == model_post_betree_aus);

        let post_tree = reachable_tight_betree(pushed);
        let stable_tree_aus = pre.betree.betree_aus.dom() - deallocs;
        let stable_tree_addrs = addresses_in_aus(stable_tree_aus);
        assert(stable_tree_aus.disjoint(allocs));
        assert(stable_tree_aus.disjoint(deallocs));
        addresses_in_aus_preserves_disjointness(stable_tree_aus, allocs);
        addresses_in_aus_preserves_disjointness(stable_tree_aus, deallocs);
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            stable_tree_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            stable_tree_addrs,
        );
        let pushed_ranking = pushed.the_ranking();
        pushed.tree_likes_domain(pushed_ranking);
        crate::allocation_layer::Likes_v::to_au_likes_domain(
            pushed_tree_likes,
        );
        assert(post_tree.dv.entries <= post.visible_betree_entries()) by {
            assert forall |addr: Address|
                #[trigger] post_tree.dv.entries.contains_key(addr)
                implies post.visible_betree_entries().contains_key(addr)
                    && post_tree.dv.entries[addr]
                        == post.visible_betree_entries()[addr]
            by {
                assert(pushed.dv.entries.contains_key(addr));
                assert(pushed.reachable_betree_addrs().contains(addr));
                assert(pushed_tree_likes.contains(addr));
                assert(model_post_betree_aus.contains(addr.au));
                assert(post.betree.betree_aus.dom().contains(addr.au));
                assert(addresses_in_aus(post.betree.betree_aus.dom())
                    .contains(addr));
                if addr == new_root_addr {
                    assert(writes.contains_key(addr));
                    assert(to_betree_nodes(writes)[addr] == pushed.dv.entries[addr]);
                    assert(new_disk.visible()[addr] == writes[addr]);
                    assert(to_betree_nodes(new_disk.visible())
                        .contains_key(addr));
                } else {
                    assert(pre.tight_betree_i().dv.entries.contains_key(addr));
                    assert(pushed.dv.entries[addr]
                        == pre.tight_betree_i().dv.entries[addr]);
                    assert(pre.tight_betree_i().dv.entries
                        <= pre.visible_betree_entries());
                    assert(pre.visible_betree_entries().contains_key(addr));
                    assert(to_betree_nodes(pre.disk.visible())
                        .contains_key(addr));
                    assert(pre.betree.betree_aus.dom().contains(addr.au));
                    assert(post.betree.betree_aus.dom().contains(addr.au));
                    assert(!deallocs.contains(addr.au));
                    assert(stable_tree_addrs.contains(addr));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_tree_addrs,
                    )[addr] == to_betree_nodes(pre.disk.visible()).restrict(
                        stable_tree_addrs,
                    )[addr]);
                    assert(to_betree_nodes(pre.disk.visible()).restrict(
                        stable_tree_addrs,
                    ).contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_tree_addrs,
                    ).contains_key(addr));
                    assert(pre.tight_betree_i().dv.entries[addr]
                        == pre.visible_betree_entries()[addr]) by {
                        assert(pre.visible_betree_entries().contains_key(addr));
                    };
                    assert(pre.visible_betree_entries()[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]);
                    assert(to_betree_nodes(pre.disk.visible())
                        .contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible())
                        .contains_key(addr));
                }
                assert(post_tree.dv.entries[addr] == pushed.dv.entries[addr]);
                assert(post.visible_betree_entries().contains_key(addr));
                assert(post.visible_betree_entries()[addr]
                    == to_betree_nodes(new_disk.visible())[addr]);
            };
        };
        reachable_tight_betree_is_candidate(
            pushed,
            post.betree.root,
            post.visible_betree_entries(),
        );
        tight_betree_of_equals_candidate(
            post.betree.root,
            post.visible_betree_entries(),
            post_tree,
        );
        assert(post.tight_betree_i() == post_tree);
        let post_ranking = post_tree.the_ranking();
        agreeable_betrees_same_reachable(
            pushed,
            post_tree,
            pushed_ranking,
            post_ranking,
        );
        assert(pushed.reachable_betree_addrs()
            == post_tree.reachable_betree_addrs());
        assert(post_tree.dv.entries.dom()
            == post_tree.reachable_betree_addrs());
        pushed.reachable_betree_addrs_using_ranking_closed(pushed_ranking);
        assert(pushed.reachable_betree_addrs()
            <= pushed.dv.entries.dom());
        assert(post_tree.dv.is_sub_disk(pushed.dv)) by {
            assert forall |addr: Address|
                #[trigger] post_tree.dv.entries.contains_key(addr)
                implies pushed.dv.entries.contains_key(addr)
                    && post_tree.dv.entries[addr] == pushed.dv.entries[addr]
            by {
                assert(post_tree.reachable_betree_addrs().contains(addr));
                assert(pushed.reachable_betree_addrs().contains(addr));
            };
        };

        pushed.same_reachable_betree_addrs_implies_same_buffer_addrs(
            post_tree,
        );
        assert(pushed.reachable_buffer_addrs()
            == post_tree.reachable_buffer_addrs());
        assert(pushed.reachable_buffer_addrs()
            == pre.linked_i().reachable_buffer_addrs()
                + set![branch_root]);
        assert(pre.linked_i().root == pre.tight_betree_i().root);
        assert(pre.linked_i().dv == pre.tight_betree_i().dv);
        let pre_tree_ranking = pre.tight_betree_i().the_ranking();
        assert(pre.linked_i().valid_ranking(pre_tree_ranking));
        broadcast use LinkedBetree::reachable_betree_addrs_ignore_ranking;
        assert(pre.linked_i().reachable_betree_addrs()
            == pre.linked_i().reachable_betree_addrs_using_ranking(
                pre_tree_ranking,
            ));
        assert(pre.tight_betree_i().reachable_betree_addrs()
            == pre.tight_betree_i().reachable_betree_addrs_using_ranking(
                pre_tree_ranking,
            ));
        agreeable_betrees_same_reachable(
            pre.linked_i(),
            pre.tight_betree_i(),
            pre_tree_ranking,
            pre_tree_ranking,
        );
        assert(pre.linked_i().reachable_betree_addrs()
            == pre.tight_betree_i().reachable_betree_addrs());
        pre.linked_i().same_reachable_betree_addrs_implies_same_buffer_addrs(
            pre.tight_betree_i(),
        );
        assert(pre.linked_i().reachable_buffer_addrs()
            == pre.tight_betree_i().reachable_buffer_addrs());
        assert(pre.tight_betree_i().reachable_buffer_addrs()
                + set![branch_root]
            == pre.tight_betree_i().reachable_buffer_addrs()
                .insert(branch_root));
        assert(post.semantic_branch_roots()
            == pre.semantic_branch_roots().insert(branch_root)) by {
            assert(post.betree.compactors == pre.betree.compactors);
        };

        let pre_sealed_aus = summary_aus(pre.betree.branch_summary);
        let pre_sealed_addrs = addresses_in_aus(pre_sealed_aus);
        assert(pre_sealed_aus.disjoint(allocs));
        assert(pre_sealed_aus.disjoint(deallocs));
        addresses_in_aus_preserves_disjointness(pre_sealed_aus, allocs);
        addresses_in_aus_preserves_disjointness(pre_sealed_aus, deallocs);
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            pre_sealed_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            pre_sealed_addrs,
        );
        assert(post.betree.branch_summary
            == pre.betree.branch_summary.insert(
                branch_root.au,
                new_branch.get_summary(),
            ));
        assert(post.betree.branch_summary.values().finite()) by {
            lemma_values_finite(post.betree.branch_summary);
        };
        let (_, pre_branch_likes) = pre.i().betree.linked.transitive_likes();
        let pre_compactor_roots = CompactorInput::input_roots(
            pre.i().compactors,
        );
        let pre_branch_roots = pre_branch_likes.dom() + pre_compactor_roots;
        CompactorInput::input_roots_finite(pre.i().compactors);
        pre.i().betree.linked.buffer_dv
            .build_branch_summary_finite(pre_branch_roots);
        assert(pre.i().branch_summary =~=
            pre.i().betree.linked.buffer_dv
                .build_branch_summary(pre_branch_roots));
        assert(pre.betree.branch_summary.values().finite());
        assert(!pre.betree.branch_summary.contains_key(branch_root.au)) by {
            pre.i().inv_branch_summary_ensures();
            AllocationBulkBranch::alloc_aus_ensures(
                pre.i().wip_branches,
                branch_idx,
            );
            assert(pre.i().branch_allocator_aus().contains(branch_root.au));
            assert(new_branch.get_summary().contains(branch_root.au));
            assert(new_branch.get_summary()
                == pre.i().wip_branches[branch_idx]
                    .mini_allocator.all_aus());
            assert(summary_aus(pre.i().branch_summary).disjoint(
                pre.i().branch_allocator_aus(),
            ));
            if pre.betree.branch_summary.contains_key(branch_root.au) {
                assert(pre.betree.branch_summary.values().contains(
                    pre.betree.branch_summary[branch_root.au],
                ));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    pre.betree.branch_summary[branch_root.au],
                );
            }
        };
        assert forall |root: Address|
            #[trigger] pre.semantic_branch_roots().contains(root)
            implies {
                &&& pre.betree.branch_summary.contains_key(root.au)
                &&& tight_branch_exists(
                    loose_disk_for_summary(
                        pre.visible_sealed_branch_disk(),
                        pre.betree.branch_summary[root.au],
                    ),
                    root,
                    pre.betree.branch_summary[root.au],
                )
                &&& loose_disk_for_summary(
                    post.visible_sealed_branch_disk(),
                    post.betree.branch_summary[root.au],
                ) == loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    pre.betree.branch_summary[root.au],
                )
            }
        by {
            assert(pre.tight_branches_exist());
            assert(root.au != branch_root.au);
            assert(post.betree.branch_summary[root.au]
                == pre.betree.branch_summary[root.au]);
            assert(pre.betree.branch_summary[root.au] <= pre_sealed_aus) by {
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    pre.betree.branch_summary[root.au],
                );
            };
            assert_maps_equal!(
                loose_disk_for_summary(
                    post.visible_sealed_branch_disk(),
                    post.betree.branch_summary[root.au],
                ).entries,
                loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    pre.betree.branch_summary[root.au],
                ).entries,
                addr => {
                    let summary = pre.betree.branch_summary[root.au];
                    if loose_disk_for_summary(
                        pre.visible_sealed_branch_disk(),
                        summary,
                    ).entries.contains_key(addr) {
                        assert(addresses_in_aus(summary).contains(addr));
                        assert(pre_sealed_addrs.contains(addr));
                        assert(to_branch_nodes(new_disk.visible()).restrict(
                            pre_sealed_addrs,
                        ).contains_key(addr));
                        assert(post.betree.branch_summary.contains_key(root.au));
                        assert(post.betree.branch_summary[root.au] == summary);
                        assert(post.betree.branch_summary.values().contains(summary));
                        assert(summary_aus(post.betree.branch_summary)
                            .contains(addr.au)) by {
                            assert(post.betree.branch_summary.values()
                                .contains(summary));
                            crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                                post.betree.branch_summary.values(),
                                summary,
                            );
                        };
                        assert(post.visible_sealed_branch_disk()
                            .entries.contains_key(addr));
                        assert(loose_disk_for_summary(
                            post.visible_sealed_branch_disk(),
                            summary,
                        ).entries.contains_key(addr));
                    }
                    if addresses_in_aus(summary).contains(addr) {
                        assert(pre_sealed_addrs.contains(addr));
                        assert(to_branch_nodes(new_disk.visible()).restrict(
                            pre_sealed_addrs,
                        )[addr] == to_branch_nodes(pre.disk.visible()).restrict(
                            pre_sealed_addrs,
                        )[addr]);
                    }
                }
            );
        };
        tight_sealed_branch_disk_insert(
            pre.visible_sealed_branch_disk(),
            post.visible_sealed_branch_disk(),
            pre.semantic_branch_roots(),
            branch_root,
            pre.betree.branch_summary,
            post.betree.branch_summary,
            new_branch,
        );
        assert(post.semantic_sealed_branch_disk().entries
            == pre.semantic_sealed_branch_disk().entries
                .union_prefer_right(new_branch.disk_view.entries));

        let post_full_branch = post.linked_i().buffer_dv.get_branch(
            branch_root,
        );
        assert(post.semantic_branch_roots().contains(branch_root));
        assert(post.linked_i().valid_ranking(post_tree.the_ranking())) by {
            assert(post.linked_i().root == post_tree.root);
            assert(post.linked_i().dv == post_tree.dv);
        };
        assert(post.linked_i().acyclic());
        let (post_semantic_tree_likes, post_semantic_branch_likes)
            = post.linked_i().transitive_likes();
        post.linked_i().tree_likes_domain(post.linked_i().the_ranking());
        assert(post_semantic_tree_likes.dom()
            == post.linked_i().reachable_betree_addrs());
        post.linked_i().buffer_likes_domain(post_semantic_tree_likes);
        assert(post.linked_i().root == post.tight_betree_i().root);
        assert(post.linked_i().dv == post.tight_betree_i().dv);
        assert(post.linked_i().reachable_betree_addrs()
            == post.tight_betree_i().reachable_betree_addrs()) by {
            let ranking = post.tight_betree_i().the_ranking();
            assert(post.linked_i().valid_ranking(ranking));
            agreeable_betrees_same_reachable(
                post.linked_i(),
                post.tight_betree_i(),
                ranking,
                ranking,
            );
        };
        post.linked_i().same_reachable_betree_addrs_implies_same_buffer_addrs(
            post.tight_betree_i(),
        );
        assert(post_semantic_branch_likes.dom()
            == post.tight_betree_i().reachable_buffer_addrs());
        assert(post.semantic_branch_roots()
            == post_semantic_branch_likes.dom()
                + CompactorInput::input_roots(post.i().compactors));
        assert(new_branch.disk_view.is_sub_disk(post_full_branch.disk_view)) by {
            assert forall |addr: Address|
                #[trigger] new_branch.disk_view.entries.contains_key(addr)
                implies post_full_branch.disk_view.entries.contains_key(addr)
                    && post_full_branch.disk_view.entries[addr]
                        == new_branch.disk_view.entries[addr]
            by {
                assert(post.semantic_sealed_branch_disk().entries
                    == pre.semantic_sealed_branch_disk().entries
                        .union_prefer_right(new_branch.disk_view.entries));
            };
        };
        assert(new_branch.full_repr()
            <= post_full_branch.disk_view.representation());
        assert forall |addr: Address|
            #[trigger] (post_full_branch.disk_view.representation()
                - new_branch.disk_view.representation()).contains(addr)
            implies !new_branch.get_summary().contains(addr.au)
        by {
            if new_branch.get_summary().contains(addr.au) {
                assert(addresses_in_aus(new_branch.get_summary()).contains(addr));
                assert(new_branch.disk_view.entries.contains_key(addr)) by {
                    assert(new_branch.valid_sealed_branch());
                    assert(crate::allocation_layer::Likes_v::restrict_domain_au(
                        new_branch.disk_view.entries,
                        new_branch.get_summary(),
                    ) == new_branch.full_repr());
                    assert(new_branch.full_repr().contains(addr)) by {
                        assert(post_full_branch.disk_view.entries.contains_key(addr));
                        assert(post.semantic_sealed_branch_disk().entries[addr]
                            == new_branch.disk_view.entries[addr]);
                    };
                };
            }
        };
        pre.i().inv_implies_wf_branch_dv();
        let pre_branch_disk = pre.semantic_sealed_branch_disk()
            .to_branch_disk();
        assert(pre_branch_disk.wf());
        assert(new_branch.disk_view.wf());
        assert(pre_branch_disk.entries.dom().disjoint(
            new_branch.disk_view.entries.dom(),
        )) by {
            assert forall |addr: Address|
                #[trigger] pre_branch_disk.entries.contains_key(addr)
                implies !new_branch.disk_view.entries.contains_key(addr)
            by {
                assert(pre.semantic_sealed_branch_disk().entries
                    .contains_key(addr));
                assert(pre.visible_sealed_branch_disk().entries
                    .contains_key(addr));
                assert(pre_sealed_aus.contains(addr.au));
                if new_branch.disk_view.entries.contains_key(addr) {
                    assert(new_branch.full_repr().contains(addr));
                    assert(new_branch.get_summary().contains(addr.au));
                    assert(new_branch.get_summary()
                        <= pre.i().branch_allocator_aus());
                    assert(pre_sealed_aus.disjoint(
                        pre.i().branch_allocator_aus(),
                    ));
                }
            };
        };
        pre_branch_disk.merge_disjoint_disk_preserves_wf(
            new_branch.disk_view,
        );
        assert(post_full_branch.disk_view
            == pre_branch_disk.merge_disk(new_branch.disk_view)) by {
            assert(post.semantic_sealed_branch_disk().entries
                == pre.semantic_sealed_branch_disk().entries
                    .union_prefer_right(new_branch.disk_view.entries));
        };
        assert(post_full_branch.disk_view.wf());
        new_branch.valid_subdisk_preserves_valid_sealed_branch(
            post_full_branch,
            new_branch.get_summary(),
        );
        assert(post_full_branch.valid_sealed_branch());
        assert(post_full_branch.i() == new_branch.i());
        assert(new_branch.root().i(
            post.i().betree.linked.buffer_dv,
            branch_root,
        ) == pre.i().betree.memtable.buffer);

        assert(pushed.valid_view(post.linked_i()));
        assert(LinkedBetreeVars::State::internal_flush_memtable(
            pre.i().betree,
            post.i().betree,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            new_branch.root(),
            post.i().betree.linked,
            new_addrs,
        ));
        pre.i().betree.internal_flush_memtable_aus_ensures(
            post.i().betree,
            new_branch.root(),
            new_addrs,
        );
        pushed.valid_view_implies_same_transitive_likes(
            post.i().betree.linked,
        );
        let (model_new_betree_aus, model_new_branch_aus)
            = crate::allocation_layer::AllocationBetree_v::AllocationBetree::State::flush_memtable_au_likes(
                pre.i().betree,
                post.i().betree,
                new_addrs,
                pre.i().betree_aus,
                pre.i().branch_aus,
            );
        let (pushed_tree_likes, pushed_branch_likes) = pushed.transitive_likes();
        let (post_tree_likes, post_branch_likes)
            = post.i().betree.linked.transitive_likes();
        assert(pushed_tree_likes == post_tree_likes);
        assert(model_new_betree_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                pushed_tree_likes,
            ));
        assert(post.i().betree_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                post_tree_likes,
            ));
        assert(post.i().betree_aus == model_new_betree_aus);
        assert(set_addrs_disjoint_aus(pushed.dv.entries.dom())) by {
            assert(pushed.dv.entries.dom()
                == pre.tight_betree_i().dv.entries.dom().insert(new_root_addr));
            assert(set_addrs_disjoint_aus(
                pre.tight_betree_i().dv.entries.dom(),
            ));
            assert(!pre.betree.betree_aus.dom().contains(new_root_addr.au));
            assert forall |left: Address, right: Address|
                pushed.dv.entries.dom().contains(left)
                    && pushed.dv.entries.dom().contains(right)
                    && left != right
                implies #[trigger] addrs_with_different_au(left, right)
            by {
                if left == new_root_addr || right == new_root_addr {
                    let old = if left == new_root_addr { right } else { left };
                    assert(pre.tight_betree_i().dv.entries.contains_key(old));
                    assert(pre.betree.betree_aus.dom().contains(old.au));
                }
            };
        };
        assert(post_semantic_tree_likes.dom()
            == post.i().betree.linked.dv.entries.dom());
        crate::allocation_layer::Likes_v::to_au_likes_domain(
            post_semantic_tree_likes,
        );
        assert(post.i().betree_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                post_semantic_tree_likes,
            ));
        assert(post.i().betree_aus.dom()
            == to_aus(post.i().betree.linked.dv.entries.dom()));
        assert(post.i().betree.linked.dv.entries.dom()
            == crate::allocation_layer::Likes_v::restrict_domain_au(
                pushed.dv.entries,
                post.i().betree_aus.dom(),
            )) by {
            let kept = crate::allocation_layer::Likes_v::restrict_domain_au(
                pushed.dv.entries,
                post.i().betree_aus.dom(),
            );
            assert forall |addr: Address|
                #[trigger] post.i().betree.linked.dv.entries.contains_key(addr)
                implies kept.contains(addr)
            by {
                assert(pushed.dv.entries.contains_key(addr));
                crate::disk::GenericDisk_v::to_aus_domain(
                    post.i().betree.linked.dv.entries.dom(),
                );
            };
            assert forall |addr: Address| #[trigger] kept.contains(addr)
                implies post.i().betree.linked.dv.entries.contains_key(addr)
            by {
                assert(to_aus(post.i().betree.linked.dv.entries.dom())
                    .contains(addr.au));
                let live_addr = choose |live_addr: Address|
                    post.i().betree.linked.dv.entries.contains_key(live_addr)
                    && live_addr.au == addr.au;
                assert(pushed.dv.entries.contains_key(live_addr));
                if addr != live_addr {
                    assert(addrs_with_different_au(addr, live_addr));
                    assert(addr.au != live_addr.au);
                }
            };
        };
        assert(post.i().betree.linked.buffer_dv.entries
            == pre.i().betree.linked.buffer_dv.entries
                .union_prefer_right(new_branch.disk_view.entries));
        assert_seqs_equal!(
            post.i().wip_branches,
            pre.i().wip_branches.remove(branch_idx),
            idx => {
                let pre_idx = if idx < branch_idx { idx } else { idx + 1 };
                assert(post.betree.wip_branches[idx]
                    == pre.betree.wip_branches[pre_idx]);
                let cached = pre.betree.wip_branches[pre_idx];
                let allocated = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                assert(pre.i().wip_branches_disjoint());
                assert(pre_idx != branch_idx);
                assert(pre.i().wip_branches[pre_idx].mini_allocator.all_aus()
                    .disjoint(pre.i().wip_branches[branch_idx]
                        .mini_allocator.all_aus()));
                AllocationBulkBranch::alloc_aus_ensures(
                    pre.i().wip_branches,
                    pre_idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= pre.i().branch_allocator_aus());
                assert(cached.mini_allocator.all_aus().disjoint(allocs));
                assert(cached.mini_allocator.all_aus().disjoint(deallocs)) by {
                    assert(deallocs <= pre.betree.betree_aus.dom());
                    assert(pre.i().betree_aus.dom().disjoint(
                        pre.i().branch_allocator_aus(),
                    ));
                };
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    allocs,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    deallocs,
                );
                disk_access_for_alloc_visible_outside_alloc_dealloc(
                    pre.disk,
                    new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        );
        pre.wip_alloc_aus_agree();
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            == pre.i().branch_allocator_aus());
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(allocs)) by {
            assert(pre.i().is_fresh(allocs));
        }
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(deallocs)) by {
            assert(deallocs <= pre.betree.betree_aus.dom());
            assert(pre.i().betree_aus.dom().disjoint(
                pre.i().branch_allocator_aus(),
            ));
        }
        assert forall |input_idx: int|
            0 <= input_idx < pre.betree.compactors.len()
            implies {
                let input_aus = #[trigger]
                    pre.betree.compactor_input_aus(input_idx);
                &&& post.betree.compactor_input_aus(input_idx)
                    == input_aus
                &&& to_branch_nodes(post.disk.visible()).restrict(
                    addresses_in_aus(input_aus),
                ) == to_branch_nodes(pre.disk.visible()).restrict(
                    addresses_in_aus(input_aus),
                )
            }
        by {
            let roots = pre.betree.compactors[input_idx]
                .input_buffers.addrs.to_set();
            let root_aus = to_aus(roots);
            let root_sets = Seq::new(
                pre.betree.compactors.len(),
                |i: int| pre.betree.compactors[i]
                    .input_buffers.addrs.to_set(),
            );
            crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                root_sets,
                input_idx,
            );
            crate::disk::GenericDisk_v::to_aus_preserves_lte(
                roots,
                CompactorInput::input_roots(pre.betree.compactors),
            );
            assert(root_aus <= read_ref_aus(pre.betree.compactors)) by {
                assert forall |au: AU| #[trigger] root_aus.contains(au)
                    implies read_ref_aus(pre.betree.compactors).contains(au)
                by {
                    let root = choose |root: Address|
                        roots.contains(root) && root.au == au;
                    assert(CompactorInput::input_roots(
                        pre.betree.compactors,
                    ).contains(root));
                }
            }
            pre.i().inv_branch_summary_ensures();
            assert(root_aus <= pre.betree.branch_summary.dom());
            assert(!root_aus.contains(branch_root.au));
            assert(post.betree.branch_summary.restrict(root_aus)
                == pre.betree.branch_summary.restrict(root_aus)) by {
                assert_maps_equal!(
                    post.betree.branch_summary.restrict(root_aus),
                    pre.betree.branch_summary.restrict(root_aus),
                    au => {}
                );
            }
            assert(post.betree.compactor_input_aus(input_idx)
                == pre.betree.compactor_input_aus(input_idx));
            summary_aus_restrict_subset(
                pre.betree.branch_summary,
                root_aus,
            );
            let input_aus = pre.betree.compactor_input_aus(input_idx);
            assert(input_aus <= pre_sealed_aus);
            assert(addresses_in_aus(input_aus) <= pre_sealed_addrs) by {
                assert forall |addr: Address|
                    #[trigger] addresses_in_aus(input_aus).contains(addr)
                    implies pre_sealed_addrs.contains(addr)
                by {
                }
            }
            map_restrict_equal_on_subset(
                to_branch_nodes(post.disk.visible()),
                to_branch_nodes(pre.disk.visible()),
                pre_sealed_addrs,
                addresses_in_aus(input_aus),
            );
        }
        Self::unchanged_compactor_receipts_preserve_selected_views(
            pre,
            post,
        );
        Self::removed_wip_preserves_staged_nodes_after_access(
            pre,
            post,
            lbl,
            new_disk,
            access,
            branch_idx,
        );
    }

    proof fn split_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        loaded_path: LoadedBetreePath,
        request: SplitRequest,
        new_addrs: SplitAddrs,
        path_addrs: PathAddrs,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::split(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                loaded_path,
                request,
                new_addrs,
                path_addrs,
                access.loaded_betree_reads(),
                access.loaded_betree_writes(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            access.writes().dom() <= addresses_in_aus(lbl.allocs()),
            AllocationBranchBetree::State::internal_split(
                pre.i(),
                post.i(),
                lbl.i(pre),
                post.i().betree,
                Path {
                    linked: pre.linked_i(),
                    key: loaded_path.key,
                    depth: loaded_path.depth(),
                },
                request,
                new_addrs,
                path_addrs,
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        access.cached_only_betree_is_only_betree();

        pre.linked_i_is_tight_candidate();
        pre.linked_i_tight_tree_facts();
        assert(post.disk == new_disk);
        assert(post.betree == new_betree);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let betree_reads = access.loaded_betree_reads();
        let betree_writes = access.loaded_betree_writes();
        let pre_tree = pre.tight_betree_i();
        let pre_linked = pre.linked_i();
        let linked_path = Path {
            linked: pre_linked,
            key: loaded_path.key,
            depth: loaded_path.depth(),
        };
        let witness = disk_access_for_alloc_witness(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
        );

        assert(access.only_betree());
        assert(reads == access.betree_reads);
        assert(writes == access.betree_writes);
        assert(allocs == to_aus(new_addrs.repr() + path_addrs.to_set()));
        crate::disk::GenericDisk_v::to_aus_additive(
            new_addrs.repr(),
            path_addrs.to_set(),
        );
        assert(allocs == to_aus(new_addrs.repr())
            + seq_addrs_to_aus(path_addrs));
        pre.wip_alloc_aus_agree();
        assert(pre.i().branch_allocator_aus()
            == cached_bulk_branch_alloc_aus(pre.betree.wip_branches));
        assert(pre.i().is_fresh(allocs));
        assert(pre.betree.betree_aus.dom().disjoint(allocs));
        assert(pre_tree.dv.entries.dom()
            <= addresses_in_aus(pre.betree.betree_aus.dom()));
        assert(pre_linked.dv.entries <= to_betree_nodes(pre.disk.visible())) by {
            assert(pre_tree.dv.entries <= pre.visible_betree_entries());
            assert(pre_linked.dv == pre_tree.dv);
            assert forall |addr: Address|
                #[trigger] pre_linked.dv.entries.contains_key(addr)
                implies to_betree_nodes(pre.disk.visible()).contains_key(addr)
                    && pre_linked.dv.entries[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]
            by {
                assert(pre.visible_betree_entries().contains_key(addr));
            };
        };

        let path_reads = access.betree_reads.restrict(
            loaded_path.needed_addrs(),
        );
        assert(loaded_path.valid_for(
            pre.betree.root,
            to_betree_nodes(path_reads),
        )) by {
            assert_maps_equal!(
                to_betree_nodes(path_reads),
                betree_reads.restrict(loaded_path.needed_addrs()),
                addr => {}
            );
        };
        loaded_path_reads_come_from_pre_cache(
            pre.disk,
            witness.expanded,
            allocs,
            pre.betree.betree_aus.dom(),
            pre_linked,
            path_reads,
            loaded_path,
        );
        assert(path_reads.restrict(loaded_path.needed_addrs()) == path_reads);
        assert(path_reads <= pre.disk.cache);
        loaded_betree_path_matches_linked(
            pre.disk,
            pre_linked,
            path_reads,
            loaded_path,
            loaded_path.depth(),
        );
        assert(linked_path.valid());
        assert(linked_path.target().root()
            == loaded_path.target().node);

        let child_idx = request.get_child_idx();
        let child_addr = loaded_path.child_addr(child_idx);
        assert(linked_path.target().root().valid_child_index(child_idx));
        assert(linked_path.target().root().children[child_idx as int]
            == Some(child_addr));
        let linked_child = linked_path.target().child_at_idx(child_idx);
        assert(linked_child.root == Some(child_addr));
        assert(pre_tree.dv.entries.contains_key(child_addr));
        assert(to_betree_nodes(pre.disk.visible()).contains_key(child_addr));
        assert(pre.disk.visible().contains_key(child_addr));
        assert(pre.betree.betree_aus.dom().contains(child_addr.au));
        assert(!allocs.contains(child_addr.au));
        assert(reads.contains_key(child_addr));
        assert(witness.expanded.cache.contains_key(child_addr));
        assert(pre.disk.cache.contains_key(child_addr)) by {
            if !pre.disk.cache.contains_key(child_addr) {
                assert((witness.expanded.cache.dom() - pre.disk.cache.dom())
                    .contains(child_addr));
                assert(addresses_in_aus(allocs).contains(child_addr));
            }
        };
        assert(reads[child_addr] == pre.disk.cache[child_addr]);
        let child_read = reads.restrict(set![child_addr]);
        assert(child_read <= pre.disk.cache);
        betree_read_node_matches_visible(pre.disk, child_read, child_addr);
        assert(linked_child.has_root());
        assert(betree_reads[child_addr] == linked_child.root());
        assert(linked_path.target().can_split_parent(request));

        let replacement = linked_path.target().split_parent(
            request,
            new_addrs,
        );
        let replacement_writes =
            crate::implementation::CachedBranchBetree_v::split_replacement(
                loaded_path,
                betree_reads,
                request,
                new_addrs,
            );
        assert(replacement.root == Some(new_addrs.parent));
        assert(replacement.dv.entries
            == pre_linked.dv.entries.union_prefer_right(
                replacement_writes,
            )) by {
            assert_maps_equal!(
                replacement.dv.entries,
                pre_linked.dv.entries.union_prefer_right(replacement_writes),
                addr => {}
            );
        };
        assert(replacement.buffer_dv == pre_linked.buffer_dv);

        assert(path_addrs.no_duplicates()) by {
            assert forall |i: int, j: int|
                0 <= i < path_addrs.len()
                    && 0 <= j < path_addrs.len()
                    && i != j
                implies path_addrs[i] != path_addrs[j]
            by {
                assert(path_addrs[i].au != path_addrs[j].au);
            };
        };
        assert(path_addrs.to_set().disjoint(pre_linked.dv.entries.dom())) by {
            assert(seq_addrs_to_aus(path_addrs) <= allocs);
            crate::disk::GenericDisk_v::to_aus_domain(
                path_addrs.to_set(),
            );
        };
        assert(path_addrs.to_set().disjoint(replacement_writes.dom())) by {
            assert(to_aus(new_addrs.repr()).disjoint(
                seq_addrs_to_aus(path_addrs),
            ));
            assert(replacement_writes.dom() == new_addrs.repr());
            crate::disk::GenericDisk_v::to_aus_domain(
                path_addrs.to_set(),
            );
            crate::disk::GenericDisk_v::to_aus_domain(
                new_addrs.repr(),
            );
        };
        loaded_substitute_writes_match(
            pre.disk,
            path_reads,
            loaded_path,
            linked_path,
            new_addrs.parent,
            replacement,
            replacement_writes,
            path_addrs,
        );

        let splitted = LinkedBetreeVars::State::post_split(
            linked_path,
            request,
            new_addrs,
            path_addrs,
        );
        assert(betree_writes
            == crate::implementation::CachedBranchBetree_v::substitute_writes(
                loaded_path,
                new_addrs.parent,
                replacement_writes,
                path_addrs,
            ));
        assert(to_betree_nodes(writes).dom() == writes.dom());
        assert(betree_writes.dom() == writes.dom());
        assert(splitted.dv.entries
            == pre_linked.dv.entries.union_prefer_right(betree_writes));
        assert(writes.dom() <= addresses_in_aus(allocs)) by {
            assert(betree_writes.dom()
                <= replacement_writes.dom() + path_addrs.to_set());
            assert(replacement_writes.dom() == new_addrs.repr());
            crate::disk::GenericDisk_v::to_aus_domain(
                new_addrs.repr() + path_addrs.to_set(),
            );
        };
        assert(splitted.root == post.betree.root);
        assert(splitted.buffer_dv == pre_linked.buffer_dv);

        assert(pre_linked.is_fresh(new_addrs.repr())) by {
            assert(to_aus(new_addrs.repr()) <= allocs);
            crate::disk::GenericDisk_v::to_aus_domain(
                new_addrs.repr(),
            );
            assert forall |addr: Address|
                #[trigger] new_addrs.repr().contains(addr)
                implies !pre_linked.dv.entries.contains_key(addr)
                    && !pre_linked.buffer_dv.entries.contains_key(addr)
            by {
                assert(allocs.contains(addr.au));
                if pre_linked.dv.entries.contains_key(addr) {
                    assert(pre.betree.betree_aus.dom().contains(addr.au));
                }
                if pre_linked.buffer_dv.entries.contains_key(addr) {
                    assert(pre.visible_sealed_branch_disk().entries
                        .contains_key(addr));
                    assert(summary_aus(pre.betree.branch_summary)
                        .contains(addr.au));
                }
            };
        };
        assert(pre_linked.is_fresh(path_addrs.to_set())) by {
            assert(seq_addrs_to_aus(path_addrs) <= allocs);
            crate::disk::GenericDisk_v::to_aus_domain(
                path_addrs.to_set(),
            );
            assert forall |addr: Address|
                #[trigger] path_addrs.to_set().contains(addr)
                implies !pre_linked.dv.entries.contains_key(addr)
                    && !pre_linked.buffer_dv.entries.contains_key(addr)
            by {
                assert(allocs.contains(addr.au));
                if pre_linked.dv.entries.contains_key(addr) {
                    assert(pre.betree.betree_aus.dom().contains(addr.au));
                }
                if pre_linked.buffer_dv.entries.contains_key(addr) {
                    assert(pre.visible_sealed_branch_disk().entries
                        .contains_key(addr));
                    assert(summary_aus(pre.betree.branch_summary)
                        .contains(addr.au));
                }
            };
        };
        pre.i().betree.post_split_ensures(
            linked_path,
            request,
            new_addrs,
            path_addrs,
        );
        assert(splitted.acyclic());
        let post_tree = reachable_tight_betree(splitted);
        reachable_tight_betree_facts(splitted);

        let model_post_linked = LinkedBetree {
            root: post_tree.root,
            dv: post_tree.dv,
            buffer_dv: pre.semantic_sealed_branch_disk(),
        };
        let model_post_vars = LinkedBetreeVars::State {
            memtable: pre.i().betree.memtable,
            linked: model_post_linked,
        };
        assert(splitted.valid_view(model_post_linked)) by {
            assert(model_post_linked.wf());
            assert(model_post_linked.dv.is_sub_disk(splitted.dv));
            assert(model_post_linked.buffer_dv.agrees_with(
                splitted.buffer_dv,
            ));
        };
        assert(LinkedBetreeVars::State::internal_split(
            pre.i().betree,
            model_post_vars,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            model_post_linked,
            linked_path,
            request,
            new_addrs,
            path_addrs,
        ));
        pre.i().betree.internal_split_aus_ensures(
            model_post_vars,
            linked_path,
            request,
            new_addrs,
            path_addrs,
        );

        let (splitted_tree_likes, splitted_branch_likes) =
            splitted.transitive_likes();
        let (expected_betree_aus, expected_branch_aus) =
            crate::allocation_layer::AllocationBetree_v::AllocationBetree::State::internal_split_au_likes(
                linked_path,
                request,
                new_addrs,
                path_addrs,
                pre.i().betree_aus,
                pre.i().branch_aus,
            );
        assert(expected_betree_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                splitted_tree_likes,
            ));
        assert(expected_branch_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                splitted_branch_likes,
            ));
        loaded_path_addrs_match_linked(
            pre.disk,
            pre_linked,
            path_reads,
            loaded_path,
        );
        loaded_path.path_addrs().to_multiset_ensures();
        linked_path.addrs_on_path().to_multiset_ensures();
        assert(loaded_path.path_addrs().to_multiset()
            == linked_path.addrs_on_path().to_multiset().add(
                linked_path.target().root_likes(),
            ));
        assert(crate::implementation::CachedBranchBetree_v::path_discard_likes(
            loaded_path,
        ).insert(child_addr)
            == crate::allocation_layer::LikesBetree_v::split_discard_betree(
                linked_path,
                request,
            ));
        split_addrs_repr_likes(new_addrs);
        assert(crate::implementation::CachedBranchBetree_v::added_path_likes(
            new_addrs,
            path_addrs,
        ) == crate::allocation_layer::LikesBetree_v::add_betree_likes(
            new_addrs,
            path_addrs,
        ));
        linked_child.root_buffer_likes_ensures();
        assert(crate::implementation::CachedBranchBetree_v::direct_buffer_likes(
            betree_reads[child_addr],
        ) == crate::allocation_layer::LikesBetree_v::split_add_buffers(
            linked_path,
            request,
        ));
        assert(post.betree.betree_aus == expected_betree_aus);
        assert(post.betree.branch_aus == expected_branch_aus);

        let stable_aus = pre.betree.betree_aus.dom() - deallocs;
        let stable_addrs = addresses_in_aus(stable_aus);
        assert(stable_aus.disjoint(allocs));
        assert(stable_aus.disjoint(deallocs));
        addresses_in_aus_preserves_disjointness(stable_aus, allocs);
        addresses_in_aus_preserves_disjointness(stable_aus, deallocs);
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            stable_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            stable_addrs,
        );
        let ranking = splitted.the_ranking();
        splitted.tree_likes_domain(ranking);
        crate::allocation_layer::Likes_v::to_au_likes_domain(
            splitted_tree_likes,
        );
        assert(post_tree.dv.entries <= post.visible_betree_entries()) by {
            assert forall |addr: Address|
                #[trigger] post_tree.dv.entries.contains_key(addr)
                implies post.visible_betree_entries().contains_key(addr)
                    && post_tree.dv.entries[addr]
                        == post.visible_betree_entries()[addr]
            by {
                assert(splitted.dv.entries.contains_key(addr));
                assert(splitted.reachable_betree_addrs().contains(addr));
                assert(splitted_tree_likes.contains(addr));
                assert(post.betree.betree_aus.dom().contains(addr.au));
                assert(addresses_in_aus(post.betree.betree_aus.dom())
                    .contains(addr));
                if writes.contains_key(addr) {
                    assert(new_disk.visible()[addr] == writes[addr]);
                    assert(to_betree_nodes(new_disk.visible())
                        .contains_key(addr));
                    assert(betree_writes.contains_key(addr));
                    assert(splitted.dv.entries[addr]
                        == betree_writes[addr]);
                    assert(betree_writes[addr]
                        == to_betree_nodes(writes)[addr]);
                    assert(to_betree_nodes(new_disk.visible())[addr]
                        == to_betree_nodes(writes)[addr]);
                } else {
                    assert(pre_tree.dv.entries.contains_key(addr));
                    assert(pre_tree.dv.entries
                        <= pre.visible_betree_entries());
                    assert(pre.visible_betree_entries().contains_key(addr));
                    assert(pre.betree.betree_aus.dom().contains(addr.au));
                    assert(!deallocs.contains(addr.au));
                    assert(stable_addrs.contains(addr));
                    assert(to_betree_nodes(pre.disk.visible()).restrict(
                        stable_addrs,
                    ).contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_addrs,
                    ).contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_addrs,
                    ) == to_betree_nodes(pre.disk.visible()).restrict(
                        stable_addrs,
                    ));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_addrs,
                    )[addr] == to_betree_nodes(pre.disk.visible()).restrict(
                        stable_addrs,
                    )[addr]);
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_addrs,
                    )[addr] == to_betree_nodes(new_disk.visible())[addr]);
                    assert(to_betree_nodes(pre.disk.visible()).restrict(
                        stable_addrs,
                    )[addr] == to_betree_nodes(pre.disk.visible())[addr]);
                    assert(!betree_writes.contains_key(addr));
                    assert(splitted.dv.entries[addr]
                        == pre_linked.dv.entries[addr]);
                    assert(pre_linked.dv.entries[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]);
                    assert(to_betree_nodes(new_disk.visible())[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]);
                }
                assert(post_tree.dv.entries[addr] == splitted.dv.entries[addr]);
            };
        };
        reachable_tight_betree_is_candidate(
            splitted,
            post.betree.root,
            post.visible_betree_entries(),
        );
        tight_betree_of_equals_candidate(
            post.betree.root,
            post.visible_betree_entries(),
            post_tree,
        );
        assert(post.tight_betree_i() == post_tree);

        assert(splitted_branch_likes.dom()
            == pre_linked.reachable_buffer_addrs()) by {
            let (pre_tree_likes, pre_branch_likes) =
                pre_linked.transitive_likes();
            crate::allocation_layer::LikesBetree_v::LikesBetree::State::post_split_likes_ensures(
                pre.i().betree,
                model_post_vars,
                linked_path,
                request,
                new_addrs,
                path_addrs,
            );
            pre_linked.tree_likes_domain(pre_linked.the_ranking());
            pre_linked.buffer_likes_domain(pre_tree_likes);
            assert(splitted_branch_likes
                == pre_branch_likes.add(
                    crate::allocation_layer::LikesBetree_v::split_add_buffers(
                        linked_path,
                        request,
                    ),
                ));
            assert(crate::allocation_layer::LikesBetree_v::split_add_buffers(
                linked_path,
                request,
            ) <= pre_branch_likes);
        };
        splitted.tree_likes_domain(splitted.the_ranking());
        splitted.buffer_likes_domain(splitted_tree_likes);
        assert(splitted_branch_likes.dom()
            == splitted.reachable_buffer_addrs());
        assert(post.semantic_branch_roots()
            == pre.semantic_branch_roots()) by {
            assert(post.betree.compactors == pre.betree.compactors);
            assert(post_tree.reachable_buffer_addrs()
                == splitted.reachable_buffer_addrs()) by {
                splitted.same_reachable_betree_addrs_implies_same_buffer_addrs(
                    post_tree,
                );
            };
            assert(pre_linked.dv == pre_tree.dv);
            assert(pre_linked.dv.entries.dom()
                == pre_linked.reachable_betree_addrs());
            assert(pre_tree.dv.entries.dom()
                == pre_tree.reachable_betree_addrs());
            assert(pre_linked.reachable_betree_addrs()
                == pre_tree.reachable_betree_addrs());
            pre_linked.same_reachable_betree_addrs_implies_same_buffer_addrs(
                pre_tree,
            );
            assert(post_tree.reachable_buffer_addrs()
                == pre_tree.reachable_buffer_addrs());
        };

        let sealed_aus = summary_aus(pre.betree.branch_summary);
        let sealed_addrs = addresses_in_aus(sealed_aus);
        assert(sealed_aus.disjoint(allocs));
        assert(sealed_aus.disjoint(deallocs));
        addresses_in_aus_preserves_disjointness(sealed_aus, allocs);
        addresses_in_aus_preserves_disjointness(sealed_aus, deallocs);
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            sealed_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            sealed_addrs,
        );
        assert(post.betree.branch_summary == pre.betree.branch_summary);
        assert(post.visible_sealed_branch_disk()
            == pre.visible_sealed_branch_disk());
        assert(post.semantic_sealed_branch_disk()
            == pre.semantic_sealed_branch_disk());
        assert(post.linked_i() == model_post_linked);
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i(),
            idx => {
                assert(post.betree.wip_branches[idx]
                    == pre.betree.wip_branches[idx]);
                let cached = pre.betree.wip_branches[idx];
                let allocated = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                AllocationBulkBranch::alloc_aus_ensures(
                    pre.i().wip_branches,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= pre.i().branch_allocator_aus());
                assert(cached.mini_allocator.all_aus().disjoint(allocs));
                assert(cached.mini_allocator.all_aus().disjoint(deallocs)) by {
                    assert(deallocs <= pre.betree.betree_aus.dom());
                };
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    allocs,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    deallocs,
                );
                disk_access_for_alloc_visible_outside_alloc_dealloc(
                    pre.disk,
                    new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        );

        assert(set_addrs_disjoint_aus(splitted.dv.entries.dom())) by {
            assert(splitted.dv.entries.dom()
                == pre_tree.dv.entries.dom() + writes.dom());
            assert(set_addrs_disjoint_aus(pre_tree.dv.entries.dom()));
            assert forall |left: Address, right: Address|
                splitted.dv.entries.dom().contains(left)
                    && splitted.dv.entries.dom().contains(right)
                    && left != right
                implies #[trigger] addrs_with_different_au(left, right)
            by {
                if writes.contains_key(left) || writes.contains_key(right) {
                    if writes.contains_key(left) && writes.contains_key(right) {
                        assert((new_addrs.repr() + path_addrs.to_set())
                            .contains(left));
                        assert((new_addrs.repr() + path_addrs.to_set())
                            .contains(right));
                        if new_addrs.repr().contains(left)
                            && new_addrs.repr().contains(right)
                        {
                            assert(new_addrs.addrs_in_disjoint_aus());
                        } else if path_addrs.to_set().contains(left)
                            && path_addrs.to_set().contains(right)
                        {
                            let i = choose |i: int|
                                0 <= i < path_addrs.len()
                                    && path_addrs[i] == left;
                            let j = choose |j: int|
                                0 <= j < path_addrs.len()
                                    && path_addrs[j] == right;
                            assert(i != j);
                            assert(path_addrs[i].au != path_addrs[j].au);
                        } else {
                            let direct = if new_addrs.repr().contains(left) {
                                left
                            } else {
                                right
                            };
                            let path_addr = if new_addrs.repr().contains(left) {
                                right
                            } else {
                                left
                            };
                            crate::disk::GenericDisk_v::to_aus_domain(
                                new_addrs.repr(),
                            );
                            crate::disk::GenericDisk_v::to_aus_domain(
                                path_addrs.to_set(),
                            );
                            assert(to_aus(new_addrs.repr())
                                .contains(direct.au));
                            assert(seq_addrs_to_aus(path_addrs)
                                .contains(path_addr.au));
                        }
                    } else {
                        let fresh = if writes.contains_key(left) { left } else { right };
                        let old = if writes.contains_key(left) { right } else { left };
                        assert(allocs.contains(fresh.au));
                        assert(pre.betree.betree_aus.dom().contains(old.au));
                    }
                }
            };
        };
        direct_au_restrict_is_domain(
            splitted.dv.entries,
            post_tree.dv.entries.dom(),
        );
        assert(crate::allocation_layer::Likes_v::restrict_domain_au(
            splitted.dv.entries,
            post.i().betree_aus.dom(),
        ) == post.i().betree.linked.dv.entries.dom()) by {
            assert(post.i().betree_aus.dom()
                == to_aus(post_tree.dv.entries.dom()));
        };
        assert(pre.i().betree.linked.buffer_dv
            == post.i().betree.linked.buffer_dv);
        assert(LinkedBetreeVars::State::internal_split(
            pre.i().betree,
            post.i().betree,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            post.i().betree.linked,
            linked_path,
            request,
            new_addrs,
            path_addrs,
        ));
        pre.wip_alloc_aus_agree();
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            == pre.i().branch_allocator_aus());
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(allocs)) by {
            assert(pre.i().is_fresh(allocs));
        }
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(deallocs)) by {
            assert(deallocs <= pre.betree.betree_aus.dom());
            assert(pre.i().betree_aus.dom().disjoint(
                pre.i().branch_allocator_aus(),
            ));
        }
        Self::unchanged_wips_preserve_staged_nodes_after_access(
            pre,
            post,
            lbl,
            new_disk,
            access,
        );
        Self::unchanged_compactor_receipts_preserve_inv(pre, post);
    }

    proof fn flush_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        loaded_path: LoadedBetreePath,
        child_idx: nat,
        buffer_gc: nat,
        new_addrs: TwoAddrs,
        path_addrs: PathAddrs,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::flush(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                loaded_path,
                child_idx,
                buffer_gc,
                new_addrs,
                path_addrs,
                access.loaded_betree_reads(),
                access.loaded_betree_writes(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            access.writes().dom() <= addresses_in_aus(lbl.allocs()),
            AllocationBranchBetree::State::internal_flush(
                pre.i(),
                post.i(),
                lbl.i(pre),
                post.i().betree,
                Path {
                    linked: pre.linked_i(),
                    key: loaded_path.key,
                    depth: loaded_path.depth(),
                },
                child_idx,
                buffer_gc,
                new_addrs,
                path_addrs,
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        access.cached_only_betree_is_only_betree();

        pre.linked_i_is_tight_candidate();
        pre.linked_i_tight_tree_facts();
        assert(post.disk == new_disk);
        assert(post.betree == new_betree);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let betree_reads = access.loaded_betree_reads();
        let betree_writes = access.loaded_betree_writes();
        let pre_tree = pre.tight_betree_i();
        let pre_linked = pre.linked_i();
        let linked_path = Path {
            linked: pre_linked,
            key: loaded_path.key,
            depth: loaded_path.depth(),
        };
        let witness = disk_access_for_alloc_witness(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
        );

        assert(access.only_betree());
        assert(reads == access.betree_reads);
        assert(writes == access.betree_writes);
        assert(allocs == to_aus(new_addrs.repr() + path_addrs.to_set()));
        crate::disk::GenericDisk_v::to_aus_additive(
            new_addrs.repr(),
            path_addrs.to_set(),
        );
        assert(allocs == to_aus(new_addrs.repr())
            + seq_addrs_to_aus(path_addrs));
        pre.wip_alloc_aus_agree();
        assert(pre.i().is_fresh(allocs));
        assert(pre.betree.betree_aus.dom().disjoint(allocs));
        assert(pre_tree.dv.entries.dom()
            <= addresses_in_aus(pre.betree.betree_aus.dom()));
        assert(pre_linked.dv.entries <= to_betree_nodes(pre.disk.visible())) by {
            assert(pre_tree.dv.entries <= pre.visible_betree_entries());
            assert(pre_linked.dv == pre_tree.dv);
            assert forall |addr: Address|
                #[trigger] pre_linked.dv.entries.contains_key(addr)
                implies to_betree_nodes(pre.disk.visible()).contains_key(addr)
                    && pre_linked.dv.entries[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]
            by {
                assert(pre.visible_betree_entries().contains_key(addr));
            };
        };

        let path_reads = access.betree_reads.restrict(
            loaded_path.needed_addrs(),
        );
        assert(loaded_path.valid_for(
            pre.betree.root,
            to_betree_nodes(path_reads),
        )) by {
            assert_maps_equal!(
                to_betree_nodes(path_reads),
                betree_reads.restrict(loaded_path.needed_addrs()),
                addr => {}
            );
        };
        loaded_path_reads_come_from_pre_cache(
            pre.disk,
            witness.expanded,
            allocs,
            pre.betree.betree_aus.dom(),
            pre_linked,
            path_reads,
            loaded_path,
        );
        assert(path_reads.restrict(loaded_path.needed_addrs()) == path_reads);
        assert(path_reads <= pre.disk.cache);
        loaded_betree_path_matches_linked(
            pre.disk,
            pre_linked,
            path_reads,
            loaded_path,
            loaded_path.depth(),
        );
        assert(linked_path.valid());
        assert(linked_path.target().root()
            == loaded_path.target().node);

        let child_addr = loaded_path.child_addr(child_idx);
        assert(linked_path.target().root().valid_child_index(child_idx));
        assert(linked_path.target().root().children[child_idx as int]
            == Some(child_addr));
        let linked_child = linked_path.target().child_at_idx(child_idx);
        assert(linked_child.root == Some(child_addr));
        assert(pre_tree.dv.entries.contains_key(child_addr));
        assert(pre.betree.betree_aus.dom().contains(child_addr.au));
        assert(!allocs.contains(child_addr.au));
        assert(reads.contains_key(child_addr));
        assert(witness.expanded.cache.contains_key(child_addr));
        assert(pre.disk.cache.contains_key(child_addr)) by {
            if !pre.disk.cache.contains_key(child_addr) {
                assert((witness.expanded.cache.dom() - pre.disk.cache.dom())
                    .contains(child_addr));
                assert(addresses_in_aus(allocs).contains(child_addr));
            }
        };
        assert(reads[child_addr] == pre.disk.cache[child_addr]);
        let child_read = reads.restrict(set![child_addr]);
        assert(child_read <= pre.disk.cache);
        assert(to_betree_nodes(pre.disk.visible()).contains_key(child_addr));
        assert(pre.disk.visible().contains_key(child_addr));
        betree_read_node_matches_visible(pre.disk, child_read, child_addr);
        assert(linked_child.has_root());
        assert(betree_reads[child_addr] == linked_child.root());
        assert(linked_path.target().can_flush(child_idx, buffer_gc));

        let replacement = linked_path.target().flush(
            child_idx,
            buffer_gc,
            new_addrs,
        );
        let replacement_writes =
            crate::implementation::CachedBranchBetree_v::flush_replacement(
                loaded_path,
                betree_reads,
                child_idx,
                buffer_gc,
                new_addrs,
            );
        assert(replacement.root == Some(new_addrs.addr1));
        assert(replacement.dv.entries
            == pre_linked.dv.entries.union_prefer_right(
                replacement_writes,
            )) by {
            assert_maps_equal!(
                replacement.dv.entries,
                pre_linked.dv.entries.union_prefer_right(replacement_writes),
                addr => {}
            );
        };
        assert(replacement.buffer_dv == pre_linked.buffer_dv);

        assert(path_addrs.no_duplicates()) by {
            assert forall |i: int, j: int|
                0 <= i < path_addrs.len()
                    && 0 <= j < path_addrs.len()
                    && i != j
                implies path_addrs[i] != path_addrs[j]
            by {
                assert(path_addrs[i].au != path_addrs[j].au);
            };
        };
        assert(path_addrs.to_set().disjoint(pre_linked.dv.entries.dom())) by {
            assert(seq_addrs_to_aus(path_addrs) <= allocs);
            crate::disk::GenericDisk_v::to_aus_domain(path_addrs.to_set());
        };
        assert(path_addrs.to_set().disjoint(replacement_writes.dom())) by {
            assert(to_aus(new_addrs.repr()).disjoint(
                seq_addrs_to_aus(path_addrs),
            ));
            assert(replacement_writes.dom() == new_addrs.repr());
            crate::disk::GenericDisk_v::to_aus_domain(path_addrs.to_set());
            crate::disk::GenericDisk_v::to_aus_domain(new_addrs.repr());
        };
        loaded_substitute_writes_match(
            pre.disk,
            path_reads,
            loaded_path,
            linked_path,
            new_addrs.addr1,
            replacement,
            replacement_writes,
            path_addrs,
        );

        let flushed = LinkedBetreeVars::State::post_flush(
            linked_path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
        );
        assert(betree_writes
            == crate::implementation::CachedBranchBetree_v::substitute_writes(
                loaded_path,
                new_addrs.addr1,
                replacement_writes,
                path_addrs,
            ));
        assert(to_betree_nodes(writes).dom() == writes.dom());
        assert(betree_writes.dom() == writes.dom());
        assert(flushed.dv.entries
            == pre_linked.dv.entries.union_prefer_right(betree_writes));
        assert(writes.dom() <= addresses_in_aus(allocs)) by {
            assert(betree_writes.dom()
                <= replacement_writes.dom() + path_addrs.to_set());
            assert(replacement_writes.dom() == new_addrs.repr());
            crate::disk::GenericDisk_v::to_aus_domain(
                new_addrs.repr() + path_addrs.to_set(),
            );
        };
        assert(flushed.root == post.betree.root);
        assert(flushed.buffer_dv == pre_linked.buffer_dv);

        assert(pre_linked.is_fresh(new_addrs.repr())) by {
            assert(to_aus(new_addrs.repr()) <= allocs);
            crate::disk::GenericDisk_v::to_aus_domain(new_addrs.repr());
            assert forall |addr: Address|
                #[trigger] new_addrs.repr().contains(addr)
                implies !pre_linked.dv.entries.contains_key(addr)
                    && !pre_linked.buffer_dv.entries.contains_key(addr)
            by {
                assert(allocs.contains(addr.au));
                if pre_linked.dv.entries.contains_key(addr) {
                    assert(pre.betree.betree_aus.dom().contains(addr.au));
                }
                if pre_linked.buffer_dv.entries.contains_key(addr) {
                    assert(pre.visible_sealed_branch_disk().entries
                        .contains_key(addr));
                    assert(summary_aus(pre.betree.branch_summary)
                        .contains(addr.au));
                }
            };
        };
        assert(pre_linked.is_fresh(path_addrs.to_set())) by {
            assert(seq_addrs_to_aus(path_addrs) <= allocs);
            crate::disk::GenericDisk_v::to_aus_domain(path_addrs.to_set());
            assert forall |addr: Address|
                #[trigger] path_addrs.to_set().contains(addr)
                implies !pre_linked.dv.entries.contains_key(addr)
                    && !pre_linked.buffer_dv.entries.contains_key(addr)
            by {
                assert(allocs.contains(addr.au));
                if pre_linked.dv.entries.contains_key(addr) {
                    assert(pre.betree.betree_aus.dom().contains(addr.au));
                }
                if pre_linked.buffer_dv.entries.contains_key(addr) {
                    assert(pre.visible_sealed_branch_disk().entries
                        .contains_key(addr));
                    assert(summary_aus(pre.betree.branch_summary)
                        .contains(addr.au));
                }
            };
        };
        assert(pre_linked.valid_path_replacement(
            linked_path,
            new_addrs,
            path_addrs,
        ));
        pre.i().betree.post_flush_ensures(
            linked_path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
        );
        assert(flushed.acyclic());
        let post_tree = reachable_tight_betree(flushed);
        reachable_tight_betree_facts(flushed);

        let model_post_vars = LinkedBetreeVars::State {
            memtable: pre.i().betree.memtable,
            linked: flushed,
        };
        assert(flushed.valid_view(flushed));
        assert(LinkedBetreeVars::State::internal_flush(
            pre.i().betree,
            model_post_vars,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            flushed,
            linked_path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
        ));
        pre.i().betree.internal_flush_aus_ensures(
            model_post_vars,
            linked_path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
        );
        let (flushed_tree_likes, flushed_branch_likes) =
            flushed.transitive_likes();
        let (expected_betree_aus, expected_branch_aus) =
            crate::allocation_layer::AllocationBetree_v::AllocationBetree::State::internal_flush_au_likes(
                linked_path,
                child_idx,
                buffer_gc,
                new_addrs,
                path_addrs,
                pre.i().betree_aus,
                pre.i().branch_aus,
            );
        assert(expected_betree_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                flushed_tree_likes,
            ));
        assert(expected_branch_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                flushed_branch_likes,
            ));
        loaded_path_addrs_match_linked(
            pre.disk,
            pre_linked,
            path_reads,
            loaded_path,
        );
        loaded_path.path_addrs().to_multiset_ensures();
        linked_path.addrs_on_path().to_multiset_ensures();
        assert(loaded_path.path_addrs().to_multiset()
            == linked_path.addrs_on_path().to_multiset().add(
                linked_path.target().root_likes(),
            ));
        assert(crate::implementation::CachedBranchBetree_v::path_discard_likes(
            loaded_path,
        ).insert(child_addr)
            == crate::allocation_layer::LikesBetree_v::flush_discard_betree(
                linked_path,
                child_idx,
            ));
        two_addrs_repr_likes(new_addrs);
        assert(crate::implementation::CachedBranchBetree_v::added_path_likes(
            new_addrs,
            path_addrs,
        ) == crate::allocation_layer::LikesBetree_v::add_betree_likes(
            new_addrs,
            path_addrs,
        ));
        assert(crate::implementation::CachedBranchBetree_v::direct_buffer_likes(
            linked_path.target().root(),
        ).sub(
            linked_path.target().root().buffers.slice(
                0,
                buffer_gc as int,
            ).addrs.to_multiset(),
        ) == crate::implementation::CachedBranchBetree_v::direct_buffer_likes(
            linked_path.target().root(),
        ).sub(
            crate::allocation_layer::LikesBetree_v::flush_discard_buffers(
                linked_path,
                buffer_gc,
            ),
        ));
        assert(post.betree.betree_aus == expected_betree_aus);
        assert(post.betree.branch_aus == expected_branch_aus);

        let added_tree_likes =
            crate::allocation_layer::LikesBetree_v::add_betree_likes(
                new_addrs,
                path_addrs,
            );
        path_addrs.to_multiset_ensures();
        crate::allocation_layer::Likes_v::to_au_likes_domain(
            added_tree_likes,
        );
        assert(added_tree_likes.dom()
            == new_addrs.repr() + path_addrs.to_set());
        assert(allocs <= post.betree.betree_aus.dom());
        let tree_deallocs = pre.betree.betree_aus.dom()
            - post.betree.betree_aus.dom();
        let source_branch_deallocs = pre.betree.branch_aus.dom()
            - post.betree.branch_aus.dom()
            - read_ref_aus(pre.betree.compactors);
        let source_summary_deallocs = summary_aus(
            pre.betree.branch_summary.restrict(source_branch_deallocs),
        );
        assert(deallocs == tree_deallocs + source_summary_deallocs);
        assert(allocs.disjoint(tree_deallocs));
        assert(source_summary_deallocs
            <= summary_aus(pre.betree.branch_summary)) by {
            pre.i().inv_branch_summary_ensures();
            let (_, pre_buffer_likes_for_finite) = pre_linked.transitive_likes();
            let model_roots_for_finite = pre_buffer_likes_for_finite.dom()
                + CompactorInput::input_roots(pre.i().compactors);
            pre.i().betree.linked.buffer_dv
                .build_branch_summary_finite(model_roots_for_finite);
            assert(pre.i().branch_summary
                == pre.i().betree.linked.buffer_dv
                    .build_branch_summary(model_roots_for_finite));
            lemma_values_finite(pre.betree.branch_summary);
            let dropped = pre.betree.branch_summary.restrict(
                source_branch_deallocs,
            );
            crate::betree::Utils_v::lemma_subset_finite(
                pre.betree.branch_summary.dom(),
                dropped.dom(),
            );
            lemma_values_finite(dropped);
            assert forall |au: AU|
                #[trigger] summary_aus(dropped).contains(au)
                implies summary_aus(pre.betree.branch_summary).contains(au)
            by {
                let summary = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
                    dropped.values(),
                    au,
                );
                assert(pre.betree.branch_summary.values().contains(summary));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    summary,
                );
            };
        };
        assert(allocs.disjoint(source_summary_deallocs));
        assert(allocs.disjoint(deallocs));
        assert(post.betree.betree_aus.dom()
            <= pre.betree.betree_aus.dom() + allocs);
        assert(post.betree.betree_aus.dom().disjoint(
            summary_aus(pre.betree.branch_summary),
        ));

        let stable_aus = pre.betree.betree_aus.dom() - deallocs;
        let stable_addrs = addresses_in_aus(stable_aus);
        assert(stable_aus.disjoint(allocs));
        assert(stable_aus.disjoint(deallocs));
        addresses_in_aus_preserves_disjointness(stable_aus, allocs);
        addresses_in_aus_preserves_disjointness(stable_aus, deallocs);
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            stable_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            stable_addrs,
        );
        CachingDisk::State::access_visible_effect(
            witness.expanded,
            witness.accessed,
            reads,
            writes,
        );
        CachingDisk::State::forget_effect(
            witness.accessed,
            new_disk,
            deallocs - guard_aus,
        );
        flushed.tree_likes_domain(flushed.the_ranking());
        crate::allocation_layer::Likes_v::to_au_likes_domain(
            flushed_tree_likes,
        );
        assert forall |addr: Address|
            #[trigger] post_tree.dv.entries.contains_key(addr)
            implies post.visible_betree_entries().contains_key(addr)
        by {
            assert(flushed.dv.entries.contains_key(addr));
            assert(flushed_tree_likes.contains(addr));
            assert(post.betree.betree_aus.dom().contains(addr.au));
            if writes.contains_key(addr) {
                assert(allocs.contains(addr.au));
                assert(!deallocs.contains(addr.au));
                assert(witness.accessed.visible().contains_key(addr));
                assert(new_disk.visible().contains_key(addr));
                assert(to_betree_nodes(new_disk.visible()).contains_key(addr));
            } else {
                assert(pre_tree.dv.entries.contains_key(addr));
                assert(!deallocs.contains(addr.au));
                assert(stable_addrs.contains(addr));
                assert(to_betree_nodes(new_disk.visible()).restrict(
                    stable_addrs,
                ).contains_key(addr));
            }
        };
        assert(post_tree.dv.entries <= post.visible_betree_entries()) by {
            assert forall |addr: Address|
                #[trigger] post_tree.dv.entries.contains_key(addr)
                implies post.visible_betree_entries().contains_key(addr)
                    && post_tree.dv.entries[addr]
                        == post.visible_betree_entries()[addr]
            by {
                assert(flushed.dv.entries.contains_key(addr));
                assert(flushed.reachable_betree_addrs().contains(addr));
                assert(flushed_tree_likes.contains(addr));
                assert(post.betree.betree_aus.dom().contains(addr.au));
                if writes.contains_key(addr) {
                    assert(allocs.contains(addr.au));
                    assert(!deallocs.contains(addr.au));
                    assert(witness.accessed.visible()[addr] == writes[addr]);
                    assert(new_disk.visible()[addr] == writes[addr]);
                    assert(to_betree_nodes(new_disk.visible()).contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible())[addr]
                        == betree_writes[addr]);
                    assert(flushed.dv.entries[addr] == betree_writes[addr]);
                } else {
                    assert(pre_tree.dv.entries.contains_key(addr));
                    assert(pre_tree.dv.entries <= pre.visible_betree_entries());
                    assert(pre.betree.betree_aus.dom().contains(addr.au));
                    assert(!tree_deallocs.contains(addr.au));
                    assert(!source_summary_deallocs.contains(addr.au));
                    assert(!deallocs.contains(addr.au));
                    assert(stable_addrs.contains(addr));
                    assert(to_betree_nodes(pre.disk.visible()).restrict(
                        stable_addrs,
                    ).contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_addrs,
                    ).contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_addrs,
                    ) == to_betree_nodes(pre.disk.visible()).restrict(
                        stable_addrs,
                    ));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_addrs,
                    )[addr] == to_betree_nodes(pre.disk.visible()).restrict(
                        stable_addrs,
                    )[addr]);
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_addrs,
                    )[addr] == to_betree_nodes(new_disk.visible())[addr]);
                    assert(to_betree_nodes(pre.disk.visible()).restrict(
                        stable_addrs,
                    )[addr] == to_betree_nodes(pre.disk.visible())[addr]);
                    assert(flushed.dv.entries[addr]
                        == pre_linked.dv.entries[addr]);
                    assert(pre_linked.dv.entries[addr]
                        == pre_tree.dv.entries[addr]);
                    assert(to_betree_nodes(new_disk.visible())[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]);
                }
                assert(post_tree.dv.entries[addr]
                    == flushed.dv.entries[addr]);
            };
        };
        reachable_tight_betree_is_candidate(
            flushed,
            post.betree.root,
            post.visible_betree_entries(),
        );
        tight_betree_of_equals_candidate(
            post.betree.root,
            post.visible_betree_entries(),
            post_tree,
        );
        assert(post.tight_betree_i() == post_tree);

        assert(set_addrs_disjoint_aus(flushed.dv.entries.dom())) by {
            assert(flushed.dv.entries.dom()
                == pre_tree.dv.entries.dom() + writes.dom());
            assert(set_addrs_disjoint_aus(pre_tree.dv.entries.dom()));
            assert forall |left: Address, right: Address|
                flushed.dv.entries.dom().contains(left)
                    && flushed.dv.entries.dom().contains(right)
                    && left != right
                implies #[trigger] addrs_with_different_au(left, right)
            by {
                if writes.contains_key(left) || writes.contains_key(right) {
                    if writes.contains_key(left) && writes.contains_key(right) {
                        if new_addrs.repr().contains(left)
                            && new_addrs.repr().contains(right)
                        {
                            assert(new_addrs.addrs_in_disjoint_aus());
                        } else if path_addrs.to_set().contains(left)
                            && path_addrs.to_set().contains(right)
                        {
                            let i = choose |i: int|
                                0 <= i < path_addrs.len()
                                    && path_addrs[i] == left;
                            let j = choose |j: int|
                                0 <= j < path_addrs.len()
                                    && path_addrs[j] == right;
                            assert(i != j);
                            assert(path_addrs[i].au != path_addrs[j].au);
                        } else {
                            let direct = if new_addrs.repr().contains(left) {
                                left
                            } else {
                                right
                            };
                            let path_addr = if new_addrs.repr().contains(left) {
                                right
                            } else {
                                left
                            };
                            crate::disk::GenericDisk_v::to_aus_domain(
                                new_addrs.repr(),
                            );
                            crate::disk::GenericDisk_v::to_aus_domain(
                                path_addrs.to_set(),
                            );
                            assert(to_aus(new_addrs.repr()).contains(direct.au));
                            assert(seq_addrs_to_aus(path_addrs)
                                .contains(path_addr.au));
                        }
                    } else {
                        let fresh = if writes.contains_key(left) { left } else { right };
                        let old = if writes.contains_key(left) { right } else { left };
                        assert(allocs.contains(fresh.au));
                        assert(pre.betree.betree_aus.dom().contains(old.au));
                    }
                }
            };
        };
        direct_au_restrict_is_domain(
            flushed.dv.entries,
            post_tree.dv.entries.dom(),
        );
        assert(crate::allocation_layer::Likes_v::restrict_domain_au(
            flushed.dv.entries,
            post.i().betree_aus.dom(),
        ) == post.i().betree.linked.dv.entries.dom()) by {
            assert(post.i().betree_aus.dom()
                == to_aus(post_tree.dv.entries.dom()));
        };

        let pre_roots = pre.semantic_branch_roots();
        let post_roots = post.semantic_branch_roots();
        let (_, pre_branch_likes) = pre_linked.transitive_likes();
        crate::allocation_layer::LikesBetree_v::LikesBetree::State::post_flush_likes_ensures(
            pre.i().betree,
            model_post_vars,
            linked_path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
        );
        pre_linked.tree_likes_domain(pre_linked.the_ranking());
        pre_linked.buffer_likes_domain(
            pre_linked.tree_likes(pre_linked.the_ranking()),
        );
        flushed.tree_likes_domain(flushed.the_ranking());
        flushed.buffer_likes_domain(flushed_tree_likes);
        assert(pre_roots == pre_branch_likes.dom()
            + CompactorInput::input_roots(pre.betree.compactors)) by {
            assert(pre_linked.reachable_buffer_addrs()
                == pre_tree.reachable_buffer_addrs()) by {
                assert(pre_linked.dv == pre_tree.dv);
                assert(pre_linked.reachable_betree_addrs()
                    == pre_tree.reachable_betree_addrs());
                pre_linked.same_reachable_betree_addrs_implies_same_buffer_addrs(
                    pre_tree,
                );
            };
        };
        assert(post_tree.reachable_buffer_addrs()
            == flushed.reachable_buffer_addrs()) by {
            flushed.same_reachable_betree_addrs_implies_same_buffer_addrs(
                post_tree,
            );
        };
        assert(post_roots == flushed_branch_likes.dom()
            + CompactorInput::input_roots(pre.betree.compactors)) by {
            assert(post.betree.compactors == pre.betree.compactors);
        };
        assert(post_roots <= pre_roots) by {
            assert(flushed_branch_likes.dom() <= pre_branch_likes.dom());
        };

        let branch_deallocs = pre.betree.branch_aus.dom()
            - post.betree.branch_aus.dom()
            - read_ref_aus(pre.betree.compactors);
        assert(to_aus(pre_roots - post_roots) == branch_deallocs) by {
            crate::allocation_layer::Likes_v::to_au_likes_domain(
                flushed_branch_likes,
            );
            crate::allocation_layer::Likes_v::to_au_likes_domain(
                pre_branch_likes,
            );
            let compactor_roots = CompactorInput::input_roots(
                pre.betree.compactors,
            );
            assert(pre_branch_likes.dom() - flushed_branch_likes.dom()
                - compactor_roots == pre_roots - post_roots);
            crate::disk::GenericDisk_v::to_aus_subtract(
                pre_branch_likes.dom(),
                flushed_branch_likes.dom(),
            );
            crate::disk::GenericDisk_v::to_aus_subtract(
                pre_branch_likes.dom() - flushed_branch_likes.dom(),
                compactor_roots,
            );
        };
        let deallocated_summary = pre.betree.branch_summary.restrict(
            branch_deallocs,
        );
        assert(post.betree.branch_summary
            == pre.betree.branch_summary.remove_keys(branch_deallocs));
        assert(deallocs == (pre.betree.betree_aus.dom()
            - post.betree.betree_aus.dom())
            + summary_aus(deallocated_summary));
        let summary_deallocs = summary_aus(deallocated_summary);
        assert(summary_deallocs <= deallocs);
        let post_summary_aus = summary_aus(post.betree.branch_summary);
        pre.i().inv_branch_summary_ensures();
        pre.semantic_sealed_branch_disk().build_branch_summary_finite(pre_roots);
        lemma_values_finite(pre.betree.branch_summary);
        summary_partition_disjoint(
            pre.betree.branch_summary,
            branch_deallocs,
        );
        assert(post_summary_aus.disjoint(summary_deallocs));
        assert(post.betree.branch_summary.values()
            <= pre.betree.branch_summary.values()) by {
            assert forall |summary: Summary|
                #[trigger] post.betree.branch_summary.values().contains(summary)
                implies pre.betree.branch_summary.values().contains(summary)
            by {
                let root_au = choose |root_au: AU|
                    post.betree.branch_summary.contains_key(root_au)
                        && post.betree.branch_summary[root_au] == summary;
                assert(pre.betree.branch_summary.contains_key(root_au));
            };
        };
        assert(post_summary_aus
            <= summary_aus(pre.betree.branch_summary)) by {
            crate::betree::Utils_v::lemma_subset_finite(
                pre.betree.branch_summary.dom(),
                post.betree.branch_summary.dom(),
            );
            lemma_values_finite(post.betree.branch_summary);
            assert forall |au: AU| #[trigger] post_summary_aus.contains(au)
                implies summary_aus(pre.betree.branch_summary).contains(au)
            by {
                let summary = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
                    post.betree.branch_summary.values(),
                    au,
                );
                assert(pre.betree.branch_summary.values().contains(summary));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    summary,
                );
            };
        };
        assert(post_summary_aus.disjoint(allocs));
        assert(post_summary_aus.disjoint(deallocs)) by {
            assert(post_summary_aus.disjoint(
                pre.betree.betree_aus.dom() - post.betree.betree_aus.dom(),
            ));
        };
        addresses_in_aus_preserves_disjointness(post_summary_aus, allocs);
        addresses_in_aus_preserves_disjointness(post_summary_aus, deallocs);
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            addresses_in_aus(post_summary_aus),
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            addresses_in_aus(post_summary_aus),
        );
        assert(post.visible_sealed_branch_disk().entries
            == pre.visible_sealed_branch_disk().entries.restrict(
                addresses_in_aus(post_summary_aus),
            )) by {
            assert_maps_equal!(
                post.visible_sealed_branch_disk().entries,
                pre.visible_sealed_branch_disk().entries.restrict(
                    addresses_in_aus(post_summary_aus),
                ),
                addr => {}
            );
        };
        semantic_sealed_branch_disk_prune(
            pre,
            post,
            pre_roots,
            post_roots,
            branch_deallocs,
            summary_deallocs,
        );

        assert(flushed.valid_view(post.linked_i()));
        assert(post.i().betree.memtable == pre.i().betree.memtable);
        assert(LinkedBetreeVars::State::internal_flush(
            pre.i().betree,
            post.i().betree,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            post.i().betree.linked,
            linked_path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
        ));
        assert(deallocs.disjoint(pre.i().branch_allocator_aus())) by {
            assert(tree_deallocs <= pre.i().betree_aus.dom());
            assert(source_summary_deallocs
                <= summary_aus(pre.i().branch_summary));
            assert(pre.i().betree_aus.dom()
                .disjoint(pre.i().branch_allocator_aus()));
            assert(summary_aus(pre.i().branch_summary)
                .disjoint(pre.i().branch_allocator_aus()));
        };
        assert(post.i().wip_branches == pre.i().wip_branches) by {
            assert_seqs_equal!(
                post.wip_branches_i(),
                pre.wip_branches_i(),
                idx => {
                    let cached = pre.betree.wip_branches[idx];
                    let allocated = mini_allocator_allocated_addrs(
                        cached.mini_allocator,
                    );
                    assert(post.betree.wip_branches[idx] == cached);
                    AllocationBulkBranch::alloc_aus_ensures(
                        pre.i().wip_branches,
                        idx,
                    );
                    assert(cached.mini_allocator.all_aus()
                        <= pre.i().branch_allocator_aus());
                    assert(allocs.disjoint(cached.mini_allocator.all_aus()));
                    assert(deallocs.disjoint(cached.mini_allocator.all_aus()));
                    mini_allocator_allocated_addrs_subset_all_aus(
                        cached.mini_allocator,
                    );
                    addresses_in_aus_preserves_disjointness(
                        cached.mini_allocator.all_aus(),
                        allocs,
                    );
                    addresses_in_aus_preserves_disjointness(
                        cached.mini_allocator.all_aus(),
                        deallocs,
                    );
                    disk_access_for_alloc_visible_outside_alloc_dealloc(
                        pre.disk,
                        new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
                        allocated,
                    );
                    to_branch_nodes_restrict_agrees(
                        new_disk.visible(),
                        pre.disk.visible(),
                        allocated,
                    );
                }
            );
        };
        assert(lbl.i(pre) is Internal);
        assert(pre.i().is_fresh(allocs));
        assert(new_addrs.addrs_in_disjoint_aus());
        assert(to_aus(new_addrs.repr()).disjoint(
            seq_addrs_to_aus(path_addrs),
        ));
        assert(seq_addrs_disjoint_aus(path_addrs));
        assert(post.i().betree_aus == expected_betree_aus);
        assert(post.i().branch_aus == expected_branch_aus);
        assert(post.i().branch_summary
            == pre.i().branch_summary.remove_keys(branch_deallocs));
        assert(post.i().compactors == pre.i().compactors);
        let target_post_summary_aus = summary_aus(post.i().branch_summary);
        let target_kept_domain =
            crate::allocation_layer::Likes_v::restrict_domain_au(
                pre.i().betree.linked.buffer_dv.entries,
                target_post_summary_aus,
            );
        assert(target_post_summary_aus == post_summary_aus);
        assert(post.i().betree.linked.buffer_dv.entries
            == pre.i().betree.linked.buffer_dv.entries.restrict(
                target_kept_domain,
            ));
        assert(post.i().betree.linked.buffer_dv.repr()
            == target_kept_domain);
        assert(crate::allocation_layer::Likes_v::restrict_domain_au(
            pre.i().betree.linked.buffer_dv.entries,
            target_post_summary_aus,
        ) == post.i().betree.linked.buffer_dv.repr());
        let target_flushed = LinkedBetreeVars::State::post_flush(
            linked_path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
        );
        let (target_betree_aus, target_branch_aus) =
            crate::allocation_layer::AllocationBetree_v::AllocationBetree::State::internal_flush_au_likes(
                linked_path,
                child_idx,
                buffer_gc,
                new_addrs,
                path_addrs,
                pre.i().betree_aus,
                pre.i().branch_aus,
            );
        let target_tree_deallocs = pre.i().betree_aus.dom()
            - target_betree_aus.dom();
        let target_branch_deallocs = pre.i().branch_aus.dom()
            - target_branch_aus.dom()
            - read_ref_aus(pre.i().compactors);
        let target_summary = pre.i().branch_summary.remove_keys(
            target_branch_deallocs,
        );
        let target_dropped = pre.i().branch_summary.restrict(
            target_branch_deallocs,
        );
        assert(target_flushed == flushed);
        assert(target_betree_aus == post.i().betree_aus);
        assert(target_branch_aus == post.i().branch_aus);
        assert(target_tree_deallocs == tree_deallocs);
        assert(target_branch_deallocs == branch_deallocs);
        assert(target_summary == post.i().branch_summary);
        assert(summary_aus(target_dropped) == summary_deallocs);
        assert(deallocs == (pre.i().betree_aus.dom()
            - post.i().betree_aus.dom())
            + summary_aus(
                pre.i().branch_summary.restrict(branch_deallocs),
            ));
        assert(AllocationBranchBetree::State::internal_flush(
            pre.i(),
            post.i(),
            lbl.i(pre),
            post.i().betree,
            linked_path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
        ));
        pre.wip_alloc_aus_agree();
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            == pre.i().branch_allocator_aus());
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(allocs)) by {
            assert(pre.i().is_fresh(allocs));
        }
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(deallocs));
        assert forall |input_idx: int|
            0 <= input_idx < pre.betree.compactors.len()
            implies {
                let input_aus = #[trigger]
                    pre.betree.compactor_input_aus(input_idx);
                &&& post.betree.compactor_input_aus(input_idx)
                    == input_aus
                &&& to_branch_nodes(post.disk.visible()).restrict(
                    addresses_in_aus(input_aus),
                ) == to_branch_nodes(pre.disk.visible()).restrict(
                    addresses_in_aus(input_aus),
                )
            }
        by {
            let roots = pre.betree.compactors[input_idx]
                .input_buffers.addrs.to_set();
            let root_aus = to_aus(roots);
            let root_sets = Seq::new(
                pre.betree.compactors.len(),
                |i: int| pre.betree.compactors[i]
                    .input_buffers.addrs.to_set(),
            );
            crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
                root_sets,
                input_idx,
            );
            crate::disk::GenericDisk_v::to_aus_preserves_lte(
                roots,
                CompactorInput::input_roots(pre.betree.compactors),
            );
            assert(root_aus <= read_ref_aus(pre.betree.compactors)) by {
                assert forall |au: AU| #[trigger] root_aus.contains(au)
                    implies read_ref_aus(pre.betree.compactors).contains(au)
                by {
                    let root = choose |root: Address|
                        roots.contains(root) && root.au == au;
                    assert(CompactorInput::input_roots(
                        pre.betree.compactors,
                    ).contains(root));
                }
            }
            assert(root_aus.disjoint(branch_deallocs));
            assert(post.betree.branch_summary.restrict(root_aus)
                == pre.betree.branch_summary.restrict(root_aus)) by {
                assert_maps_equal!(
                    post.betree.branch_summary.restrict(root_aus),
                    pre.betree.branch_summary.restrict(root_aus),
                    au => {}
                );
            }
            assert(post.betree.compactor_input_aus(input_idx)
                == pre.betree.compactor_input_aus(input_idx));
            crate::betree::Utils_v::lemma_subset_finite(
                pre.betree.branch_summary.dom(),
                post.betree.branch_summary.dom(),
            );
            summary_aus_restrict_subset(
                post.betree.branch_summary,
                root_aus,
            );
            let input_aus = pre.betree.compactor_input_aus(input_idx);
            assert(input_aus <= post_summary_aus);
            assert(addresses_in_aus(input_aus)
                <= addresses_in_aus(post_summary_aus)) by {
                assert forall |addr: Address|
                    #[trigger] addresses_in_aus(input_aus).contains(addr)
                    implies addresses_in_aus(post_summary_aus)
                        .contains(addr)
                by {
                }
            }
            map_restrict_equal_on_subset(
                to_branch_nodes(post.disk.visible()),
                to_branch_nodes(pre.disk.visible()),
                addresses_in_aus(post_summary_aus),
                addresses_in_aus(input_aus),
            );
        }
        Self::unchanged_compactor_receipts_preserve_selected_views(
            pre,
            post,
        );
        Self::unchanged_wips_preserve_staged_nodes_after_access(
            pre,
            post,
            lbl,
            new_disk,
            access,
        );
    }

    proof fn compact_begin_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        path: LoadedBetreePath,
        start: nat,
        end: nat,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_access(
                pre, post, lbl, new_betree, post.disk,
            ),
            access == lbl.arrow_InternalAccess_access(),
            CachedBranchBetree::State::compact_begin(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                path,
                start,
                end,
                access.loaded_betree_reads(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::internal_compact_begin(
                pre.i(),
                post.i(),
                lbl.i(pre),
                Path {
                    linked: pre.linked_i(),
                    key: path.key,
                    depth: path.depth(),
                },
                start,
                end,
                post.i().compactors.last(),
            ),
    {
        CachingDiskBranchBetree::State::internal_access_effect(
            pre, post, lbl, new_betree, post.disk,
        );
        access.cached_only_betree_is_only_betree();
        access.cached_read_only_is_read_only();
        CachingDisk::State::access_effect(
            pre.disk, post.disk, access.reads(), access.writes(),
        );
        assert(post.disk == pre.disk);

        let reads = access.betree_reads;
        let linked = pre.linked_i();
        let linked_path = Path {
            linked,
            key: path.key,
            depth: path.depth(),
        };
        let input = CompactorInput {
            input_buffers: path.target().node.buffers.slice(start as int, end as int),
            offset_map: path.target().node.make_offset_map().decrement(start),
        };

        CachingDisk::State::access_effect(
            pre.disk,
            pre.disk,
            access.reads(),
            access.writes(),
        );
        assert(reads <= access.reads());
        assert(reads <= pre.disk.cache) by {
            assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                implies pre.disk.cache.contains_key(addr)
                    && reads[addr] == pre.disk.cache[addr]
            by {
                assert(access.reads().contains_key(addr));
                assert(reads[addr] == access.reads()[addr]);
            };
        }
        pre.linked_i_tight_tree_facts();
        assert(linked.dv.entries <= to_betree_nodes(pre.disk.visible())) by {
            assert forall |addr: Address| #[trigger] linked.dv.entries.contains_key(addr)
                implies to_betree_nodes(pre.disk.visible()).contains_key(addr)
                    && linked.dv.entries[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]
            by {
                assert(pre.visible_betree_entries().contains_key(addr));
            };
        }
        loaded_betree_path_matches_linked(
            pre.disk,
            linked,
            reads,
            path,
            path.depth(),
        );
        assert(linked_path.valid());
        assert(linked_path.target().root() == path.target().node);
        assert(AllocationBranchBetree::State::valid_compactor_input(
            linked_path,
            start,
            end,
            input,
        ));

        assert(post.disk == pre.disk);
        assert(post.betree.compactors == pre.betree.compactors.push(input));
        assert(post.tight_betree_i() == pre.tight_betree_i());
        assert(CompactorInput::input_roots(post.betree.compactors)
            == CompactorInput::input_roots(pre.betree.compactors)
                + input.input_buffers.addrs.to_set()) by {
            let roots = Seq::new(
                post.betree.compactors.len(),
                |i: int| post.betree.compactors[i].input_buffers.addrs.to_set(),
            );
            let pre_roots = Seq::new(
                pre.betree.compactors.len(),
                |i: int| pre.betree.compactors[i].input_buffers.addrs.to_set(),
            );
            assert(roots.drop_last() == pre_roots);
            union_seq_of_sets_push(pre_roots, input.input_buffers.addrs.to_set());
        }
        assert(input.input_buffers.addrs.to_set()
            <= pre.tight_betree_i().reachable_buffer_addrs()) by {
            let tree_addr = path.target().addr;
            assert(pre.tight_betree_i().reachable_betree_addrs().contains(tree_addr)) by {
                assert(pre.tight_betree_i().dv.entries.dom()
                    == pre.tight_betree_i().reachable_betree_addrs());
                assert(pre.tight_betree_i().dv.entries.contains_key(tree_addr));
            }
            assert forall |root: Address|
                #[trigger] input.input_buffers.addrs.to_set().contains(root)
                implies pre.tight_betree_i().reachable_buffer_addrs().contains(root)
            by {
                assert(path.target().node.buffers.contains(root));
                assert(pre.tight_betree_i().dv.entries[tree_addr]
                    == path.target().node);
                assert(pre.tight_betree_i().reachable_buffer(tree_addr, root));
            };
        }
        assert(post.semantic_branch_roots() == pre.semantic_branch_roots());
        assert(post.semantic_sealed_branch_disk()
            == pre.semantic_sealed_branch_disk());
        assert(post.linked_i() == pre.linked_i());
        assert(post.wip_branches_i() == pre.wip_branches_i());
        assert(post.i().betree == pre.i().betree);
        assert(post.i().compactors == pre.i().compactors.push(input));
        assert(post.i().compactors.last() == input);
        assert(post.staged_nodes_inv());
        assert(post.sealed_wip_nodes_inv());
        assert(post.compactor_receipts_inv()) by {
            assert(post.betree.compactor_receipts
                == pre.betree.compactor_receipts.push(Map::empty()));
            assert forall |idx: int| 0 <= idx < post.betree.compactors.len()
                implies {
                    let receipt = #[trigger]
                        post.betree.compactor_receipts[idx];
                    &&& receipt.dom() <= addresses_in_aus(
                        post.betree.compactor_input_aus(idx),
                    )
                    &&& BranchDiskView { entries: receipt }.agrees_with_disk(
                        BranchDiskView {
                            entries: to_branch_nodes(post.disk.visible()),
                        },
                    )
                } by {
                if idx < pre.betree.compactors.len() {
                    assert(post.betree.compactors[idx]
                        == pre.betree.compactors[idx]);
                    assert(post.betree.compactor_receipts[idx]
                        == pre.betree.compactor_receipts[idx]);
                    assert(post.betree.compactor_input_aus(idx)
                        == pre.betree.compactor_input_aus(idx));
                } else {
                    assert(idx == pre.betree.compactors.len());
                    assert(post.betree.compactor_receipts[idx]
                        == Map::<Address, BranchNode>::empty());
                }
            };
        }
    }

    proof fn compact_scan_page_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        input_idx: int,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_access(
                pre, post, lbl, new_betree, post.disk,
            ),
            access == lbl.arrow_InternalAccess_access(),
            CachedBranchBetree::State::compact_scan_page(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                input_idx,
                access.loaded_branch_reads(),
            ),
        ensures
            post.refinement_inv(),
            post.i() == pre.i(),
    {
        CachingDiskBranchBetree::State::internal_access_effect(
            pre, post, lbl, new_betree, post.disk,
        );
        access.cached_only_branch_is_only_branch();
        access.cached_read_only_is_read_only();
        CachingDisk::State::access_effect(
            pre.disk, post.disk, access.reads(), access.writes(),
        );
        assert(post.disk == pre.disk);
        CachingDisk::State::access_effect(
            pre.disk,
            pre.disk,
            access.reads(),
            access.writes(),
        );
        assert(post.disk == pre.disk);
        assert(post.betree == new_betree);
        assert(access.betree_reads.is_empty());
        assert(access.betree_writes.is_empty());
        assert(access.branch_writes.is_empty());
        assert(access.writes().is_empty());
        assert(access.reads() == access.branch_reads);
        let loaded = access.loaded_branch_reads();
        let visible = BranchDiskView {
            entries: to_branch_nodes(pre.disk.visible()),
        };
        assert(BranchDiskView { entries: loaded }
            .agrees_with_disk(visible)) by {
            assert forall |addr: Address|
                #[trigger] loaded.contains_key(addr)
                    && visible.entries.contains_key(addr)
                implies loaded[addr] == visible.entries[addr]
            by {
                assert(access.branch_reads.contains_key(addr));
                assert(access.reads().contains_key(addr));
                CachingDisk::State::access_read_matches_visible(
                    pre.disk,
                    pre.disk,
                    access.reads(),
                    access.writes(),
                    addr,
                );
            };
        };

        assert(post.betree.compactors == pre.betree.compactors);
        assert(post.betree.branch_summary == pre.betree.branch_summary);
        assert(post.betree.compactor_receipts.len()
            == post.betree.compactors.len());
        assert(post.compactor_receipts_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.compactors.len()
                implies {
                    let receipt = #[trigger]
                        post.betree.compactor_receipts[idx];
                    &&& receipt.dom() <= addresses_in_aus(
                        post.betree.compactor_input_aus(idx),
                    )
                    &&& BranchDiskView { entries: receipt }
                        .agrees_with_disk(BranchDiskView {
                            entries: to_branch_nodes(post.disk.visible()),
                        })
                }
            by {
                if idx == input_idx {
                    let old_receipt = pre.betree.compactor_receipts[idx];
                    let new_receipt = old_receipt.union_prefer_right(loaded);
                    assert(post.betree.compactor_receipts[idx]
                        == new_receipt);
                    assert(old_receipt.dom() <= addresses_in_aus(
                        pre.betree.compactor_input_aus(idx),
                    ));
                    assert(loaded.dom() <= addresses_in_aus(
                        pre.betree.compactor_input_aus(idx),
                    ));
                    assert(new_receipt.dom() <= addresses_in_aus(
                        post.betree.compactor_input_aus(idx),
                    ));
                    assert(BranchDiskView { entries: new_receipt }
                        .agrees_with_disk(visible)) by {
                        assert forall |addr: Address|
                            #[trigger] new_receipt.contains_key(addr)
                                && visible.entries.contains_key(addr)
                            implies new_receipt[addr]
                                == visible.entries[addr]
                        by {
                            if loaded.contains_key(addr) {
                            } else {
                                assert(old_receipt.contains_key(addr));
                            }
                        };
                    };
                } else {
                    assert(post.betree.compactor_receipts[idx]
                        == pre.betree.compactor_receipts[idx]);
                }
            };
        };
        assert(post.semantic_selector_inv());
        assert(post.staged_nodes_inv());
        assert(post.sealed_wip_nodes_inv());
        assert(post.wip_branches_i() == pre.wip_branches_i());
        assert(post.i() == pre.i());
        reveal(CachingDiskBranchBetree::State::next);
        reveal(CachingDiskBranchBetree::State::next_by);
        assert(CachingDiskBranchBetree::State::next_by(
            pre,
            post,
            lbl,
            CachingDiskBranchBetree::Step::internal_access(
                new_betree,
                post.disk,
            ),
        ));
        assert(CachingDiskBranchBetree::State::next(pre, post, lbl));
        CachingDiskBranchBetree::State::inv_next(pre, post, lbl);
        assert(post.i().inv());
    }

    proof fn compact_abort_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        input_idx: int,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            CachedBranchBetree::State::compact_abort(
                pre.betree, new_betree, lbl.cached_i(),
                input_idx,
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::internal_compact_abort(
                pre.i(),
                post.i(),
                lbl.i(pre),
                input_idx,
                post.i().betree,
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        let effect_access = lbl.arrow_InternalAllocAccess_access();
        effect_access.cached_empty_is_empty();
        assert(lbl.arrow_InternalAllocAccess_allocs().is_empty());
        assert(effect_access.reads() == Map::<Address, RawPage>::empty());
        assert(effect_access.writes() == Map::<Address, RawPage>::empty());
        disk_access_empty_alloc_access_is_forget(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAllocAccess_deallocs(),
            lbl.arrow_InternalAllocAccess_guard_aus(),
        );

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let forgotten_aus = deallocs - guard_aus;
        let new_compactors = pre.betree.compactors.remove(input_idx);
        let released = read_ref_aus(pre.betree.compactors)
            - read_ref_aus(new_compactors);
        let branch_deallocs = released - pre.betree.branch_aus.dom();
        let deallocated_summary = pre.betree.branch_summary.restrict(
            branch_deallocs,
        );
        let new_summary = pre.betree.branch_summary.remove_keys(
            branch_deallocs,
        );
        let pre_tree = pre.tight_betree_i();
        let pre_buffer = pre.semantic_sealed_branch_disk();
        let post_summary_aus = summary_aus(new_summary);
        let kept_domain = crate::allocation_layer::Likes_v::restrict_domain_au(
            pre_buffer.entries,
            post_summary_aus,
        );
        let expected_buffer = BufferDisk {
            entries: pre_buffer.entries.restrict(kept_domain),
        };
        let pre_linked = pre.linked_i();
        let (tree_likes, branch_likes) = pre_linked.transitive_likes();
        let pre_roots = branch_likes.dom()
            + CompactorInput::input_roots(pre.i().compactors);
        let post_roots = branch_likes.dom()
            + CompactorInput::input_roots(post.i().compactors);

        assert(allocs.is_empty());
        assert(deallocs == summary_aus(deallocated_summary));
        assert(post.disk == new_disk);
        assert(post.betree == new_betree);
        assert(post.betree.root == pre.betree.root);
        assert(post.betree.memtable == pre.betree.memtable);
        assert(post.betree.betree_aus == pre.betree.betree_aus);
        assert(post.betree.branch_aus == pre.betree.branch_aus);
        assert(post.betree.wip_branches == pre.betree.wip_branches);
        assert(post.betree.compactors == new_compactors);
        assert(post.betree.branch_summary == new_summary);

        pre.i().inv_branch_summary_ensures();
        pre_buffer.build_branch_summary_finite(pre_roots);
        assert(pre.i().betree_aus.dom().disjoint(
            summary_aus(pre.i().branch_summary),
        ));
        assert(deallocs <= summary_aus(pre.betree.branch_summary)) by {
            lemma_values_finite(pre.betree.branch_summary);
            crate::betree::Utils_v::lemma_subset_finite(
                pre.betree.branch_summary.dom(),
                deallocated_summary.dom(),
            );
            lemma_values_finite(deallocated_summary);
            assert(deallocated_summary.values()
                <= pre.betree.branch_summary.values()) by {
                assert forall |summary: Summary|
                    #[trigger] deallocated_summary.values().contains(summary)
                    implies pre.betree.branch_summary.values().contains(summary)
                by {
                    let au = choose |au: AU|
                        deallocated_summary.contains_key(au)
                            && deallocated_summary[au] == summary;
                    assert(pre.betree.branch_summary.contains_key(au));
                };
            };
            assert forall |au: AU| #[trigger] deallocs.contains(au)
                implies summary_aus(pre.betree.branch_summary).contains(au)
            by {
                let summary = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
                    deallocated_summary.values(),
                    au,
                );
                assert(pre.betree.branch_summary.values().contains(summary));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    summary,
                );
            };
        };
        assert(pre.betree.betree_aus.dom().disjoint(deallocs));
        assert(pre.betree.betree_aus.dom().disjoint(forgotten_aus));
        addresses_in_aus_preserves_disjointness(
            pre.betree.betree_aus.dom(),
            forgotten_aus,
        );
        disk_forget_visible_outside_aus(
            pre.disk,
            new_disk,
            forgotten_aus,
            addresses_in_aus(pre.betree.betree_aus.dom()),
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            addresses_in_aus(pre.betree.betree_aus.dom()),
        );
        assert(post.visible_betree_entries() == pre.visible_betree_entries());
        assert(post.tight_betree_i() == pre_tree);

        assert(branch_likes.dom() == pre_tree.reachable_buffer_addrs()) by {
            pre_linked.tree_likes_domain(pre_linked.the_ranking());
            pre_linked.buffer_likes_domain(tree_likes);
            assert(pre_linked.dv == pre_tree.dv);
            assert(pre_linked.reachable_betree_addrs()
                == pre_tree.reachable_betree_addrs()) by {
                pre.linked_i_tight_tree_facts();
                assert(pre_linked.dv.entries.dom()
                    == pre_linked.reachable_betree_addrs());
                assert(pre_tree.dv.entries.dom()
                    == pre_tree.reachable_betree_addrs());
            };
            pre_linked.same_reachable_betree_addrs_implies_same_buffer_addrs(
                pre_tree,
            );
        };
        assert(pre_roots == pre.semantic_branch_roots());
        CompactorInput::input_roots_remove_subset(
            pre.betree.compactors,
            input_idx,
        );
        assert(post_roots <= pre_roots);
        assert(to_aus(pre_roots - post_roots) == branch_deallocs) by {
            let pre_compactor_roots = CompactorInput::input_roots(
                pre.betree.compactors,
            );
            let post_compactor_roots = CompactorInput::input_roots(
                new_compactors,
            );
            assert(pre_roots - post_roots
                == pre_compactor_roots - post_compactor_roots
                    - branch_likes.dom());
            crate::disk::GenericDisk_v::to_aus_subtract(
                pre_compactor_roots,
                post_compactor_roots,
            );
            crate::allocation_layer::Likes_v::to_au_likes_domain(
                branch_likes,
            );
            crate::disk::GenericDisk_v::to_aus_subtract(
                pre_compactor_roots - post_compactor_roots,
                branch_likes.dom(),
            );
        };
        assert(post.semantic_branch_roots() == post_roots) by {
            assert(post.tight_betree_i() == pre_tree);
        };

        pre.i().inv_implies_wf_branch_dv();
        assert(pre_buffer.to_branch_disk().wf());
        assert(pre_buffer.sealed_branch_roots(pre_roots));
        assert(crate::allocation_layer::AllocationBranchBetree_v::map_with_disjoint_values(
            pre.betree.branch_summary,
        ));
        assert(crate::disk::GenericDisk_v::addrs_closed(
            pre_buffer.entries.dom(),
            summary_aus(pre.betree.branch_summary),
        ));
        assert(pre.betree.branch_summary
            == pre_buffer.build_branch_summary(pre_roots));
        pre_buffer.build_branch_summary_remove(
            pre.betree.branch_summary,
            pre_roots,
            post_roots,
        );
        assert(new_summary == pre.betree.branch_summary.remove_keys(
            to_aus(pre_roots - post_roots),
        ));
        assert(expected_buffer.to_branch_disk().wf());
        assert(expected_buffer.sealed_branch_roots(post_roots));
        assert(new_summary == expected_buffer.build_branch_summary(post_roots));

        lemma_values_finite(pre.betree.branch_summary);
        crate::betree::Utils_v::lemma_subset_finite(
            pre.betree.branch_summary.dom(),
            new_summary.dom(),
        );
        crate::betree::Utils_v::lemma_subset_finite(
            pre.betree.branch_summary.dom(),
            deallocated_summary.dom(),
        );
        lemma_values_finite(new_summary);
        lemma_values_finite(deallocated_summary);
        summary_partition_disjoint(
            pre.betree.branch_summary,
            branch_deallocs,
        );
        assert(post_summary_aus.disjoint(deallocs));
        assert(post_summary_aus.disjoint(forgotten_aus));
        addresses_in_aus_preserves_disjointness(
            post_summary_aus,
            forgotten_aus,
        );
        disk_forget_visible_outside_aus(
            pre.disk,
            new_disk,
            forgotten_aus,
            addresses_in_aus(post_summary_aus),
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            addresses_in_aus(post_summary_aus),
        );
        assert(post.visible_sealed_branch_disk().entries
            == pre.visible_sealed_branch_disk().entries.restrict(
                addresses_in_aus(post_summary_aus),
            )) by {
            assert_maps_equal!(
                post.visible_sealed_branch_disk().entries,
                pre.visible_sealed_branch_disk().entries.restrict(
                    addresses_in_aus(post_summary_aus),
                ),
                addr => {}
            );
        };

        assert forall |root: Address| #[trigger] post_roots.contains(root)
            implies {
                &&& new_summary.contains_key(root.au)
                &&& tight_branch_exists(
                    loose_disk_for_summary(
                        post.visible_sealed_branch_disk(),
                        new_summary[root.au],
                    ),
                    root,
                    new_summary[root.au],
                )
                &&& tight_branch_of(
                    loose_disk_for_summary(
                        post.visible_sealed_branch_disk(),
                        new_summary[root.au],
                    ),
                    root,
                    new_summary[root.au],
                ) == tight_branch_of(
                    loose_disk_for_summary(
                        pre.visible_sealed_branch_disk(),
                        pre.betree.branch_summary[root.au],
                    ),
                    root,
                    pre.betree.branch_summary[root.au],
                )
            }
        by {
            expected_buffer.build_branch_summary_contains(post_roots, root);
            assert(new_summary.contains_key(root.au));
            assert(!branch_deallocs.contains(root.au));
            assert(new_summary[root.au]
                == pre.betree.branch_summary[root.au]);
            let root_summary = new_summary[root.au];
            assert(new_summary.values().contains(root_summary));
            lemma_values_finite(new_summary);
            crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                new_summary.values(),
                root_summary,
            );
            let pre_root_loose = loose_disk_for_summary(
                pre.visible_sealed_branch_disk(),
                root_summary,
            );
            let post_root_loose = loose_disk_for_summary(
                post.visible_sealed_branch_disk(),
                root_summary,
            );
            assert(post_root_loose == pre_root_loose) by {
                assert_maps_equal!(
                    post_root_loose.entries,
                    pre_root_loose.entries,
                    addr => {
                        if addresses_in_aus(root_summary).contains(addr) {
                            assert(addresses_in_aus(post_summary_aus)
                                .contains(addr));
                        }
                    }
                );
            };
            assert(pre.tight_branches_exist());
            assert(pre_roots.contains(root));
            tight_branch_of_is_candidate(pre_root_loose, root, root_summary);
            let old_branch = tight_branch_of(
                pre_root_loose,
                root,
                root_summary,
            );
            assert(tight_branch_in_loose_disk(
                post_root_loose,
                root,
                root_summary,
                old_branch,
            ));
            tight_branch_of_equals_candidate(
                post_root_loose,
                root,
                root_summary,
                old_branch,
            );
        };
        assert(post.tight_branches_exist());
        assert_maps_equal!(
            post.semantic_sealed_branch_disk().entries,
            expected_buffer.entries,
            addr => {
                if post.semantic_sealed_branch_disk().entries.contains_key(addr) {
                    let root = choose |root: Address|
                        post_roots.contains(root)
                            && tight_branch_of(
                                loose_disk_for_summary(
                                    post.visible_sealed_branch_disk(),
                                    new_summary[root.au],
                                ),
                                root,
                                new_summary[root.au],
                            ).disk_view.entries.contains_key(addr);
                    assert(pre_roots.contains(root));
                    assert(pre.semantic_sealed_branch_disk().entries
                        .contains_key(addr));
                    tight_branch_of_is_candidate(
                        loose_disk_for_summary(
                            post.visible_sealed_branch_disk(),
                            new_summary[root.au],
                        ),
                        root,
                        new_summary[root.au],
                    );
                    let branch = tight_branch_of(
                        loose_disk_for_summary(
                            post.visible_sealed_branch_disk(),
                            new_summary[root.au],
                        ),
                        root,
                        new_summary[root.au],
                    );
                    assert(branch.full_repr().contains(addr));
                    assert(branch.get_summary().contains(addr.au));
                    assert(post_summary_aus.contains(addr.au));
                    assert(kept_domain.contains(addr));
                }
                if expected_buffer.entries.contains_key(addr) {
                    assert(pre.semantic_sealed_branch_disk().entries
                        .contains_key(addr));
                    assert(post_summary_aus.contains(addr.au));
                    let old_root = choose |root: Address|
                        pre_roots.contains(root)
                            && tight_branch_of(
                                loose_disk_for_summary(
                                    pre.visible_sealed_branch_disk(),
                                    pre.betree.branch_summary[root.au],
                                ),
                                root,
                                pre.betree.branch_summary[root.au],
                            ).disk_view.entries.contains_key(addr);
                    if !post_roots.contains(old_root) {
                        assert((pre_roots - post_roots).contains(old_root));
                        crate::disk::GenericDisk_v::to_aus_domain(
                            pre_roots - post_roots,
                        );
                        assert(branch_deallocs.contains(old_root.au));
                        let old_summary = pre.betree.branch_summary[old_root.au];
                        assert(deallocated_summary.contains_key(old_root.au));
                        assert(deallocated_summary.values().contains(old_summary));
                        tight_branch_of_is_candidate(
                            loose_disk_for_summary(
                                pre.visible_sealed_branch_disk(),
                                old_summary,
                            ),
                            old_root,
                            old_summary,
                        );
                        let old_branch = tight_branch_of(
                            loose_disk_for_summary(
                                pre.visible_sealed_branch_disk(),
                                old_summary,
                            ),
                            old_root,
                            old_summary,
                        );
                        assert(old_branch.full_repr().contains(addr));
                        assert(old_summary.contains(addr.au));
                        crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                            deallocated_summary.values(),
                            old_summary,
                        );
                        assert(deallocs.contains(addr.au));
                        assert(false);
                    }
                    assert(post_roots.contains(old_root));
                    assert(post.semantic_sealed_branch_disk().entries
                        .contains_key(addr));
                }
            }
        );

        assert(post.semantic_sealed_branch_disk() == expected_buffer);
        assert(post.i().betree == LinkedBetreeVars::State::<BranchNode> {
            linked: LinkedBetree::<BranchNode> {
                buffer_dv: expected_buffer,
                ..pre.i().betree.linked
            },
            ..pre.i().betree
        });
        assert(post.i().branch_summary == new_summary);
        assert(post.i().compactors == new_compactors);
        assert(post.i().betree.memtable == pre.i().betree.memtable);
        assert(lbl.i(pre) is Internal);
        assert(read_ref_aus(pre.i().compactors)
            - read_ref_aus(post.i().compactors) == released);
        assert(released - pre.i().branch_aus.dom() == branch_deallocs);
        assert(summary_aus(
            pre.i().branch_summary.restrict(branch_deallocs),
        ) == deallocs);
        let target_new_compactors = pre.i().compactors.remove(input_idx);
        let target_released = read_ref_aus(pre.i().compactors)
            - read_ref_aus(target_new_compactors);
        let target_branch_deallocs = target_released
            - pre.i().branch_aus.dom();
        let target_summary = pre.i().branch_summary.remove_keys(
            target_branch_deallocs,
        );
        let target_summary_aus = summary_aus(target_summary);
        let target_domain = crate::allocation_layer::Likes_v::restrict_domain_au(
            pre.i().betree.linked.buffer_dv.entries,
            target_summary_aus,
        );
        let target_buffer = BufferDisk {
            entries: pre.i().betree.linked.buffer_dv.entries.restrict(
                target_domain,
            ),
        };
        assert(target_new_compactors == new_compactors);
        assert(target_released == released);
        assert(target_branch_deallocs == branch_deallocs);
        assert(target_summary == new_summary);
        assert(target_summary_aus == post_summary_aus);
        assert(target_domain == kept_domain);
        assert(target_buffer == expected_buffer);
        assert(0 <= input_idx < pre.i().compactors.len());
        assert(post.i().betree_aus == pre.i().betree_aus);
        assert(post.i().branch_aus == pre.i().branch_aus);
        pre.wip_alloc_aus_agree();
        assert(summary_aus(pre.i().branch_summary)
            .disjoint(pre.i().branch_allocator_aus()));
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i(),
            idx => {
                assert(post.betree.wip_branches[idx]
                    == pre.betree.wip_branches[idx]);
                let cached = pre.betree.wip_branches[idx];
                let allocated = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                AllocationBulkBranch::alloc_aus_ensures(
                    pre.i().wip_branches,
                    idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= pre.i().branch_allocator_aus());
                assert(deallocs.disjoint(cached.mini_allocator.all_aus()));
                assert(forgotten_aus.disjoint(
                    cached.mini_allocator.all_aus(),
                ));
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    forgotten_aus,
                    cached.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk,
                    new_disk,
                    forgotten_aus,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        );
        assert(post.i().wip_branches == pre.i().wip_branches);
        assert(crate::allocation_layer::Likes_v::restrict_domain_au(
            pre.i().betree.linked.buffer_dv.entries,
            summary_aus(post.i().branch_summary),
        ) == kept_domain);
        assert(AllocationBranchBetree::State::internal_compact_abort(
            pre.i(),
            post.i(),
            lbl.i(pre),
            input_idx,
            post.i().betree,
        ));
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            == pre.i().branch_allocator_aus());
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(forgotten_aus)) by {
            assert(summary_aus(pre.i().branch_summary)
                .disjoint(pre.i().branch_allocator_aus()));
            assert(deallocs <= summary_aus(pre.i().branch_summary));
        }
        assert(branch_deallocs.disjoint(read_ref_aus(
            post.betree.compactors,
        )));
        CompactorInput::input_roots_remove_subset(
            pre.betree.compactors,
            input_idx,
        );
        crate::disk::GenericDisk_v::to_aus_preserves_lte(
            CompactorInput::input_roots(post.betree.compactors),
            CompactorInput::input_roots(pre.betree.compactors),
        );
        assert(read_ref_aus(post.betree.compactors)
            <= read_ref_aus(pre.betree.compactors));
        pre.i().inv_branch_summary_ensures();
        assert(post.betree.branch_summary
            == pre.betree.branch_summary.remove_keys(branch_deallocs));
        assert forall |au: AU|
            #[trigger] read_ref_aus(post.betree.compactors).contains(au)
            implies
                post.betree.branch_summary.contains_key(au)
                && pre.betree.branch_summary.contains_key(au)
                && post.betree.branch_summary[au]
                    == pre.betree.branch_summary[au]
        by {
            assert(pre.betree.branch_summary.contains_key(au));
            assert(!branch_deallocs.contains(au));
        }
        Self::removed_compactor_receipt_preserves_inv(
            pre,
            post,
            input_idx,
        );
        Self::unchanged_wips_preserve_staged_nodes_after_forget(
            pre,
            post,
            forgotten_aus,
        );
    }

    #[verifier::spinoff_prover]
    #[verifier::rlimit(100)]
    proof fn compact_complete_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        input_idx: int,
        branch_idx: int,
        loaded_path: LoadedBetreePath,
        start: nat,
        end: nat,
        new_node_addr: Address,
        path_addrs: PathAddrs,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::compact_complete(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                input_idx,
                branch_idx,
                loaded_path,
                start,
                end,
                new_node_addr,
                path_addrs,
                access.loaded_betree_reads(),
                access.loaded_betree_writes(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            access.writes().dom() <= addresses_in_aus(lbl.allocs()),
            AllocationBranchBetree::State::internal_compact_complete(
                pre.i(),
                post.i(),
                lbl.i(pre),
                post.i().betree,
                Path {
                    linked: pre.linked_i(),
                    key: loaded_path.key,
                    depth: loaded_path.depth(),
                },
                start,
                end,
                input_idx,
                branch_idx,
                new_node_addr,
                path_addrs,
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        access.cached_only_betree_is_only_betree();

        pre.linked_i_is_tight_candidate();
        pre.linked_i_tight_tree_facts();
        assert(post.disk == new_disk);
        assert(post.betree == new_betree);

        let cached_branch = pre.betree.wip_branches[branch_idx];
        let allocation_branch = pre.wip_branch_i(branch_idx);
        let new_branch = allocation_branch.sealed_branch();
        let branch_root = new_branch.root;
        let new_addrs = TwoAddrs {
            addr1: new_node_addr,
            addr2: branch_root,
        };
        let linked_path = Path {
            linked: pre.linked_i(),
            key: loaded_path.key,
            depth: loaded_path.depth(),
        };
        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let input_roots = pre.betree.compactors[input_idx]
            .input_buffers.addrs.to_set();
        let input_branch_reads = pre.betree.compactor_receipts[input_idx];
        let output_branch_reads = new_branch.disk_view.entries;
        let source_tree_deallocs = pre.betree.betree_aus.dom()
            - post.betree.betree_aus.dom();
        let source_branch_deallocs = pre.betree.branch_summary.dom()
            - post.betree.branch_aus.dom()
            - read_ref_aus(post.betree.compactors);
        let source_dropped_summary = pre.betree.branch_summary.restrict(
            source_branch_deallocs,
        );

        assert(0 <= input_idx < pre.i().compactors.len());
        assert(0 <= branch_idx < pre.i().wip_branches.len());
        assert(allocation_branch == pre.i().wip_branches[branch_idx]);
        assert(allocation_branch.is_sealed());
        assert(cached_branch.sealed_root() == branch_root);
        pre.wip_alloc_aus_agree();
        AllocationBulkBranch::alloc_aus_ensures(
            pre.i().wip_branches,
            branch_idx,
        );
        assert(cached_branch.mini_allocator.all_aus()
            <= pre.i().branch_allocator_aus());
        assert(deallocs == source_tree_deallocs
            + summary_aus(source_dropped_summary));
        assert(summary_aus(source_dropped_summary)
            <= summary_aus(pre.betree.branch_summary)) by {
            pre.i().inv_branch_summary_ensures();
            let (_, pre_branch_likes) = pre.linked_i().transitive_likes();
            let pre_roots = pre_branch_likes.dom()
                + CompactorInput::input_roots(pre.i().compactors);
            pre.semantic_sealed_branch_disk()
                .build_branch_summary_finite(pre_roots);
            lemma_values_finite(pre.betree.branch_summary);
            crate::betree::Utils_v::lemma_subset_finite(
                pre.betree.branch_summary.dom(),
                source_dropped_summary.dom(),
            );
            lemma_values_finite(source_dropped_summary);
            assert forall |au: AU|
                #[trigger] summary_aus(source_dropped_summary).contains(au)
                implies summary_aus(pre.betree.branch_summary).contains(au)
            by {
                let summary = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
                    source_dropped_summary.values(),
                    au,
                );
                assert(pre.betree.branch_summary.values().contains(summary));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    summary,
                );
            };
        };
        assert(deallocs <= pre.i().betree_aus.dom()
            + summary_aus(pre.i().branch_summary));
        assert(cached_branch.mini_allocator.all_aus().disjoint(allocs)) by {
            assert(pre.i().is_fresh(allocs));
        };
        assert(cached_branch.mini_allocator.all_aus().disjoint(deallocs)) by {
            assert(pre.i().betree_aus.dom().disjoint(
                pre.i().branch_allocator_aus(),
            ));
            assert(summary_aus(pre.i().branch_summary).disjoint(
                pre.i().branch_allocator_aus(),
            ));
        };
        assert(summary_aus(pre.betree.branch_summary).disjoint(allocs)) by {
            assert(pre.i().is_fresh(allocs));
        };
        let reads = access.reads();
        let writes = access.writes();
        let betree_reads = access.loaded_betree_reads();
        let betree_writes = access.loaded_betree_writes();
        let pre_tree = pre.tight_betree_i();
        let pre_linked = pre.linked_i();
        let witness = disk_access_for_alloc_witness(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
        );
        assert(allocation_branch.sealed_branch() == new_branch);
        assert(cached_branch.summary() == new_branch.get_summary());
        assert(access.branch_writes.is_empty());
        assert(writes == access.betree_writes);
        assert(pre_linked.dv.entries
            <= to_betree_nodes(pre.disk.visible())) by {
            assert(pre_tree.dv.entries <= pre.visible_betree_entries());
            assert(pre_linked.dv == pre_tree.dv);
            assert forall |addr: Address|
                #[trigger] pre_linked.dv.entries.contains_key(addr)
                implies to_betree_nodes(pre.disk.visible()).contains_key(addr)
                    && pre_linked.dv.entries[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]
            by {
                assert(pre.visible_betree_entries().contains_key(addr));
            };
        };

        let path_reads = access.betree_reads.restrict(
            loaded_path.needed_addrs(),
        );
        assert(loaded_path.valid_for(
            pre.betree.root,
            to_betree_nodes(path_reads),
        )) by {
            assert_maps_equal!(
                to_betree_nodes(path_reads),
                betree_reads.restrict(loaded_path.needed_addrs()),
                addr => {}
            );
        };
        assert(access.betree_reads <= reads) by {
            assert forall |addr: Address|
                #[trigger] access.betree_reads.contains_key(addr)
                implies reads.contains_key(addr)
                    && reads[addr] == access.betree_reads[addr]
            by {
                assert(!access.branch_reads.contains_key(addr)) by {
                    if access.branch_reads.contains_key(addr) {
                        assert(access.betree_reads.dom().disjoint(
                            access.branch_reads.dom(),
                        ));
                    }
                };
            };
        };
        assert(path_reads <= access.betree_reads);
        assert(path_reads <= reads);
        assert(reads <= witness.expanded.cache);
        assert(path_reads <= witness.expanded.cache) by {
            assert forall |addr: Address|
                #[trigger] path_reads.contains_key(addr)
                implies witness.expanded.cache.contains_key(addr)
                    && path_reads[addr] == witness.expanded.cache[addr]
            by {
                assert(access.betree_reads.contains_pair(
                    addr,
                    path_reads[addr],
                ));
                assert(reads.contains_pair(addr, path_reads[addr]));
                assert(witness.expanded.cache.contains_pair(
                    addr,
                    path_reads[addr],
                ));
            };
        };
        loaded_path_reads_come_from_pre_cache(
            pre.disk,
            witness.expanded,
            allocs,
            pre.betree.betree_aus.dom(),
            pre_linked,
            path_reads,
            loaded_path,
        );
        assert(path_reads.restrict(loaded_path.needed_addrs()) == path_reads);
        assert(path_reads <= pre.disk.cache);
        loaded_betree_path_matches_linked(
            pre.disk,
            pre_linked,
            path_reads,
            loaded_path,
            loaded_path.depth(),
        );
        assert(linked_path.valid());
        assert(linked_path.target().root() == loaded_path.target().node);

        let replacement = linked_path.target().compact(
            start,
            end,
            new_branch.root(),
            new_addrs,
        );
        let replacement_writes =
            crate::implementation::CachedBranchBetree_v::compact_replacement(
                loaded_path,
                start,
                end,
                branch_root,
                new_addrs,
            );
        assert(replacement.root == Some(new_node_addr));
        assert(replacement.dv.entries
            == pre_linked.dv.entries.union_prefer_right(
                replacement_writes,
            )) by {
            assert_maps_equal!(
                replacement.dv.entries,
                pre_linked.dv.entries.union_prefer_right(replacement_writes),
                addr => {}
            );
        };
        assert(replacement.buffer_dv
            == pre_linked.buffer_dv.modify_disk(
                branch_root,
                new_branch.root(),
            ));

        assert(path_addrs.no_duplicates()) by {
            assert forall |i: int, j: int|
                0 <= i < path_addrs.len()
                    && 0 <= j < path_addrs.len()
                    && i != j
                implies path_addrs[i] != path_addrs[j]
            by {
                assert(path_addrs[i].au != path_addrs[j].au);
            };
        };
        assert(path_addrs.to_set().disjoint(pre_linked.dv.entries.dom())) by {
            assert(seq_addrs_to_aus(path_addrs) <= allocs);
            crate::disk::GenericDisk_v::to_aus_domain(path_addrs.to_set());
        };
        assert(path_addrs.to_set().disjoint(replacement_writes.dom())) by {
            assert(replacement_writes.dom() == set![new_node_addr]);
            assert(!seq_addrs_to_aus(path_addrs).contains(new_node_addr.au));
            crate::disk::GenericDisk_v::to_aus_domain(path_addrs.to_set());
        };
        loaded_substitute_writes_match(
            pre.disk,
            path_reads,
            loaded_path,
            linked_path,
            new_node_addr,
            replacement,
            replacement_writes,
            path_addrs,
        );

        let compacted = LinkedBetreeVars::State::post_compact(
            linked_path,
            start,
            end,
            new_branch.root(),
            new_addrs,
            path_addrs,
        );
        assert(betree_writes
            == crate::implementation::CachedBranchBetree_v::substitute_writes(
                loaded_path,
                new_node_addr,
                replacement_writes,
                path_addrs,
            ));
        assert(to_betree_nodes(writes).dom() == writes.dom());
        assert(betree_writes.dom() == writes.dom());
        assert(compacted.dv.entries
            == pre_linked.dv.entries.union_prefer_right(betree_writes));
        assert(allocs == to_aus(path_addrs.to_set())
            .insert(new_node_addr.au));
        crate::disk::GenericDisk_v::to_aus_singleton(new_node_addr);
        crate::disk::GenericDisk_v::to_aus_additive(
            path_addrs.to_set(),
            set![new_node_addr],
        );
        assert(seq_addrs_to_aus(path_addrs)
            == to_aus(path_addrs.to_set()));
        assert(set![new_node_addr] + path_addrs.to_set()
            == path_addrs.to_set() + set![new_node_addr]);
        assert(to_aus(set![new_node_addr] + path_addrs.to_set()) == allocs);
        assert(writes.dom() <= addresses_in_aus(allocs)) by {
            assert(betree_writes.dom()
                <= set![new_node_addr] + path_addrs.to_set());
            crate::disk::GenericDisk_v::to_aus_domain(
                set![new_node_addr] + path_addrs.to_set(),
            );
        };
        assert(compacted.root == post.betree.root);

        assert(new_addrs.no_duplicates()) by {
            assert(cached_branch.mini_allocator.all_aus()
                .contains(branch_root.au)) by {
                assert(new_branch.get_summary().contains(branch_root.au));
                assert(new_branch.get_summary()
                    == cached_branch.mini_allocator.all_aus());
            };
            assert(allocs.contains(new_node_addr.au));
        };
        assert(pre_linked.is_fresh(new_addrs.repr())) by {
            assert forall |addr: Address|
                #[trigger] new_addrs.repr().contains(addr)
                implies !pre_linked.dv.entries.contains_key(addr)
                    && !pre_linked.buffer_dv.entries.contains_key(addr)
            by {
                if addr == new_node_addr {
                    assert(allocs.contains(addr.au));
                    assert(pre.i().is_fresh(allocs));
                } else {
                    assert(addr == branch_root);
                    assert(pre.i().branch_allocator_aus().contains(addr.au));
                    assert(pre.i().betree_aus.dom().disjoint(
                        pre.i().branch_allocator_aus(),
                    ));
                    assert(summary_aus(pre.i().branch_summary).disjoint(
                        pre.i().branch_allocator_aus(),
                    ));
                }
            };
        };
        assert(pre_linked.is_fresh(path_addrs.to_set())) by {
            assert(seq_addrs_to_aus(path_addrs) <= allocs);
            crate::disk::GenericDisk_v::to_aus_domain(path_addrs.to_set());
            assert forall |addr: Address|
                #[trigger] path_addrs.to_set().contains(addr)
                implies !pre_linked.dv.entries.contains_key(addr)
                    && !pre_linked.buffer_dv.entries.contains_key(addr)
            by {
                assert(allocs.contains(addr.au));
                assert(pre.i().is_fresh(allocs));
            };
        };
        assert(new_addrs.repr().disjoint(path_addrs.to_set())) by {
            assert forall |new_addr: Address|
                #[trigger] new_addrs.repr().contains(new_addr)
                implies !path_addrs.to_set().contains(new_addr)
            by {
                if new_addr == new_node_addr {
                    if path_addrs.to_set().contains(new_addr) {
                        crate::disk::GenericDisk_v::to_aus_domain(
                            path_addrs.to_set(),
                        );
                        assert(seq_addrs_to_aus(path_addrs)
                            .contains(new_node_addr.au));
                    }
                } else {
                    assert(new_addr == branch_root);
                    if path_addrs.to_set().contains(new_addr) {
                        crate::disk::GenericDisk_v::to_aus_domain(
                            path_addrs.to_set(),
                        );
                        assert(allocs.contains(branch_root.au));
                        assert(cached_branch.mini_allocator.all_aus()
                            .contains(branch_root.au));
                        assert(cached_branch.mini_allocator.all_aus()
                            .disjoint(allocs));
                    }
                }
            };
        };
        assert(pre_linked.valid_path_replacement(
            linked_path,
            new_addrs,
            path_addrs,
        ));
        pre.i().betree.post_compact_ensures(
            linked_path,
            start,
            end,
            new_branch.root(),
            new_addrs,
            path_addrs,
        );
        assert(compacted.acyclic());
        let post_tree = reachable_tight_betree(compacted);
        reachable_tight_betree_facts(compacted);

        let full_buffer = BufferDisk {
            entries: pre_linked.buffer_dv.entries.union_prefer_right(
                new_branch.disk_view.entries,
            ),
        };
        let model_post_linked = LinkedBetree {
            root: compacted.root,
            dv: compacted.dv,
            buffer_dv: full_buffer,
        };
        let model_post_vars = LinkedBetreeVars::State {
            memtable: pre.i().betree.memtable,
            linked: model_post_linked,
        };
        assert(compacted.valid_view(model_post_linked)) by {
            assert(model_post_linked.wf());
            assert(model_post_linked.dv.is_sub_disk(compacted.dv));
            assert(model_post_linked.buffer_dv.agrees_with(
                compacted.buffer_dv,
            )) by {
                assert forall |addr: Address|
                    #[trigger] model_post_linked.buffer_dv.entries
                        .contains_key(addr)
                        && compacted.buffer_dv.entries.contains_key(addr)
                    implies model_post_linked.buffer_dv.entries[addr]
                        == compacted.buffer_dv.entries[addr]
                by {
                    if addr == branch_root {
                        assert(new_branch.disk_view.entries
                            .contains_key(addr));
                        assert(new_branch.disk_view.entries[addr]
                            == new_branch.root());
                    } else {
                        assert(pre_linked.buffer_dv.entries
                            .contains_key(addr));
                    }
                };
            };
        };

        compactor_receipt_matches_semantic(pre, input_idx);
        compact_reads_establish_can_compact(
            pre,
            input_idx,
            linked_path,
            start,
            end,
            new_addrs,
            input_branch_reads,
            output_branch_reads,
            new_branch,
        );
        assert(LinkedBetreeVars::State::internal_compact(
            pre.i().betree,
            model_post_vars,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            model_post_linked,
            linked_path,
            start,
            end,
            new_branch.root(),
            new_addrs,
            path_addrs,
        ));
        pre.i().betree.internal_compact_complete_aus_ensures(
            model_post_vars,
            linked_path,
            start,
            end,
            new_branch.root(),
            new_addrs,
            path_addrs,
        );
        let (compacted_tree_likes, compacted_branch_likes) =
            compacted.transitive_likes();
        let (expected_betree_aus, expected_branch_aus) =
            crate::allocation_layer::AllocationBetree_v::AllocationBetree::State::internal_compact_complete_au_likes(
                linked_path,
                start,
                end,
                new_addrs,
                path_addrs,
                pre.i().betree_aus,
                pre.i().branch_aus,
            );
        assert(expected_betree_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                compacted_tree_likes,
            ));
        assert(expected_branch_aus
            == crate::allocation_layer::Likes_v::to_au_likes(
                compacted_branch_likes,
            ));
        loaded_path_addrs_match_linked(
            pre.disk,
            pre_linked,
            path_reads,
            loaded_path,
        );
        loaded_path.path_addrs().to_multiset_ensures();
        linked_path.addrs_on_path().to_multiset_ensures();
        assert(loaded_path.path_addrs().to_multiset()
            == linked_path.addrs_on_path().to_multiset().add(
                linked_path.target().root_likes(),
            ));
        assert(crate::implementation::CachedBranchBetree_v::path_discard_likes(
            loaded_path,
        ) == crate::allocation_layer::LikesBetree_v::compact_discard_betree(
            linked_path,
        ));
        assert(post.betree.betree_aus == expected_betree_aus);
        assert(loaded_path.target().node.buffers.slice(
            start as int,
            end as int,
        ) == linked_path.target().root().buffers.slice(
            start as int,
            end as int,
        ));
        crate::allocation_layer::Likes_v::to_au_likes_singleton(branch_root);
        assert(post.betree.branch_aus == expected_branch_aus);

        let stable_tree_aus = pre.betree.betree_aus.dom() - deallocs;
        let stable_tree_addrs = addresses_in_aus(stable_tree_aus);
        assert(stable_tree_aus.disjoint(allocs));
        assert(stable_tree_aus.disjoint(deallocs));
        addresses_in_aus_preserves_disjointness(stable_tree_aus, allocs);
        addresses_in_aus_preserves_disjointness(stable_tree_aus, deallocs);
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            stable_tree_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            stable_tree_addrs,
        );
        CachingDisk::State::access_visible_effect(
            witness.expanded,
            witness.accessed,
            reads,
            writes,
        );
        CachingDisk::State::forget_effect(
            witness.accessed,
            new_disk,
            deallocs - guard_aus,
        );
        compacted.tree_likes_domain(compacted.the_ranking());
        crate::allocation_layer::Likes_v::to_au_likes_domain(
            compacted_tree_likes,
        );
        assert(post_tree.dv.entries <= post.visible_betree_entries()) by {
            assert forall |addr: Address|
                #[trigger] post_tree.dv.entries.contains_key(addr)
                implies post.visible_betree_entries().contains_key(addr)
                    && post_tree.dv.entries[addr]
                        == post.visible_betree_entries()[addr]
            by {
                assert(compacted.dv.entries.contains_key(addr));
                assert(compacted.reachable_betree_addrs().contains(addr));
                assert(compacted_tree_likes.contains(addr));
                assert(post.betree.betree_aus.dom().contains(addr.au));
                if writes.contains_key(addr) {
                    assert(allocs.contains(addr.au));
                    assert(!deallocs.contains(addr.au));
                    assert(witness.accessed.visible()[addr] == writes[addr]);
                    assert(new_disk.visible()[addr] == writes[addr]);
                    assert(to_betree_nodes(new_disk.visible())
                        .contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible())[addr]
                        == betree_writes[addr]);
                    assert(compacted.dv.entries[addr]
                        == betree_writes[addr]);
                } else {
                    assert(pre_tree.dv.entries.contains_key(addr));
                    assert(pre.betree.betree_aus.dom().contains(addr.au));
                    assert(!source_tree_deallocs.contains(addr.au));
                    assert(!deallocs.contains(addr.au));
                    assert(stable_tree_addrs.contains(addr));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_tree_addrs,
                    ).contains_key(addr));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_tree_addrs,
                    ) == to_betree_nodes(
                        pre.disk.visible(),
                    ).restrict(stable_tree_addrs));
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_tree_addrs,
                    )[addr] == to_betree_nodes(
                        pre.disk.visible(),
                    ).restrict(stable_tree_addrs)[addr]);
                    assert(to_betree_nodes(new_disk.visible()).restrict(
                        stable_tree_addrs,
                    )[addr] == to_betree_nodes(
                        new_disk.visible(),
                    )[addr]);
                    assert(to_betree_nodes(
                        pre.disk.visible(),
                    ).restrict(stable_tree_addrs)[addr]
                        == to_betree_nodes(
                            pre.disk.visible(),
                        )[addr]);
                    assert(compacted.dv.entries[addr]
                        == pre_linked.dv.entries[addr]);
                    assert(pre_linked.dv.entries[addr]
                        == pre_tree.dv.entries[addr]);
                    assert(to_betree_nodes(new_disk.visible())[addr]
                        == to_betree_nodes(pre.disk.visible())[addr]);
                }
                assert(post_tree.dv.entries[addr]
                    == compacted.dv.entries[addr]);
            };
        };
        reachable_tight_betree_is_candidate(
            compacted,
            post.betree.root,
            post.visible_betree_entries(),
        );
        tight_betree_of_equals_candidate(
            post.betree.root,
            post.visible_betree_entries(),
            post_tree,
        );
        assert(post.tight_betree_i() == post_tree);

        let pre_roots = pre.semantic_branch_roots();
        let full_roots = pre_roots.insert(branch_root);
        let post_roots = post.semantic_branch_roots();
        let new_compactors = pre.betree.compactors.remove(input_idx);
        let full_summary = pre.betree.branch_summary.insert(
            branch_root.au,
            new_branch.get_summary(),
        );
        let full_loose = visible_branch_disk(pre.disk, full_summary);
        let post_loose = post.visible_sealed_branch_disk();
        let (_, pre_branch_likes) = pre_linked.transitive_likes();

        pre_linked.tree_likes_domain(pre_linked.the_ranking());
        pre_linked.buffer_likes_domain(
            pre_linked.tree_likes(pre_linked.the_ranking()),
        );
        compacted.buffer_likes_domain(compacted_tree_likes);
        assert(pre_roots == pre_branch_likes.dom()
            + CompactorInput::input_roots(pre.i().compactors)) by {
            assert(pre_linked.reachable_buffer_addrs()
                == pre_tree.reachable_buffer_addrs()) by {
                assert(pre_linked.dv == pre_tree.dv);
                assert(pre_linked.reachable_betree_addrs()
                    == pre_tree.reachable_betree_addrs());
                pre_linked.same_reachable_betree_addrs_implies_same_buffer_addrs(
                    pre_tree,
                );
            };
        };
        assert(post_tree.reachable_buffer_addrs()
            == compacted.reachable_buffer_addrs()) by {
            compacted.same_reachable_betree_addrs_implies_same_buffer_addrs(
                post_tree,
            );
        };
        assert(post.betree.compactors == new_compactors);
        assert(post_roots == compacted_branch_likes.dom()
            + CompactorInput::input_roots(new_compactors));

        crate::allocation_layer::LikesBetree_v::LikesBetree::State::post_compact_likes_ensures(
            pre.i().betree,
            model_post_vars,
            linked_path,
            start,
            end,
            new_branch.root(),
            new_addrs,
            path_addrs,
        );
        CompactorInput::input_roots_remove_subset(
            pre.i().compactors,
            input_idx,
        );
        CompactorInput::input_roots_finite(pre.i().compactors);
        assert(pre_branch_likes.dom().finite());
        assert(pre_roots.finite());
        pre_linked.buffer_dv.build_branch_summary_finite(pre_roots);
        lemma_values_finite(pre.betree.branch_summary);
        assert(set_addrs_disjoint_aus(pre_roots));
        assert(set_addrs_disjoint_aus(full_roots)) by {
            assert forall |root: Address|
                #[trigger] pre_roots.contains(root)
                implies root.au != branch_root.au
            by {
                pre_linked.buffer_dv.build_branch_summary_contains(
                    pre_roots,
                    root,
                );
                assert(pre.betree.branch_summary.contains_key(root.au));
                assert(pre.betree.branch_summary.values().contains(
                    pre.betree.branch_summary[root.au],
                ));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    pre.betree.branch_summary[root.au],
                );
                assert(summary_aus(pre.betree.branch_summary)
                    .contains(root.au));
                assert(new_branch.get_summary().contains(branch_root.au));
            };
        };
        assert(post_roots <= full_roots);
        assert(to_aus(full_roots - post_roots)
            == source_branch_deallocs) by {
            let pre_compactor_roots = CompactorInput::input_roots(
                pre.i().compactors,
            );
            let post_compactor_roots = CompactorInput::input_roots(
                new_compactors,
            );
            assert(full_roots - post_roots
                == (pre_branch_likes.dom() + pre_compactor_roots)
                    - (compacted_branch_likes.dom()
                        + post_compactor_roots));
            crate::disk::GenericDisk_v::to_aus_subtract(
                pre_branch_likes.dom() + pre_compactor_roots,
                compacted_branch_likes.dom() + post_compactor_roots,
            );
            assert(to_aus(pre_branch_likes.dom() + pre_compactor_roots)
                == pre.betree.branch_summary.dom());
            crate::disk::GenericDisk_v::to_aus_additive(
                compacted_branch_likes.dom(),
                post_compactor_roots,
            );
            crate::allocation_layer::Likes_v::to_au_likes_domain(
                compacted_branch_likes,
            );
            assert(post.betree.branch_aus.dom()
                == to_aus(compacted_branch_likes.dom()));
        };
        assert(!source_branch_deallocs.contains(branch_root.au)) by {
            assert(post.betree.branch_aus.dom().contains(branch_root.au));
        };
        assert(post.betree.branch_summary
            == full_summary.remove_keys(source_branch_deallocs));
        assert(full_summary.restrict(source_branch_deallocs)
            == source_dropped_summary) by {
            assert_maps_equal!(
                full_summary.restrict(source_branch_deallocs),
                source_dropped_summary,
                au => {}
            );
        };

        pre.i().inv_branch_summary_ensures();
        assert(pre_linked.buffer_dv.sealed_branch_roots(pre_roots));
        assert(pre.betree.branch_summary
            == pre_linked.buffer_dv.build_branch_summary(pre_roots));
        assert(!pre.betree.branch_summary.contains_key(branch_root.au)) by {
            if pre.betree.branch_summary.contains_key(branch_root.au) {
                assert(pre.betree.branch_summary.values().contains(
                    pre.betree.branch_summary[branch_root.au],
                ));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    pre.betree.branch_summary[branch_root.au],
                );
                assert(summary_aus(pre.betree.branch_summary)
                    .contains(branch_root.au));
                assert(new_branch.get_summary().contains(branch_root.au));
            }
        };
        crate::allocation_layer::AllocationBranchBetree_v::branch_summary_insert_ensures(
            pre.betree.branch_summary,
            new_branch,
        );
        lemma_values_finite(full_summary);
        assert(full_summary.contains_key(branch_root.au));
        assert(full_summary[branch_root.au] == new_branch.get_summary());
        assert(full_summary.values().contains(new_branch.get_summary()));

        let new_branch_loose = loose_disk_for_summary(
            full_loose,
            new_branch.get_summary(),
        );
        assert(tight_branch_in_loose_disk(
            new_branch_loose,
            branch_root,
            new_branch.get_summary(),
            new_branch,
        )) by {
            assert(new_branch.disk_view.entries
                <= new_branch_loose.entries) by {
                assert forall |addr: Address|
                    #[trigger] new_branch.disk_view.entries.contains_key(addr)
                    implies new_branch_loose.entries.contains_key(addr)
                        && new_branch_loose.entries[addr]
                            == new_branch.disk_view.entries[addr]
                by {
                    assert(new_branch.disk_view.entries
                        == to_branch_nodes(pre.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                cached_branch.mini_allocator,
                            ),
                        ));
                    assert(new_branch.full_repr().contains(addr));
                    assert(new_branch.get_summary().contains(addr.au));
                    assert(full_summary.values().contains(
                        new_branch.get_summary(),
                    ));
                    crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                        full_summary.values(),
                        new_branch.get_summary(),
                    );
                };
            };
        };
        assert forall |root: Address|
            #[trigger] pre_roots.contains(root)
            implies {
                &&& pre.betree.branch_summary.contains_key(root.au)
                &&& tight_branch_exists(
                    loose_disk_for_summary(
                        pre.visible_sealed_branch_disk(),
                        pre.betree.branch_summary[root.au],
                    ),
                    root,
                    pre.betree.branch_summary[root.au],
                )
                &&& loose_disk_for_summary(
                    full_loose,
                    full_summary[root.au],
                ) == loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    pre.betree.branch_summary[root.au],
                )
            }
        by {
            assert(pre.tight_branches_exist());
            assert(root.au != branch_root.au);
            assert(full_summary[root.au]
                == pre.betree.branch_summary[root.au]);
            let root_summary = pre.betree.branch_summary[root.au];
            assert(root_summary <= summary_aus(pre.betree.branch_summary)) by {
                assert(pre.betree.branch_summary.values().contains(
                    root_summary,
                ));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    pre.betree.branch_summary.values(),
                    root_summary,
                );
            };
            assert_maps_equal!(
                loose_disk_for_summary(
                    full_loose,
                    root_summary,
                ).entries,
                loose_disk_for_summary(
                    pre.visible_sealed_branch_disk(),
                    root_summary,
                ).entries,
                addr => {}
            );
        };
        tight_sealed_branch_disk_insert(
            pre.visible_sealed_branch_disk(),
            full_loose,
            pre_roots,
            branch_root,
            pre.betree.branch_summary,
            full_summary,
            new_branch,
        );
        let full_semantic_buffer = tight_sealed_branch_disk(
            full_loose,
            full_roots,
            full_summary,
        );
        assert(full_semantic_buffer.entries == full_buffer.entries);
        assert(full_semantic_buffer == full_buffer);
        pre.i().inv_implies_wf_branch_dv();
        assert(pre_linked.buffer_dv.to_branch_disk().wf());
        assert(pre_linked.buffer_dv.entries.dom().disjoint(
            new_branch.disk_view.entries.dom(),
        )) by {
            assert forall |addr: Address|
                #[trigger] pre_linked.buffer_dv.entries.contains_key(addr)
                implies !new_branch.disk_view.entries.contains_key(addr)
            by {
                assert(summary_aus(pre.betree.branch_summary)
                    .contains(addr.au));
                if new_branch.disk_view.entries.contains_key(addr) {
                    assert(new_branch.get_summary().contains(addr.au));
                }
            };
        };
        pre_linked.buffer_dv.to_branch_disk()
            .merge_disjoint_disk_preserves_wf(new_branch.disk_view);
        assert(full_semantic_buffer.to_branch_disk().wf());
        assert(full_roots == pre_roots + set![branch_root]);
        pre_linked.buffer_dv.build_branch_summary_insert(
            full_semantic_buffer,
            pre_roots,
            new_branch,
        );
        assert(full_semantic_buffer.sealed_branch_roots(full_roots));
        assert(full_summary
            == full_semantic_buffer.build_branch_summary(full_roots));
        assert(crate::allocation_layer::AllocationBranchBetree_v::map_with_disjoint_values(
            full_summary,
        ));
        assert(crate::disk::GenericDisk_v::addrs_closed(
            full_semantic_buffer.entries.dom(),
            summary_aus(full_summary),
        ));

        assert forall |root: Address|
            #[trigger] full_roots.contains(root)
            implies {
                &&& full_summary.contains_key(root.au)
                &&& tight_branch_exists(
                    loose_disk_for_summary(
                        full_loose,
                        full_summary[root.au],
                    ),
                    root,
                    full_summary[root.au],
                )
            }
        by {
            if root == branch_root {
                assert(tight_branch_in_loose_disk(
                    new_branch_loose,
                    branch_root,
                    new_branch.get_summary(),
                    new_branch,
                ));
            } else {
                assert(pre_roots.contains(root));
            }
        };

        let post_summary_aus = summary_aus(post.betree.branch_summary);
        let summary_deallocs = summary_aus(
            full_summary.restrict(source_branch_deallocs),
        );
        map_remove_keys_preserves_point(
            full_summary,
            source_branch_deallocs,
            branch_root.au,
        );
        assert(post.betree.branch_summary <= full_summary);
        crate::betree::Utils_v::lemma_subset_finite(
            full_summary.dom(),
            post.betree.branch_summary.dom(),
        );
        lemma_values_finite(post.betree.branch_summary);
        assert(post_summary_aus <= summary_aus(full_summary)) by {
            assert forall |au: AU| #[trigger] post_summary_aus.contains(au)
                implies summary_aus(full_summary).contains(au)
            by {
                let summary = crate::betree::Utils_v::lemma_union_set_of_sets_contains(
                    post.betree.branch_summary.values(),
                    au,
                );
                assert(full_summary.values().contains(summary));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    full_summary.values(),
                    summary,
                );
            };
        };
        assert(summary_deallocs
            == summary_aus(source_dropped_summary));
        assert(post_summary_aus.disjoint(summary_deallocs)) by {
            summary_partition_disjoint(
                full_summary,
                source_branch_deallocs,
            );
        };
        assert(post_summary_aus.disjoint(allocs)) by {
            assert(summary_aus(full_summary)
                == summary_aus(pre.betree.branch_summary)
                    + new_branch.get_summary());
            assert(new_branch.get_summary()
                == cached_branch.mini_allocator.all_aus());
            assert(cached_branch.mini_allocator.all_aus().disjoint(allocs));
        };
        assert(post_summary_aus.disjoint(source_tree_deallocs)) by {
            assert(source_tree_deallocs <= pre.betree.betree_aus.dom());
            assert(pre.i().betree_aus.dom().disjoint(
                summary_aus(pre.i().branch_summary),
            ));
            assert(pre.i().betree_aus.dom().disjoint(
                pre.i().branch_allocator_aus(),
            ));
            assert(new_branch.get_summary()
                <= pre.i().branch_allocator_aus());
            assert(summary_aus(full_summary)
                == summary_aus(pre.betree.branch_summary)
                    + new_branch.get_summary());
        };
        assert(post_summary_aus.disjoint(deallocs)) by {
            assert(deallocs == source_tree_deallocs + summary_deallocs);
        };
        addresses_in_aus_preserves_disjointness(
            post_summary_aus,
            allocs,
        );
        addresses_in_aus_preserves_disjointness(
            post_summary_aus,
            deallocs,
        );
        disk_access_for_alloc_visible_outside_alloc_dealloc(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
            addresses_in_aus(post_summary_aus),
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            addresses_in_aus(post_summary_aus),
        );
        assert(post_loose.entries
            == to_branch_nodes(new_disk.visible()).restrict(
                addresses_in_aus(post_summary_aus),
            ));
        assert(full_loose.entries.restrict(
            addresses_in_aus(post_summary_aus),
        ) == to_branch_nodes(pre.disk.visible()).restrict(
            addresses_in_aus(post_summary_aus),
        )) by {
            assert_maps_equal!(
                full_loose.entries.restrict(
                    addresses_in_aus(post_summary_aus),
                ),
                to_branch_nodes(pre.disk.visible()).restrict(
                    addresses_in_aus(post_summary_aus),
                ),
                addr => {
                    if addresses_in_aus(post_summary_aus).contains(addr) {
                        assert(addresses_in_aus(summary_aus(full_summary))
                            .contains(addr));
                    }
                }
            );
        };
        assert(post_loose.entries == full_loose.entries.restrict(
            addresses_in_aus(post_summary_aus),
        )) by {
            assert_maps_equal!(
                post_loose.entries,
                full_loose.entries.restrict(
                    addresses_in_aus(post_summary_aus),
                ),
                addr => {}
            );
        };
        tight_sealed_branch_disk_prune(
            full_loose,
            post_loose,
            full_roots,
            post_roots,
            full_summary,
            post.betree.branch_summary,
            source_branch_deallocs,
            summary_deallocs,
        );
        let post_buffer_domain =
            crate::allocation_layer::Likes_v::restrict_domain_au(
                full_buffer.entries,
                post_summary_aus,
            );
        assert(post.tight_branches_exist());
        assert(post.semantic_sealed_branch_disk().entries
            == full_buffer.entries.restrict(post_buffer_domain));
        let expected_post_buffer = BufferDisk {
            entries: full_buffer.entries.restrict(post_buffer_domain),
        };
        assert(post.linked_i().buffer_dv == expected_post_buffer);
        full_semantic_buffer.build_branch_summary_remove(
            full_summary,
            full_roots,
            post_roots,
        );
        assert(post.linked_i().buffer_dv.to_branch_disk().wf());
        assert(post.linked_i().buffer_dv.sealed_branch_roots(post_roots));
        assert(compacted_branch_likes.contains(branch_root));
        assert(post_roots.contains(branch_root));
        assert(post.betree.branch_summary.contains_key(branch_root.au));
        assert(post.betree.branch_summary[branch_root.au]
            == new_branch.get_summary());

        let post_new_branch_loose = loose_disk_for_summary(
            post_loose,
            new_branch.get_summary(),
        );
        assert(post_new_branch_loose == new_branch_loose) by {
            assert(new_branch.get_summary() <= post_summary_aus) by {
                assert(post.betree.branch_summary.values().contains(
                    new_branch.get_summary(),
                ));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    post.betree.branch_summary.values(),
                    new_branch.get_summary(),
                );
            };
            assert_maps_equal!(
                post_new_branch_loose.entries,
                new_branch_loose.entries,
                addr => {
                    if addresses_in_aus(new_branch.get_summary())
                        .contains(addr)
                    {
                        assert(addresses_in_aus(post_summary_aus)
                            .contains(addr));
                    }
                }
            );
        };
        assert(tight_branch_in_loose_disk(
            post_new_branch_loose,
            branch_root,
            new_branch.get_summary(),
            new_branch,
        ));
        assert(new_branch.disk_view.entries
            <= post_new_branch_loose.entries);
        tight_branch_of_equals_candidate(
            post_new_branch_loose,
            branch_root,
            new_branch.get_summary(),
            new_branch,
        );
        let selected_post_branch = tight_branch_of(
            post_new_branch_loose,
            branch_root,
            new_branch.get_summary(),
        );
        assert(selected_post_branch == new_branch);

        let post_new_branch_entries = post.linked_i().buffer_dv.entries
            .restrict(addresses_in_aus(new_branch.get_summary()));
        assert(post_new_branch_entries == new_branch.disk_view.entries) by {
            assert_maps_equal!(
                post_new_branch_entries,
                new_branch.disk_view.entries,
                addr => {
                    if post_new_branch_entries.contains_key(addr) {
                        assert(post.semantic_sealed_branch_disk().entries
                            .contains_key(addr));
                        let root = choose |root: Address|
                            post_roots.contains(root)
                                && tight_branch_of(
                                    loose_disk_for_summary(
                                        post_loose,
                                        post.betree.branch_summary[root.au],
                                    ),
                                    root,
                                    post.betree.branch_summary[root.au],
                                ).disk_view.entries.contains_key(addr);
                        let root_summary = post.betree.branch_summary[root.au];
                        tight_branch_of_is_candidate(
                            loose_disk_for_summary(post_loose, root_summary),
                            root,
                            root_summary,
                        );
                        assert(root_summary.contains(addr.au));
                        if root.au != branch_root.au {
                            assert(post.betree.branch_summary[root.au]
                                .disjoint(post.betree.branch_summary[
                                    branch_root.au
                                ]));
                            assert(false);
                        }
                        assert(root == branch_root) by {
                            if root != branch_root {
                                assert(addrs_with_different_au(
                                    root,
                                    branch_root,
                                ));
                            }
                        };
                        assert(tight_branch_of(
                            post_new_branch_loose,
                            branch_root,
                            new_branch.get_summary(),
                        ) == new_branch);
                    }
                    if new_branch.disk_view.entries.contains_key(addr) {
                        assert(post_new_branch_loose.entries
                            .contains_key(addr));
                        assert(post_loose.entries.contains_key(addr));
                        assert(tight_branch_addrs(
                            post_loose,
                            post_roots,
                            post.betree.branch_summary,
                        ).contains(addr)) by {
                            assert(exists |root: Address|
                                post_roots.contains(root)
                                    && tight_branch_of(
                                        loose_disk_for_summary(
                                            post_loose,
                                            post.betree.branch_summary[root.au],
                                        ),
                                        root,
                                        post.betree.branch_summary[root.au],
                                    ).disk_view.entries.contains_key(addr)) by {
                                assert(post_roots.contains(branch_root));
                            };
                        };
                    }
                }
            );
        };
        let post_output_branch = post.linked_i().buffer_dv.get_branch(
            branch_root,
        );
        assert(new_branch.disk_view.is_sub_disk(
            post_output_branch.disk_view,
        ));
        assert forall |addr: Address|
            #[trigger] (post_output_branch.disk_view.representation()
                - new_branch.disk_view.representation()).contains(addr)
            implies !new_branch.get_summary().contains(addr.au)
        by {
            if new_branch.get_summary().contains(addr.au) {
                assert(post_new_branch_entries.contains_key(addr));
                assert(new_branch.disk_view.entries.contains_key(addr));
            }
        };
        new_branch.valid_subdisk_preserves_valid_sealed_branch(
            post_output_branch,
            new_branch.get_summary(),
        );
        assert(post_output_branch.i() == new_branch.i());
        assert(post.linked_i().wf());
        assert(post.linked_i().root == compacted.root);
        assert(post.linked_i().dv.is_sub_disk(compacted.dv)) by {
            assert(post.linked_i().dv == post_tree.dv);
            assert(post_tree.dv.is_sub_disk(compacted.dv));
        };
        assert(post.linked_i().buffer_dv.agrees_with(
            compacted.buffer_dv,
        )) by {
            assert forall |addr: Address|
                #[trigger] post.linked_i().buffer_dv.entries.contains_key(addr)
                    && compacted.buffer_dv.entries.contains_key(addr)
                implies post.linked_i().buffer_dv.entries[addr]
                    == compacted.buffer_dv.entries[addr]
            by {
                assert(full_buffer.entries.contains_key(addr));
                if addr == branch_root {
                    assert(new_branch.disk_view.entries.contains_key(addr));
                    assert(new_branch.disk_view.entries[addr]
                        == new_branch.root());
                } else {
                    assert(pre_linked.buffer_dv.entries.contains_key(addr));
                    assert(compacted.buffer_dv.entries[addr]
                        == pre_linked.buffer_dv.entries[addr]);
                    if new_branch.disk_view.entries.contains_key(addr) {
                        assert(pre_linked.buffer_dv.entries.dom().disjoint(
                            new_branch.disk_view.entries.dom(),
                        ));
                    }
                }
            };
        };
        assert(compacted.valid_view(post.linked_i()));
        sealed_output_branch_observations_preserved(pre, new_branch);
        let local_output_buffer = BufferDisk {
            entries: new_branch.disk_view.entries,
        };
        assert forall |key: crate::spec::KeyType_t::Key| true implies {
            &&& new_branch.root().linked_contains(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) == new_branch.root().linked_contains(
                full_buffer,
                branch_root,
                key,
            )
            &&& new_branch.root().linked_query(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) == new_branch.root().linked_query(
                full_buffer,
                branch_root,
                key,
            )
        } by {
            valid_branches_same_i_same_observations(
                post_output_branch,
                new_branch,
                key,
            );
            assert(local_output_buffer.get_branch(branch_root)
                == new_branch);
            assert(new_branch.root().linked_contains(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) == post_output_branch.contains_internal(
                post_output_branch.the_ranking(),
                key,
            ));
            assert(new_branch.root().linked_contains(
                local_output_buffer,
                branch_root,
                key,
            ) == new_branch.contains_internal(
                new_branch.the_ranking(),
                key,
            ));
            assert(new_branch.root().linked_query(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) == post_output_branch.query(key));
            assert(new_branch.root().linked_query(
                local_output_buffer,
                branch_root,
                key,
            ) == new_branch.query(key));
        };
        assert forall |key: crate::spec::KeyType_t::Key|
            new_branch.root().linked_contains(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) <==> #[trigger] pre_linked.buffer_dv
                .valid_compact_key_domain(
                    linked_path.target().root(),
                    start,
                    end,
                    key,
                )
        by {
            assert(new_branch.root().linked_contains(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) == new_branch.root().linked_contains(
                full_buffer,
                branch_root,
                key,
            ));
        };
        assert forall |key: crate::spec::KeyType_t::Key|
            new_branch.root().linked_contains(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) implies #[trigger] new_branch.root().linked_query(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) == pre_linked.buffer_dv.compact_key_value(
                linked_path.target().root(),
                start,
                end,
                key,
            )
        by {
            assert(new_branch.root().linked_contains(
                full_buffer,
                branch_root,
                key,
            ));
            assert(new_branch.root().linked_query(
                post.linked_i().buffer_dv,
                branch_root,
                key,
            ) == new_branch.root().linked_query(
                full_buffer,
                branch_root,
                key,
            ));
        };
        assert(linked_path.target().compact_buffer_valid_domain(
            start,
            end,
            new_branch.root(),
            post.linked_i().buffer_dv,
            new_addrs.addr2,
        ));
        assert(linked_path.target().compact_buffer_valid_range(
            start,
            end,
            new_branch.root(),
            post.linked_i().buffer_dv,
            new_addrs.addr2,
        ));
        assert(linked_path.target().can_compact(
            start,
            end,
            new_branch.root(),
            post.linked_i().buffer_dv,
            new_addrs,
        ));
        assert(post.i().betree.memtable == pre.i().betree.memtable);
        assert(LinkedBetreeVars::State::internal_compact(
            pre.i().betree,
            post.i().betree,
            crate::allocation_layer::AllocationBranchBetree_v::Internal,
            post.i().betree.linked,
            linked_path,
            start,
            end,
            new_branch.root(),
            new_addrs,
            path_addrs,
        ));
        assert(set_addrs_disjoint_aus(compacted.dv.entries.dom())) by {
            assert(compacted.dv.entries.dom()
                == pre_tree.dv.entries.dom() + writes.dom());
            assert(set_addrs_disjoint_aus(pre_tree.dv.entries.dom()));
            assert forall |left: Address, right: Address|
                compacted.dv.entries.dom().contains(left)
                    && compacted.dv.entries.dom().contains(right)
                    && left != right
                implies #[trigger] addrs_with_different_au(left, right)
            by {
                if writes.contains_key(left) || writes.contains_key(right) {
                    if writes.contains_key(left) && writes.contains_key(right) {
                        if left == new_node_addr || right == new_node_addr {
                            let path_addr = if left == new_node_addr {
                                right
                            } else {
                                left
                            };
                            assert(path_addrs.to_set().contains(path_addr));
                            crate::disk::GenericDisk_v::to_aus_domain(
                                path_addrs.to_set(),
                            );
                            assert(!seq_addrs_to_aus(path_addrs)
                                .contains(new_node_addr.au));
                        } else {
                            let i = choose |i: int|
                                0 <= i < path_addrs.len()
                                    && path_addrs[i] == left;
                            let j = choose |j: int|
                                0 <= j < path_addrs.len()
                                    && path_addrs[j] == right;
                            assert(i != j);
                            assert(path_addrs[i].au != path_addrs[j].au);
                        }
                    } else {
                        let fresh = if writes.contains_key(left) {
                            left
                        } else {
                            right
                        };
                        let old = if writes.contains_key(left) {
                            right
                        } else {
                            left
                        };
                        assert(allocs.contains(fresh.au));
                        assert(pre.betree.betree_aus.dom().contains(old.au));
                        assert(pre.i().is_fresh(allocs));
                    }
                }
            };
        };
        direct_au_restrict_is_domain(
            compacted.dv.entries,
            post_tree.dv.entries.dom(),
        );
        crate::allocation_layer::Likes_v::to_au_likes_domain(
            compacted_tree_likes,
        );
        assert(post.i().betree_aus.dom()
            == to_aus(post_tree.dv.entries.dom()));
        assert(crate::allocation_layer::Likes_v::restrict_domain_au(
            compacted.dv.entries,
            post.i().betree_aus.dom(),
        ) == post.i().betree.linked.dv.entries.dom());
        assert(post.i().betree.linked.buffer_dv.entries
            == full_buffer.entries.restrict(post_buffer_domain));
        assert(lbl.i(pre) is Internal);
        assert(AllocationBranchBetree::State::valid_compactor_input(
            linked_path,
            start,
            end,
            pre.i().compactors[input_idx],
        ));
        assert(post.i().branch_summary
            == full_summary.remove_keys(source_branch_deallocs));
        assert(post.i().compactors == new_compactors);
        assert(deallocs.disjoint(pre.i().branch_allocator_aus())) by {
            assert(source_tree_deallocs <= pre.i().betree_aus.dom());
            assert(summary_deallocs
                <= summary_aus(pre.i().branch_summary));
            assert(pre.i().betree_aus.dom().disjoint(
                pre.i().branch_allocator_aus(),
            ));
            assert(summary_aus(pre.i().branch_summary).disjoint(
                pre.i().branch_allocator_aus(),
            ));
            assert(deallocs == source_tree_deallocs + summary_deallocs);
        };
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().remove(branch_idx),
            j => {
                let pre_idx = if j < branch_idx { j } else { j + 1 };
                assert(post.betree.wip_branches[j]
                    == pre.betree.wip_branches[pre_idx]);
                let cached = pre.betree.wip_branches[pre_idx];
                let allocated = mini_allocator_allocated_addrs(
                    cached.mini_allocator,
                );
                AllocationBulkBranch::alloc_aus_ensures(
                    pre.i().wip_branches,
                    pre_idx,
                );
                assert(cached.mini_allocator.all_aus()
                    <= pre.i().branch_allocator_aus());
                assert(allocs.disjoint(cached.mini_allocator.all_aus())) by {
                    assert(pre.i().is_fresh(allocs));
                };
                assert(deallocs.disjoint(cached.mini_allocator.all_aus()));
                mini_allocator_allocated_addrs_subset_all_aus(
                    cached.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    allocs,
                );
                addresses_in_aus_preserves_disjointness(
                    cached.mini_allocator.all_aus(),
                    deallocs,
                );
                disk_access_for_alloc_visible_outside_alloc_dealloc(
                    pre.disk,
                    new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        );
        assert(post.i().wip_branches
            == pre.i().wip_branches.remove(branch_idx));
        assert(allocation_compact_complete_conditions(
            pre.i(),
            post.i(),
            lbl.i(pre),
            post.i().betree,
            linked_path,
            start,
            end,
            input_idx,
            branch_idx,
            new_node_addr,
            path_addrs,
        ));
        allocation_compact_complete_intro(
            pre.i(),
            post.i(),
            lbl.i(pre),
            post.i().betree,
            linked_path,
            start,
            end,
            input_idx,
            branch_idx,
            new_node_addr,
            path_addrs,
        );
        pre.wip_alloc_aus_agree();
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            == pre.i().branch_allocator_aus());
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(allocs)) by {
            assert(pre.i().is_fresh(allocs));
        }
        assert(cached_bulk_branch_alloc_aus(pre.betree.wip_branches)
            .disjoint(deallocs));
        CompactorInput::input_roots_remove_subset(
            pre.betree.compactors,
            input_idx,
        );
        crate::disk::GenericDisk_v::to_aus_preserves_lte(
            CompactorInput::input_roots(post.betree.compactors),
            CompactorInput::input_roots(pre.betree.compactors),
        );
        assert(read_ref_aus(post.betree.compactors)
            <= read_ref_aus(pre.betree.compactors)) by {
            assert forall |au: AU|
                #[trigger] read_ref_aus(post.betree.compactors).contains(au)
                implies read_ref_aus(pre.betree.compactors).contains(au)
            by {
                let root = choose |root: Address|
                    CompactorInput::input_roots(
                        post.betree.compactors,
                    ).contains(root) && root.au == au;
                assert(CompactorInput::input_roots(
                    pre.betree.compactors,
                ).contains(root));
            }
        }
        pre.i().inv_branch_summary_ensures();
        assert forall |au: AU|
            #[trigger] read_ref_aus(post.betree.compactors).contains(au)
            implies
                post.betree.branch_summary.contains_key(au)
                && pre.betree.branch_summary.contains_key(au)
                && post.betree.branch_summary[au]
                    == pre.betree.branch_summary[au]
        by {
            assert(pre.betree.branch_summary.contains_key(au));
            assert(au != branch_root.au);
            assert(!source_branch_deallocs.contains(au));
            assert(full_summary[au] == pre.betree.branch_summary[au]);
        }
        Self::removed_compactor_receipt_preserves_inv(
            pre,
            post,
            input_idx,
        );
        Self::removed_wip_preserves_staged_nodes_after_access(
            pre,
            post,
            lbl,
            new_disk,
            access,
            branch_idx,
        );
    }

    proof fn branch_stage_page_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        addr: Address,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                BranchBuildEvent::StagePage{addr}.cached_event(access),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx]
                    .mini_allocator.all_aus(),
            ),
            AllocationBranchBetree::State::branch_build(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
                post.i().wip_branches[idx],
                BulkBranchEvent::StagePage{addr},
                lbl.arrow_InternalAllocAccess_allocs(),
                lbl.arrow_InternalAllocAccess_deallocs(),
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        access.cached_only_branch_is_only_branch();

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let pre_cached = pre.betree.wip_branches[idx];
        let pre_target = pre.wip_branch_i(idx);
        let write_nodes = access.loaded_branch_writes();

        assert(allocs.is_empty());
        assert(deallocs.is_empty());
        assert(access.only_branch());
        assert(writes == access.branch_writes);
        assert(write_nodes.dom() == set![addr]);
        assert(writes.dom() == set![addr]);
        assert(pre_cached.mini_allocator.can_allocate(addr));
        assert(pre_cached.mini_allocator.all_aus()
            .contains(addr.au));
        assert(writes.dom() <= addresses_in_aus(
            pre_cached.mini_allocator.all_aus(),
        ));

        Self::branch_build_nonseal_preserves_shared_state(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::StagePage{addr},
            access,
        );
        disk_access_without_alloc_or_dealloc(
            pre.disk,
            new_disk,
            guard_aus,
            reads,
            writes,
        );
        assert(pre.i().wip_branches_inv());
        assert(pre_target == pre.i().wip_branches[idx]);
        assert(pre_target.inv());
        assert(pre_target.mini_allocator
            == pre_cached.mini_allocator);
        assert(pre_cached.mini_allocator.wf());
        assert(post_branch.mini_allocator
            == pre_cached.mini_allocator.allocate(addr));
        mini_allocator_allocated_addrs_after_allocate(
            pre_cached.mini_allocator,
            addr,
        );
        assert(mini_allocator_allocated_addrs(
            post_branch.mini_allocator,
        ) == mini_allocator_allocated_addrs(
            pre_cached.mini_allocator,
        ).insert(addr));
        assert(mini_allocator_allocated_addrs(
            post_branch.mini_allocator,
        ) == mini_allocator_allocated_addrs(
            pre_cached.mini_allocator,
        ) + writes.dom()) by {
            assert_sets_equal!(
                mini_allocator_allocated_addrs(
                    post_branch.mini_allocator,
                ),
                mini_allocator_allocated_addrs(
                    pre_cached.mini_allocator,
                ) + writes.dom(),
                candidate => {}
            );
        }
        wip_entries_after_writes(
            pre.disk,
            new_disk,
            pre_cached.mini_allocator,
            post_branch.mini_allocator,
            reads,
            writes,
        );
        assert(pre_cached.staged_nodes()
            == to_branch_nodes(pre.disk.visible()).restrict(
                mini_allocator_allocated_addrs(
                    pre_cached.mini_allocator,
                ),
            ));
        assert(post_branch.staged_nodes()
            == pre_cached.staged_nodes().insert(addr, write_nodes[addr]));
        assert(post_branch.staged_nodes()
            == to_branch_nodes(new_disk.visible()).restrict(
                mini_allocator_allocated_addrs(
                    post_branch.mini_allocator,
                ),
            )) by {
            assert_maps_equal!(
                post_branch.staged_nodes(),
                to_branch_nodes(new_disk.visible()).restrict(
                    mini_allocator_allocated_addrs(
                        post_branch.mini_allocator,
                    ),
                ),
                candidate => {}
            );
        }
        assert(post.wip_branch_i(idx)
            == pre_target.stage_page(addr));
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().update(
                idx,
                pre_target.stage_page(addr),
            ),
            j => {
                if j != idx {
                    assert(post.wip_branch_i(j)
                        == pre.wip_branch_i(j));
                }
            }
        );
        assert(post.staged_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_building()
                implies #[trigger]
                    post.betree.wip_branches[j].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[j]
                                    .mini_allocator,
                            ),
                        ) by {
                if j == idx {
                    assert(post.betree.wip_branches[j]
                        == post_branch);
                } else {
                    assert(post.betree.wip_branches[j]
                        == pre.betree.wip_branches[j]);
                    assert(post.wip_branch_i(j)
                        == pre.wip_branch_i(j));
                }
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[j].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[j]
                                .mini_allocator,
                        ),
                    ) by {
                assert(j != idx);
                let source = pre.betree.wip_branches[j];
                let stable = mini_allocator_allocated_addrs(
                    source.mini_allocator,
                );
                assert(post.betree.wip_branches[j] == source);
                assert(source.is_sealed());
                assert(source.sealed_branch().disk_view.entries
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        stable,
                    ));
                assert(pre.i().wip_branches_disjoint());
                assert(pre.i().wip_branches[j].mini_allocator
                    == source.mini_allocator);
                assert(pre.i().wip_branches[idx].mini_allocator
                    == pre_cached.mini_allocator);
                assert(source.mini_allocator.all_aus().disjoint(
                    pre_cached.mini_allocator.all_aus(),
                ));
                mini_allocator_allocated_addrs_subset_all_aus(
                    source.mini_allocator,
                );
                addresses_in_aus_preserves_disjointness(
                    source.mini_allocator.all_aus(),
                    pre_cached.mini_allocator.all_aus(),
                );
                assert(stable.disjoint(writes.dom()));
                disk_access_empty_alloc_visible_stable(
                    pre.disk,
                    new_disk,
                    deallocs,
                    guard_aus,
                    reads,
                    writes,
                    stable,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    stable,
                );
            }
        }
        Self::unchanged_compactor_receipts_preserve_inv(pre, post);
    }

    proof fn branch_bulk_seal_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        root: Address,
        aux_ptr: Pointer,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                BranchBuildEvent::BulkSeal{root, aux_ptr}.cached_event(access),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx]
                    .mini_allocator.all_aus(),
            ),
            AllocationBranchBetree::State::branch_build(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
                post.i().wip_branches[idx],
                BulkBranchEvent::BulkSeal {
                    root,
                    aux_ptr,
                    branch: post.i().wip_branches[idx]
                        .sealed_branch(),
                },
                lbl.arrow_InternalAllocAccess_allocs(),
                lbl.arrow_InternalAllocAccess_deallocs(),
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        access.cached_only_branch_is_only_branch();

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let write_nodes = access.loaded_branch_writes();
        let pre_cached = pre.betree.wip_branches[idx];
        let pre_target = pre.wip_branch_i(idx);
        let with_root = pre_cached.mini_allocator.allocate(root);
        let allocator = if aux_ptr is Some {
            with_root.allocate(aux_ptr.unwrap())
        } else {
            with_root
        };
        let cached_branch = pre_cached.staged_branch(root, write_nodes);
        let witness = disk_access_for_alloc_witness(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            reads,
            writes,
        );

        assert(allocs.is_empty());
        disk_extend_empty_is_identity(pre.disk, witness.expanded);
        assert(witness.expanded == pre.disk);
        assert(access.only_branch());
        assert(writes == access.branch_writes);
        assert(deallocs == allocator.removable_aus());
        assert(post_branch.mini_allocator
            == allocator.prune(deallocs));
        assert(post_branch.sealed_root() == root);
        assert(post_branch.is_sealed());
        assert(cached_branch.valid_sealed_branch());
        assert(cached_branch.tight_disk_view_with_summary());
        assert(cached_branch.get_summary()
            == allocator.all_aus() - deallocs);

        assert(writes.dom() == write_nodes.dom());
        if aux_ptr is Some {
            assert(write_nodes.dom()
                == set![root, aux_ptr.unwrap()]);
        } else {
            assert(write_nodes.dom() == set![root]);
        }
        assert(writes.dom() <= addresses_in_aus(
            pre_cached.mini_allocator.all_aus(),
        )) by {
            assert forall |addr: Address|
                #[trigger] writes.contains_key(addr)
                implies addresses_in_aus(
                    pre_cached.mini_allocator.all_aus(),
                ).contains(addr) by {
                if aux_ptr is Some && addr == aux_ptr.unwrap() {
                    pre_cached.mini_allocator
                        .allocate_can_allocate_subset(root, addr);
                } else {
                    assert(addr == root);
                }
                assert(pre_cached.mini_allocator.can_allocate(addr));
                assert(pre_cached.mini_allocator.all_aus()
                    .contains(addr.au));
            }
        }

        assert(pre.i().wip_branches_inv());
        assert(pre_target == pre.i().wip_branches[idx]);
        assert(pre_target.inv());
        assert(pre_target.is_building());
        assert(pre_target.mini_allocator
            == pre_cached.mini_allocator);
        assert(pre_cached.mini_allocator.wf());
        crate::implementation::BranchProofUtils_v::
            mini_allocator_allocate_preserves_all_aus(
                pre_cached.mini_allocator,
                root,
            );
        if aux_ptr is Some {
            crate::implementation::BranchProofUtils_v::
                mini_allocator_allocate_preserves_all_aus(
                    with_root,
                    aux_ptr.unwrap(),
                );
        }
        assert(allocator.all_aus()
            == pre_cached.mini_allocator.all_aus());
        assert(deallocs <= pre_cached.mini_allocator.all_aus()) by {
            assert forall |au: AU|
                #[trigger] deallocs.contains(au)
                implies pre_cached.mini_allocator.all_aus()
                    .contains(au) by {
                assert(allocator.can_remove(au));
                assert(allocator.all_aus().contains(au));
            }
        }

        mini_allocator_allocated_addrs_after_allocate(
            pre_cached.mini_allocator,
            root,
        );
        if aux_ptr is Some {
            mini_allocator_allocated_addrs_after_allocate(
                with_root,
                aux_ptr.unwrap(),
            );
        }
        assert(mini_allocator_allocated_addrs(allocator)
            == mini_allocator_allocated_addrs(
                pre_cached.mini_allocator,
            ) + writes.dom()) by {
            assert_sets_equal!(
                mini_allocator_allocated_addrs(allocator),
                mini_allocator_allocated_addrs(
                    pre_cached.mini_allocator,
                ) + writes.dom(),
                addr => {}
            );
        }
        wip_entries_after_writes(
            pre.disk,
            witness.accessed,
            pre_cached.mini_allocator,
            allocator,
            reads,
            writes,
        );
        assert(pre_cached.staged_nodes()
            == to_branch_nodes(pre.disk.visible()).restrict(
                mini_allocator_allocated_addrs(
                    pre_cached.mini_allocator,
                ),
            ));
        assert(to_branch_nodes(witness.accessed.visible()).restrict(
            mini_allocator_allocated_addrs(allocator),
        ) == cached_branch.disk_view.entries) by {
        }

        mini_allocator_allocated_addrs_after_prune(
            allocator,
            deallocs,
        );
        assert(mini_allocator_allocated_addrs(allocator)
            .disjoint(addresses_in_aus(deallocs))) by {
            assert forall |addr: Address|
                #[trigger] mini_allocator_allocated_addrs(allocator)
                    .contains(addr)
                implies !addresses_in_aus(deallocs).contains(addr) by {
                if deallocs.contains(addr.au) {
                    assert(allocator.can_remove(addr.au));
                    assert(allocator.allocs[addr.au]
                        .has_no_allocated_pages());
                    assert(false);
                }
            }
        }
        assert(mini_allocator_allocated_addrs(
            post_branch.mini_allocator,
        ) == mini_allocator_allocated_addrs(allocator)) by {
            assert_sets_equal!(
                mini_allocator_allocated_addrs(
                    post_branch.mini_allocator,
                ),
                mini_allocator_allocated_addrs(allocator),
                addr => {}
            );
        }
        assert(addresses_in_aus(deallocs - guard_aus).disjoint(
            mini_allocator_allocated_addrs(
                post_branch.mini_allocator,
            ),
        ));
        disk_forget_visible_outside_aus(
            witness.accessed,
            new_disk,
            deallocs - guard_aus,
            mini_allocator_allocated_addrs(
                post_branch.mini_allocator,
            ),
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            witness.accessed.visible(),
            mini_allocator_allocated_addrs(
                post_branch.mini_allocator,
            ),
        );
        assert(to_branch_nodes(new_disk.visible()).restrict(
            mini_allocator_allocated_addrs(
                post_branch.mini_allocator,
            ),
        ) == cached_branch.disk_view.entries);
        assert(post.wip_branch_i(idx).sealed_branch()
            == cached_branch);
        assert(pre_target.can_bulk_seal(
            root,
            aux_ptr,
            cached_branch,
            deallocs,
        ));
        assert(post.wip_branch_i(idx)
            == pre_target.bulk_seal(
                root,
                aux_ptr,
                cached_branch,
                deallocs,
            ));

        let selected_aus = pre_cached.mini_allocator.all_aus();
        let betree_addrs = addresses_in_aus(
            pre.betree.betree_aus.dom(),
        );
        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );
        pre.wip_alloc_aus_agree();
        AllocationBulkBranch::alloc_aus_ensures(
            pre.i().wip_branches,
            idx,
        );
        assert(selected_aus <= pre.i().branch_allocator_aus());
        assert(pre.i().betree_aus.dom().disjoint(selected_aus));
        assert(summary_aus(pre.i().branch_summary)
            .disjoint(selected_aus));
        addresses_in_aus_preserves_disjointness(
            pre.i().betree_aus.dom(),
            selected_aus,
        );
        addresses_in_aus_preserves_disjointness(
            summary_aus(pre.i().branch_summary),
            selected_aus,
        );
        assert(betree_addrs.disjoint(writes.dom()));
        assert(sealed_addrs.disjoint(writes.dom()));
        assert(betree_addrs.disjoint(addresses_in_aus(
            deallocs - guard_aus,
        )));
        assert(sealed_addrs.disjoint(addresses_in_aus(
            deallocs - guard_aus,
        )));
        disk_access_empty_alloc_visible_stable(
            pre.disk,
            new_disk,
            deallocs,
            guard_aus,
            reads,
            writes,
            betree_addrs,
        );
        disk_access_empty_alloc_visible_stable(
            pre.disk,
            new_disk,
            deallocs,
            guard_aus,
            reads,
            writes,
            sealed_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            betree_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            sealed_addrs,
        );
        assert(post.visible_betree_entries()
            == pre.visible_betree_entries());
        assert(post.visible_sealed_branch_entries()
            == pre.visible_sealed_branch_entries());
        assert(post.linked_i() == pre.linked_i());
        assert(post.semantic_selector_inv());

        assert forall |j: int|
            0 <= j < pre.betree.wip_branches.len() && j != idx
            implies {
                &&& #[trigger] post.wip_branch_i(j)
                    == pre.wip_branch_i(j)
                &&& post.betree.wip_branches[j].is_building()
                    ==> post.betree.wip_branches[j].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[j]
                                    .mini_allocator,
                            ),
                        )
            } by {
            assert(post.betree.wip_branches[j]
                == pre.betree.wip_branches[j]);
            let cached = pre.betree.wip_branches[j];
            let stable = mini_allocator_allocated_addrs(
                cached.mini_allocator,
            );
            assert(pre.i().wip_branches_disjoint());
            assert(pre.i().wip_branches[j].mini_allocator
                == cached.mini_allocator);
            assert(pre.i().wip_branches[idx].mini_allocator
                == pre_cached.mini_allocator);
            assert(cached.mini_allocator.all_aus()
                .disjoint(selected_aus));
            mini_allocator_allocated_addrs_subset_all_aus(
                cached.mini_allocator,
            );
            addresses_in_aus_preserves_disjointness(
                cached.mini_allocator.all_aus(),
                selected_aus,
            );
            assert(stable.disjoint(writes.dom()));
            assert(stable.disjoint(addresses_in_aus(
                deallocs - guard_aus,
            )));
            disk_access_empty_alloc_visible_stable(
                pre.disk,
                new_disk,
                deallocs,
                guard_aus,
                reads,
                writes,
                stable,
            );
            to_branch_nodes_restrict_agrees(
                new_disk.visible(),
                pre.disk.visible(),
                stable,
            );
        }
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().update(
                idx,
                post.wip_branch_i(idx),
            ),
            j => {
                if j != idx {
                    assert(post.wip_branch_i(j)
                        == pre.wip_branch_i(j));
                }
            }
        );
        assert(post.staged_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_building()
                implies #[trigger]
                    post.betree.wip_branches[j].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[j]
                                    .mini_allocator,
                            ),
                        ) by {
                assert(j != idx);
                assert(post.betree.wip_branches[j]
                    == pre.betree.wip_branches[j]);
                assert(pre.betree.wip_branches[j].is_building());
                assert(pre.betree.wip_branches[j].staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            pre.betree.wip_branches[j]
                                .mini_allocator,
                        ),
                    ));
                assert(post.wip_branch_i(j)
                    == pre.wip_branch_i(j));
                assert(post.betree.wip_branches[j].staged_nodes()
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[j]
                                .mini_allocator,
                        ),
                    ));
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[j].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[j]
                                .mini_allocator,
                        ),
                    ) by {
                if j == idx {
                    assert(post.betree.wip_branches[j] == post_branch);
                    assert(post_branch.sealed_branch() == cached_branch);
                    assert(to_branch_nodes(new_disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post_branch.mini_allocator,
                        ),
                    ) == cached_branch.disk_view.entries);
                } else {
                    let source = pre.betree.wip_branches[j];
                    let stable = mini_allocator_allocated_addrs(
                        source.mini_allocator,
                    );
                    assert(post.betree.wip_branches[j] == source);
                    assert(source.is_sealed());
                    assert(source.sealed_branch().disk_view.entries
                        == to_branch_nodes(pre.disk.visible()).restrict(
                            stable,
                        ));
                    assert(pre.i().wip_branches_disjoint());
                    assert(pre.i().wip_branches[j].mini_allocator
                        == source.mini_allocator);
                    assert(pre.i().wip_branches[idx].mini_allocator
                        == pre_cached.mini_allocator);
                    assert(source.mini_allocator.all_aus()
                        .disjoint(selected_aus));
                    mini_allocator_allocated_addrs_subset_all_aus(
                        source.mini_allocator,
                    );
                    addresses_in_aus_preserves_disjointness(
                        source.mini_allocator.all_aus(),
                        selected_aus,
                    );
                    assert(stable.disjoint(writes.dom()));
                    assert(stable.disjoint(addresses_in_aus(
                        deallocs - guard_aus,
                    )));
                    disk_access_empty_alloc_visible_stable(
                        pre.disk,
                        new_disk,
                        deallocs,
                        guard_aus,
                        reads,
                        writes,
                        stable,
                    );
                    to_branch_nodes_restrict_agrees(
                        new_disk.visible(),
                        pre.disk.visible(),
                        stable,
                    );
                }
            }
        }
        Self::unchanged_compactor_receipts_preserve_inv(pre, post);
    }

    /*
     * Preserved mutable WIP branch refinements. The active Betree path uses
     * only branch_stage_page_refines and branch_bulk_seal_refines. These
     * proofs remain here as reference for a future branch-as-memtable design.
     *
    proof fn branch_initialize_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        init_root: Address,
        keys: Seq<crate::spec::KeyType_t::Key>,
        msgs: Seq<Message>,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                BranchBuildEvent::Initialize{
                    init_root, keys, msgs,
                }.cached_event(access),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx].mini_allocator.all_aus(),
            ),
            AllocationBranchBetree::State::branch_build(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
                post.i().wip_branches[idx],
                BuildEvent::Initialize{addr: init_root, keys, msgs},
            ),
    {
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let pre_cached = pre.betree.wip_branches[idx];
        let pre_target = pre.wip_branch_i(idx);
        let expected = pre_target.branch_initialize(init_root, keys, msgs);
        let witness = disk_access_for_alloc_witness(
            pre.disk,
            new_disk,
        allocs,
        deallocs,
        guard_aus,
        reads,
        writes,
        );

        assert(allocs.is_empty());
        assert(deallocs.is_empty());
        disk_extend_empty_is_identity(pre.disk, witness.expanded);
        assert(witness.expanded == pre.disk);
        assert(access.only_branch());
        assert(writes == access.branch_writes);
        assert(access.loaded_branch_writes()
            == loaded_initialize_write_nodes(init_root, keys, msgs));
        assert(writes.dom() == set![init_root]);
        assert(witness.accessed.visible()
            == pre.disk.visible().union_prefer_right(writes));
        assert(new_disk.visible() == witness.accessed.visible());

        let betree_addrs = addresses_in_aus(pre.betree.betree_aus.dom());
        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );
        assert(pre.i().betree_aus.dom()
            .disjoint(pre.i().branch_allocator_aus()));
        assert(summary_aus(pre.i().branch_summary)
            .disjoint(pre.i().branch_allocator_aus()));
        AllocationBulkBranch::alloc_aus_ensures(pre.i().wip_branches, idx);
        assert(pre_cached.mini_allocator.all_aus()
            <= pre.i().branch_allocator_aus());
        assert(betree_addrs.disjoint(writes.dom())) by {
            assert forall |addr: Address| #[trigger] betree_addrs.contains(addr)
                implies !writes.contains_key(addr)
            by {
                if writes.contains_key(addr) {
                    assert(addr == init_root);
                    assert(pre_cached.mini_allocator.all_aus().contains(addr.au));
                    assert(false);
                }
            };
        }
        assert(sealed_addrs.disjoint(writes.dom())) by {
            assert forall |addr: Address| #[trigger] sealed_addrs.contains(addr)
                implies !writes.contains_key(addr)
            by {
                if writes.contains_key(addr) {
                    assert(addr == init_root);
                    assert(pre_cached.mini_allocator.all_aus().contains(addr.au));
                    assert(false);
                }
            };
        }
        disk_access_empty_alloc_visible_stable(
            pre.disk,
            new_disk,
            deallocs,
            guard_aus,
            reads,
            writes,
            betree_addrs,
        );
        disk_access_empty_alloc_visible_stable(
            pre.disk,
            new_disk,
            deallocs,
            guard_aus,
            reads,
            writes,
            sealed_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            betree_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            sealed_addrs,
        );
        assert(post.visible_betree_entries() == pre.visible_betree_entries());
        assert(post.visible_sealed_branch_entries()
            == pre.visible_sealed_branch_entries());
        assert(post.linked_i() == pre.linked_i());

        assert(pre.i().wip_branches_inv());
        assert(pre_target == pre.i().wip_branches[idx]);
        assert(pre_target.inv());
        assert(pre_target.branch is None);
        assert(pre_target.mini_allocator == pre_cached.mini_allocator);
        assert(pre_target.can_initialize(init_root, keys, msgs));
        assert(post_branch.mini_allocator
            == pre_cached.mini_allocator.allocate(init_root));
        assert(post_branch.branch.root == Some(init_root));
        assert(post.wip_branch_i(idx).mini_allocator
            == expected.mini_allocator);
        assert(post.wip_branch_i(idx).is_sealed() == expected.is_sealed());

        assert(mini_allocator_allocated_addrs(post_branch.mini_allocator)
            == set![init_root]) by {
            assert forall |addr: Address|
                #[trigger] mini_allocator_allocated_addrs(post_branch.mini_allocator)
                    .contains(addr)
                <==> addr == init_root
            by {
                if addr != init_root
                    && post_branch.mini_allocator.page_is_allocated(addr)
                {
                    assert(pre_cached.mini_allocator.page_is_allocated(addr));
                    assert(pre_cached.mini_allocator.allocated_aus().contains(addr.au));
                    assert(false);
                }
            };
        }
        assert(post.wip_branch_i(idx).branch is Some);
        assert(post.wip_branch_i(idx).sealed_branch().root == init_root);
        assert(post.wip_branch_i(idx).sealed_branch().disk_view.entries
            == map![init_root => crate::allocation_layer::BranchTypes_v::BranchNode::Leaf{
                keys,
                msgs,
            }]) by {
            assert(new_disk.visible().contains_key(init_root));
            assert(new_disk.visible()[init_root] == writes[init_root]);
            assert(to_branch_nodes(writes)[init_root]
                == crate::allocation_layer::BranchTypes_v::BranchNode::Leaf{
                    keys,
                    msgs,
                });
        }
        assert(post.wip_branch_i(idx) == expected);
        assert(writes.dom() <= addresses_in_aus(
            pre_cached.mini_allocator.all_aus(),
        ));

        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().update(idx, expected),
            j => {
                if j == idx {
                    assert(post.betree.wip_branches[j] == post_branch);
                } else {
                    assert(post.betree.wip_branches[j]
                        == pre.betree.wip_branches[j]);
                    let cached = pre.betree.wip_branches[j];
                    let stable = mini_allocator_allocated_addrs(cached.mini_allocator);
                    AllocationBulkBranch::alloc_aus_ensures(pre.i().wip_branches, j);
                    mini_allocator_allocated_addrs_subset_all_aus(cached.mini_allocator);
                    assert(pre.i().wip_branches_disjoint());
                    assert(pre.i().wip_branches[j].mini_allocator
                        == cached.mini_allocator);
                    assert(pre.i().wip_branches[idx].mini_allocator
                        == pre_cached.mini_allocator);
                    assert(pre.i().wip_branches[j].mini_allocator.all_aus()
                        .disjoint(
                            pre.i().wip_branches[idx].mini_allocator.all_aus(),
                        ));
                    assert(cached.mini_allocator.all_aus()
                        .disjoint(pre_cached.mini_allocator.all_aus()));
                    assert(pre_cached.mini_allocator.all_aus().contains(init_root.au));
                    assert(stable.disjoint(writes.dom())) by {
                        assert forall |addr: Address| #[trigger] stable.contains(addr)
                            implies !writes.contains_key(addr)
                        by {
                            if writes.contains_key(addr) {
                                assert(addr == init_root);
                                assert(cached.mini_allocator.all_aus().contains(addr.au));
                                assert(false);
                            }
                        };
                    }
                    disk_access_empty_alloc_visible_stable(
                        pre.disk,
                        new_disk,
                        deallocs,
                        guard_aus,
                        reads,
                        writes,
                        stable,
                    );
                    to_branch_nodes_restrict_agrees(
                        new_disk.visible(),
                        pre.disk.visible(),
                        stable,
                    );
                }
            }
        );
        AllocationBranchBetree::State::branch_build_delta_witness(
            pre.i(),
            idx,
            post.i().wip_branches[idx],
            BuildEvent::Initialize{addr: init_root, keys, msgs},
            allocs,
            deallocs,
        );
        Self::rooted_branch_build_preserves_staged_nodes(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::Initialize{init_root, keys, msgs},
            access,
        );
    }

    proof fn branch_append_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        receipt: crate::implementation::CachedBranch_v::LoadedPathReceipt,
        keys: Seq<crate::spec::KeyType_t::Key>,
        msgs: Seq<Message>,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                BranchBuildEvent::Append{
                    receipt, keys, msgs,
                }.cached_event(access),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx].mini_allocator.all_aus(),
            ),
            AllocationBranchBetree::State::branch_build(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
                post.i().wip_branches[idx],
                BuildEvent::Append{
                    keys,
                    msgs,
                    path: BranchPath{
                        branch: pre.i().wip_branches[idx].sealed_branch(),
                        key: keys[0],
                        depth: receipt.depth(),
                    },
                },
            ),
    {
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let read_nodes = access.loaded_branch_reads();
        let write_nodes = access.loaded_branch_writes();
        let pre_cached = pre.betree.wip_branches[idx];
        let pre_target = pre.wip_branch_i(idx);
        let branch = pre_target.sealed_branch();
        let path = BranchPath{
            branch,
            key: keys[0],
            depth: receipt.depth(),
        };
        let expected = pre_target.branch_append(keys, msgs, path);

        assert(allocs.is_empty());
        assert(deallocs.is_empty());
        assert(access.only_branch());
        assert(read_nodes == to_branch_nodes(reads));
        assert(write_nodes == to_branch_nodes(writes));
        assert(write_nodes == loaded_append_write_nodes(receipt, keys, msgs));
        disk_access_without_alloc_or_dealloc(
            pre.disk,
            new_disk,
            guard_aus,
            reads,
            writes,
        );
        CachingDisk::State::access_visible_effect(
            pre.disk,
            new_disk,
            reads,
            writes,
        );

        assert(pre.i().wip_branches_inv());
        assert(pre_target.inv());
        assert(pre_target.branch is Some);
        assert(!pre_target.is_sealed());
        assert(branch.inv());
        assert(branch.disk_view.entries
            <= to_branch_nodes(pre.disk.visible()));
        receipt_path_valid_for_append(
            pre.disk,
            branch,
            branch.the_ranking(),
            reads,
            receipt,
            keys,
            msgs,
        );
        assert(path.valid());
        assert(path.branch == branch);
        assert(pre_target.can_append(keys, msgs, path));
        LinkedBranchRefinement::append_refines(branch, keys, msgs, path);

        let target = receipt.target().addr;
        assert(branch.disk_view.entries.contains_key(target));
        assert(pre_target.addrs_closed_under_mini_allocator());
        assert(pre_cached.mini_allocator.page_is_allocated(target));
        assert(mini_allocator_allocated_addrs(pre_cached.mini_allocator)
            .contains(target));
        assert(writes.dom() == set![target]) by {
            assert(write_nodes.dom() == set![target]);
            assert(to_branch_nodes(writes).dom() == writes.dom());
        };
        assert(mini_allocator_allocated_addrs(post_branch.mini_allocator)
            == mini_allocator_allocated_addrs(pre_cached.mini_allocator));
        assert(mini_allocator_allocated_addrs(post_branch.mini_allocator)
            == mini_allocator_allocated_addrs(pre_cached.mini_allocator)
                + writes.dom());
        wip_entries_after_writes(
            pre.disk,
            new_disk,
            pre_cached.mini_allocator,
            post_branch.mini_allocator,
            reads,
            writes,
        );

        let appended = branch.append(keys, msgs, path);
        assert(appended.disk_view.entries
            == branch.disk_view.entries.union_prefer_right(write_nodes)) by {
            assert_maps_equal!(
                appended.disk_view.entries,
                branch.disk_view.entries.union_prefer_right(write_nodes),
                addr => {
                    if write_nodes.contains_key(addr) {
                        assert(addr == target);
                        assert(appended.disk_view.entries[addr]
                            == write_nodes[addr]);
                    } else {
                        assert(addr != target);
                        assert(appended.disk_view.entries[addr]
                            == branch.disk_view.entries[addr]);
                    }
                }
            );
        };
        assert(post.wip_branch_i(idx).is_sealed() == expected.is_sealed());
        assert(post.wip_branch_i(idx).mini_allocator
            == expected.mini_allocator);
        assert(post.wip_branch_i(idx).branch is Some);
        assert(post.wip_branch_i(idx).sealed_branch().root == appended.root);
        assert(post.wip_branch_i(idx).sealed_branch().disk_view.entries
            == appended.disk_view.entries);
        assert(post.wip_branch_i(idx) == expected);

        assert(writes.dom() <= addresses_in_aus(
            pre_cached.mini_allocator.all_aus(),
        )) by {
            mini_allocator_allocated_addrs_subset_all_aus(
                pre_cached.mini_allocator,
            );
        };
        Self::branch_build_nonseal_preserves_shared_state(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::Append{receipt, keys, msgs},
            access,
        );
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().update(idx, expected),
            j => {
                if j == idx {
                    assert(post.wip_branch_i(j) == expected);
                } else {
                    assert(post.wip_branch_i(j) == pre.wip_branch_i(j));
                }
            }
        );
        AllocationBranchBetree::State::branch_build_delta_witness(
            pre.i(),
            idx,
            post.i().wip_branches[idx],
            BuildEvent::Append{keys, msgs, path},
            allocs,
            deallocs,
        );
        Self::rooted_branch_build_preserves_staged_nodes(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::Append{receipt, keys, msgs},
            access,
        );
    }

    proof fn branch_grow_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        new_root_addr: Address,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                BranchBuildEvent::Grow{new_root_addr}.cached_event(access),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx].mini_allocator.all_aus(),
            ),
            AllocationBranchBetree::State::branch_build(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
                post.i().wip_branches[idx],
                BuildEvent::Grow{addr: new_root_addr},
            ),
    {
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let write_nodes = access.loaded_branch_writes();
        let pre_cached = pre.betree.wip_branches[idx];
        let pre_target = pre.wip_branch_i(idx);
        let branch = pre_target.sealed_branch();
        let expected = pre_target.branch_grow(new_root_addr);

        assert(allocs.is_empty());
        assert(deallocs.is_empty());
        assert(access.only_branch());
        assert(write_nodes == to_branch_nodes(writes));
        assert(write_nodes == loaded_grow_write_nodes(
            pre_cached.branch.root.unwrap(),
            new_root_addr,
        ));
        assert(pre_cached.branch.root == Some(branch.root));
        assert(writes.dom() == set![new_root_addr]) by {
            assert(write_nodes.dom() == set![new_root_addr]);
            assert(to_branch_nodes(writes).dom() == writes.dom());
        };

        assert(pre.i().wip_branches_inv());
        assert(pre_target == pre.i().wip_branches[idx]);
        assert(pre_target.inv());
        assert(pre_target.branch is Some);
        assert(!pre_target.is_sealed());
        assert(pre_cached.mini_allocator.wf());
        assert(pre_cached.mini_allocator.can_allocate(new_root_addr));
        assert(pre_target.addrs_closed_under_mini_allocator());
        assert(!branch.disk_view.entries.contains_key(new_root_addr)) by {
            if branch.disk_view.entries.contains_key(new_root_addr) {
                assert(pre_cached.mini_allocator.page_is_allocated(new_root_addr));
                assert(false);
            }
        };
        assert(branch.disk_view.is_fresh(set![new_root_addr]));
        assert(pre_target.can_grow(new_root_addr));

        disk_access_without_alloc_or_dealloc(
            pre.disk,
            new_disk,
            guard_aus,
            reads,
            writes,
        );
        mini_allocator_allocated_addrs_after_allocate(
            pre_cached.mini_allocator,
            new_root_addr,
        );
        assert(post_branch.mini_allocator
            == pre_cached.mini_allocator.allocate(new_root_addr));
        assert(mini_allocator_allocated_addrs(post_branch.mini_allocator)
            == mini_allocator_allocated_addrs(pre_cached.mini_allocator)
                + writes.dom());
        wip_entries_after_writes(
            pre.disk,
            new_disk,
            pre_cached.mini_allocator,
            post_branch.mini_allocator,
            reads,
            writes,
        );

        let grown = branch.grow(new_root_addr);
        assert(grown.disk_view.entries
            == branch.disk_view.entries.union_prefer_right(write_nodes));
        assert(post.wip_branch_i(idx).is_sealed() == expected.is_sealed());
        assert(post.wip_branch_i(idx).mini_allocator
            == expected.mini_allocator);
        assert(post.wip_branch_i(idx).branch is Some);
        assert(post.wip_branch_i(idx).sealed_branch().root == grown.root);
        assert(post.wip_branch_i(idx).sealed_branch().disk_view.entries
            == grown.disk_view.entries);
        assert(post.wip_branch_i(idx) == expected);

        mini_allocator_allocate_preserves_all_aus(
            pre_cached.mini_allocator,
            new_root_addr,
        );
        assert(writes.dom() <= addresses_in_aus(
            pre_cached.mini_allocator.all_aus(),
        ));
        Self::branch_build_nonseal_preserves_shared_state(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::Grow{new_root_addr},
            access,
        );
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().update(idx, expected),
            j => {
                if j == idx {
                    assert(post.wip_branch_i(j) == expected);
                } else {
                    assert(post.wip_branch_i(j) == pre.wip_branch_i(j));
                }
            }
        );
        AllocationBranchBetree::State::branch_build_delta_witness(
            pre.i(),
            idx,
            post.i().wip_branches[idx],
            BuildEvent::Grow{addr: new_root_addr},
            allocs,
            deallocs,
        );
        Self::rooted_branch_build_preserves_staged_nodes(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::Grow{new_root_addr},
            access,
        );
    }

    proof fn branch_split_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        new_child_addr: Address,
        receipt: crate::implementation::CachedBranch_v::LoadedPathReceipt,
        split_arg: crate::betree::LinkedBranch_v::SplitArg,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                BranchBuildEvent::Split{
                    new_child_addr,
                    receipt,
                    split_arg,
                }.cached_event(access),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx].mini_allocator.all_aus(),
            ),
            AllocationBranchBetree::State::branch_build(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
                post.i().wip_branches[idx],
                BuildEvent::Split{
                    addr: new_child_addr,
                    path: BranchPath{
                        branch: pre.i().wip_branches[idx].sealed_branch(),
                        key: split_arg.get_pivot(),
                        depth: receipt.depth(),
                    },
                    split_arg,
                },
            ),
    {
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let read_nodes = access.loaded_branch_reads();
        let write_nodes = access.loaded_branch_writes();
        let pre_cached = pre.betree.wip_branches[idx];
        let pre_target = pre.wip_branch_i(idx);
        let branch = pre_target.sealed_branch();
        let path = BranchPath{
            branch,
            key: split_arg.get_pivot(),
            depth: receipt.depth(),
        };
        let expected = pre_target.branch_split(
            new_child_addr,
            path,
            split_arg,
        );
        let parent_addr = receipt.target().addr;
        let child_addr = receipt.child_addr();

        assert(allocs.is_empty());
        assert(deallocs.is_empty());
        assert(access.only_branch());
        assert(read_nodes == to_branch_nodes(reads));
        assert(write_nodes == to_branch_nodes(writes));
        assert(write_nodes == loaded_split_write_nodes(
            receipt,
            read_nodes,
            split_arg,
            new_child_addr,
        ));
        disk_access_without_alloc_or_dealloc(
            pre.disk,
            new_disk,
            guard_aus,
            reads,
            writes,
        );
        CachingDisk::State::access_visible_effect(
            pre.disk,
            new_disk,
            reads,
            writes,
        );

        assert(pre.i().wip_branches_inv());
        assert(pre_target == pre.i().wip_branches[idx]);
        assert(pre_target.inv());
        assert(pre_target.branch is Some);
        assert(!pre_target.is_sealed());
        assert(branch.inv());
        assert(branch.disk_view.entries
            <= to_branch_nodes(pre.disk.visible()));
        assert(receipt.root == branch.root);
        assert(pre_cached.mini_allocator.can_allocate(new_child_addr));
        assert(pre_target.addrs_closed_under_mini_allocator());
        assert(!branch.disk_view.entries.contains_key(new_child_addr)) by {
            if branch.disk_view.entries.contains_key(new_child_addr) {
                assert(pre_cached.mini_allocator.page_is_allocated(new_child_addr));
                assert(false);
            }
        };
        assert(branch.disk_view.is_fresh(set![new_child_addr]));
        receipt_path_valid_for_split(
            pre.disk,
            branch,
            branch.the_ranking(),
            reads,
            receipt,
            split_arg,
            new_child_addr,
        );
        assert(path.valid());
        assert(path.branch == branch);
        assert(pre_target.can_split(new_child_addr, path, split_arg));
        assert(reads.contains_key(child_addr));
        assert(branch.disk_view.entries.contains_key(child_addr));
        query_read_node_matches_visible(pre.disk, reads, child_addr);
        assert(read_nodes[child_addr]
            == branch.disk_view.entries[child_addr]);
        LinkedBranchRefinement::split_refines(
            branch,
            new_child_addr,
            path,
            split_arg,
        );

        let split_branch = branch.split(new_child_addr, path, split_arg);
        assert(write_nodes.contains_key(parent_addr));
        assert(write_nodes.contains_key(child_addr));
        assert(write_nodes.contains_key(new_child_addr));
        assert(writes.dom()
            == set![parent_addr, child_addr, new_child_addr]) by {
            assert(to_branch_nodes(writes).dom() == writes.dom());
        };
        assert(pre_cached.mini_allocator.page_is_allocated(parent_addr));
        assert(pre_cached.mini_allocator.page_is_allocated(child_addr));
        assert(mini_allocator_allocated_addrs(pre_cached.mini_allocator)
            .contains(parent_addr));
        assert(mini_allocator_allocated_addrs(pre_cached.mini_allocator)
            .contains(child_addr));
        mini_allocator_allocated_addrs_after_allocate(
            pre_cached.mini_allocator,
            new_child_addr,
        );
        assert(post_branch.mini_allocator
            == pre_cached.mini_allocator.allocate(new_child_addr));
        assert(mini_allocator_allocated_addrs(post_branch.mini_allocator)
            == mini_allocator_allocated_addrs(pre_cached.mini_allocator)
                + writes.dom());
        wip_entries_after_writes(
            pre.disk,
            new_disk,
            pre_cached.mini_allocator,
            post_branch.mini_allocator,
            reads,
            writes,
        );

        assert(split_branch.disk_view.entries[parent_addr]
            == write_nodes[parent_addr]);
        assert(split_branch.disk_view.entries[child_addr]
            == write_nodes[child_addr]);
        assert(split_branch.disk_view.entries[new_child_addr]
            == write_nodes[new_child_addr]);
        assert(split_branch.disk_view.entries.dom()
            == branch.disk_view.entries.dom().insert(new_child_addr));
        assert(split_branch.disk_view.entries
            == branch.disk_view.entries.union_prefer_right(write_nodes)) by {
            assert_maps_equal!(
                split_branch.disk_view.entries,
                branch.disk_view.entries.union_prefer_right(write_nodes),
                addr => {
                    if write_nodes.contains_key(addr) {
                        assert(addr == parent_addr || addr == child_addr
                            || addr == new_child_addr);
                    } else {
                        assert(addr != parent_addr && addr != child_addr
                            && addr != new_child_addr);
                        assert(split_branch.disk_view.entries.contains_key(addr)
                            == branch.disk_view.entries.contains_key(addr));
                        let except = set![
                            parent_addr,
                            child_addr,
                            new_child_addr,
                        ];
                        assert(!except.contains(addr));
                        assert(split_branch.disk_view.same_except(
                            branch.disk_view,
                            except,
                        ));
                        if split_branch.disk_view.entries.contains_key(addr)
                            || branch.disk_view.entries.contains_key(addr)
                        {
                            assert(split_branch.disk_view.entries.contains_key(addr));
                            assert(branch.disk_view.entries.contains_key(addr));
                            map_remove_keys_preserves_point(
                                split_branch.disk_view.entries,
                                except,
                                addr,
                            );
                            map_remove_keys_preserves_point(
                                branch.disk_view.entries,
                                except,
                                addr,
                            );
                            assert(split_branch.disk_view.entries.remove_keys(except)
                                == branch.disk_view.entries.remove_keys(except));
                            assert(split_branch.disk_view.entries[addr]
                                == branch.disk_view.entries[addr]);
                        }
                    }
                }
            );
        };
        assert(post.wip_branch_i(idx).is_sealed() == expected.is_sealed());
        assert(post.wip_branch_i(idx).mini_allocator
            == expected.mini_allocator);
        assert(post.wip_branch_i(idx).branch is Some);
        assert(post.wip_branch_i(idx).sealed_branch().root
            == split_branch.root);
        assert(post.wip_branch_i(idx).sealed_branch().disk_view.entries
            == split_branch.disk_view.entries);
        assert(post.wip_branch_i(idx) == expected);

        mini_allocator_allocate_preserves_all_aus(
            pre_cached.mini_allocator,
            new_child_addr,
        );
        assert(writes.dom() <= addresses_in_aus(
            pre_cached.mini_allocator.all_aus(),
        )) by {
            mini_allocator_allocated_addrs_subset_all_aus(
                pre_cached.mini_allocator,
            );
        };
        Self::branch_build_nonseal_preserves_shared_state(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::Split{
                new_child_addr,
                receipt,
                split_arg,
            },
            access,
        );
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().update(idx, expected),
            j => {
                if j == idx {
                    assert(post.wip_branch_i(j) == expected);
                } else {
                    assert(post.wip_branch_i(j) == pre.wip_branch_i(j));
                }
            }
        );
        AllocationBranchBetree::State::branch_build_delta_witness(
            pre.i(),
            idx,
            post.i().wip_branches[idx],
            BuildEvent::Split{
                addr: new_child_addr,
                path,
                split_arg,
            },
            allocs,
            deallocs,
        );
        Self::rooted_branch_build_preserves_staged_nodes(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::Split{
                new_child_addr,
                receipt,
                split_arg,
            },
            access,
        );
    }

    proof fn branch_seal_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
        aux_ptr: crate::disk::GenericDisk_v::Pointer,
        access: PageAccess,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            access == lbl.arrow_InternalAllocAccess_access(),
            CachedBranchBetree::State::branch_build(
                pre.betree,
                new_betree,
                lbl.cached_i(),
                idx,
                post_branch,
                BranchBuildEvent::Seal{aux_ptr}.cached_event(access),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            access.writes().dom() <= addresses_in_aus(
                pre.betree.wip_branches[idx].mini_allocator.all_aus(),
            ),
            AllocationBranchBetree::State::branch_build(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
                post.i().wip_branches[idx],
                BuildEvent::Seal{aux_ptr},
            ),
    {
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let reads = access.reads();
        let writes = access.writes();
        let read_nodes = access.loaded_branch_reads();
        let write_nodes = access.loaded_branch_writes();
        let pre_cached = pre.betree.wip_branches[idx];
        let pre_target = pre.wip_branch_i(idx);
        let branch = pre_target.sealed_branch();
        let root = branch.root;
        let expected = pre_target.branch_seal(aux_ptr, deallocs);
        let with_aux = if aux_ptr is Some {
            pre_cached.mini_allocator.allocate(aux_ptr.unwrap())
        } else {
            pre_cached.mini_allocator
        };

        assert(allocs.is_empty());
        assert(access.only_branch());
        assert(read_nodes == to_branch_nodes(reads));
        assert(write_nodes == to_branch_nodes(writes));
        assert(write_nodes == loaded_seal_write_nodes(
            pre_cached.branch.root.unwrap(),
            read_nodes,
            aux_ptr,
            pre_cached.mini_allocator.allocated_aus(),
        ));
        assert(pre_cached.branch.root == Some(root));
        assert(deallocs == pre_cached.mini_allocator.removable_aus());

        assert(pre.i().wip_branches_inv());
        assert(pre_target == pre.i().wip_branches[idx]);
        assert(pre_target.inv());
        assert(pre_target.branch is Some);
        assert(!pre_target.is_sealed());
        assert(branch.inv());
        assert(branch.disk_view.entries
            <= to_branch_nodes(pre.disk.visible()));
        let witness = disk_access_for_alloc_witness(
            pre.disk,
            new_disk,
            allocs,
            deallocs,
            guard_aus,
            reads,
            writes,
        );
        disk_extend_empty_is_identity(pre.disk, witness.expanded);
        assert(witness.expanded == pre.disk);
        assert(reads <= pre.disk.cache);
        assert(reads.contains_key(root));
        assert(branch.disk_view.entries.contains_key(root));
        query_read_node_matches_visible(pre.disk, reads, root);
        assert(read_nodes[root] == branch.root());
        assert(aux_ptr is Some <==> branch.root() is Index);

        if aux_ptr is Some {
            let ptr = aux_ptr.unwrap();
            assert(pre_cached.mini_allocator.can_allocate(ptr));
            assert(pre_cached.mini_allocator.allocated_aus().contains(ptr.au));
            assert(!deallocs.contains(ptr.au)) by {
                if deallocs.contains(ptr.au) {
                    assert(pre_cached.mini_allocator.can_remove(ptr.au));
                    assert(pre_cached.mini_allocator.allocs[ptr.au]
                        .has_no_allocated_pages());
                    assert(!pre_cached.mini_allocator.allocated_aus()
                        .contains(ptr.au));
                    assert(false);
                }
            };
        }
        assert(pre_target.can_seal(aux_ptr, deallocs));

        let pre_allocated = mini_allocator_allocated_addrs(
            pre_cached.mini_allocator,
        );
        let with_aux_allocated = mini_allocator_allocated_addrs(with_aux);
        if aux_ptr is Some {
            let ptr = aux_ptr.unwrap();
            mini_allocator_allocated_addrs_after_allocate(
                pre_cached.mini_allocator,
                ptr,
            );
            assert(writes.dom() == set![root, ptr]) by {
                assert(write_nodes.dom() == set![root, ptr]);
                assert(to_branch_nodes(writes).dom() == writes.dom());
            };
            assert(pre_allocated.contains(root));
            assert(with_aux_allocated == pre_allocated + writes.dom());
        } else {
            assert(write_nodes.is_empty());
            assert(writes.is_empty());
            assert(with_aux_allocated == pre_allocated + writes.dom());
        }
        wip_entries_after_writes(
            pre.disk,
            witness.accessed,
            pre_cached.mini_allocator,
            with_aux,
            reads,
            writes,
        );

        assert(pre_allocated.disjoint(addresses_in_aus(deallocs))) by {
            assert forall |addr: Address| #[trigger] pre_allocated.contains(addr)
                implies !addresses_in_aus(deallocs).contains(addr)
            by {
                if addresses_in_aus(deallocs).contains(addr) {
                    assert(deallocs.contains(addr.au));
                    assert(pre_cached.mini_allocator.can_remove(addr.au));
                    assert(pre_cached.mini_allocator.allocs[addr.au]
                        .has_no_allocated_pages());
                    assert(pre_cached.mini_allocator.allocs[addr.au]
                        .allocated.contains(addr));
                    assert(false);
                }
            };
        };
        assert(with_aux_allocated.disjoint(addresses_in_aus(deallocs))) by {
            if aux_ptr is Some {
                let ptr = aux_ptr.unwrap();
                assert(with_aux_allocated == pre_allocated.insert(ptr));
                assert(!deallocs.contains(ptr.au));
            }
        };
        mini_allocator_allocated_addrs_after_prune(with_aux, deallocs);
        assert(post_branch.mini_allocator == with_aux.prune(deallocs));
        let post_allocated = mini_allocator_allocated_addrs(
            post_branch.mini_allocator,
        );
        assert(post_allocated == with_aux_allocated);
        assert(post_allocated.disjoint(addresses_in_aus(
            deallocs - guard_aus,
        )));
        disk_forget_visible_outside_aus(
            witness.accessed,
            new_disk,
            deallocs - guard_aus,
            post_allocated,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            witness.accessed.visible(),
            post_allocated,
        );
        assert(to_branch_nodes(new_disk.visible()).restrict(post_allocated)
            == to_branch_nodes(pre.disk.visible()).restrict(pre_allocated)
                .union_prefer_right(write_nodes));

        let concrete_sealed = LinkedBranch {
            root,
            disk_view: BranchDiskView {
                entries: branch.disk_view.entries.union_prefer_right(write_nodes),
            },
        };
        if aux_ptr is Some {
            let ptr = aux_ptr.unwrap();
            assert(write_nodes[root] == BranchNode::Index{
                pivots: branch.root()->pivots,
                children: branch.root()->children,
                aux_ptr,
            });
            assert(write_nodes[ptr] == BranchNode::Auxiliary(
                pre_cached.mini_allocator.allocated_aus(),
            ));
            assert(concrete_sealed == branch.seal(
                ptr,
                pre_cached.mini_allocator.allocated_aus(),
            )) by {
                assert_maps_equal!(
                    concrete_sealed.disk_view.entries,
                    branch.seal(
                        ptr,
                        pre_cached.mini_allocator.allocated_aus(),
                    ).disk_view.entries,
                    addr => {
                        if write_nodes.contains_key(addr) {
                            assert(addr == root || addr == ptr);
                        }
                        if branch.seal(
                            ptr,
                            pre_cached.mini_allocator.allocated_aus(),
                        ).disk_view.entries.contains_key(addr)
                            && (addr == root || addr == ptr)
                        {
                            assert(write_nodes.contains_key(addr));
                        }
                    }
                );
            };
        } else {
            assert(write_nodes.is_empty());
            assert(concrete_sealed == branch);
        }
        assert(expected.branch == Some(concrete_sealed));
        assert(post.wip_branch_i(idx).is_sealed() == expected.is_sealed());
        assert(post.wip_branch_i(idx).mini_allocator
            == expected.mini_allocator);
        assert(post.wip_branch_i(idx).branch is Some);
        assert(post.wip_branch_i(idx).sealed_branch().root
            == concrete_sealed.root);
        assert(post.wip_branch_i(idx).sealed_branch().disk_view.entries
            == concrete_sealed.disk_view.entries);
        assert(post.wip_branch_i(idx) == expected);

        pre.wip_alloc_aus_agree();
        AllocationBulkBranch::alloc_aus_ensures(pre.i().wip_branches, idx);
        let selected_aus = pre_cached.mini_allocator.all_aus();
        assert(selected_aus <= pre.i().branch_allocator_aus());
        assert(deallocs <= selected_aus);
        if aux_ptr is Some {
            mini_allocator_allocate_preserves_all_aus(
                pre_cached.mini_allocator,
                aux_ptr.unwrap(),
            );
        }
        assert(writes.dom() <= addresses_in_aus(selected_aus)) by {
            mini_allocator_allocated_addrs_subset_all_aus(
                pre_cached.mini_allocator,
            );
        };
        let betree_addrs = addresses_in_aus(pre.betree.betree_aus.dom());
        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );
        assert(pre.i().betree_aus.dom().disjoint(selected_aus));
        assert(summary_aus(pre.i().branch_summary).disjoint(selected_aus));
        addresses_in_aus_preserves_disjointness(
            pre.betree.betree_aus.dom(),
            selected_aus,
        );
        addresses_in_aus_preserves_disjointness(
            summary_aus(pre.betree.branch_summary),
            selected_aus,
        );
        assert(betree_addrs.disjoint(writes.dom()));
        assert(sealed_addrs.disjoint(writes.dom()));
        assert(betree_addrs.disjoint(addresses_in_aus(deallocs)));
        assert(sealed_addrs.disjoint(addresses_in_aus(deallocs)));
        disk_access_empty_alloc_visible_stable(
            pre.disk,
            new_disk,
            deallocs,
            guard_aus,
            reads,
            writes,
            betree_addrs,
        );
        disk_access_empty_alloc_visible_stable(
            pre.disk,
            new_disk,
            deallocs,
            guard_aus,
            reads,
            writes,
            sealed_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            betree_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            sealed_addrs,
        );
        assert(post.visible_betree_entries() == pre.visible_betree_entries());
        assert(post.visible_sealed_branch_entries()
            == pre.visible_sealed_branch_entries());
        assert(post.linked_i() == pre.linked_i());

        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().update(idx, expected),
            j => {
                if j == idx {
                    assert(post.wip_branch_i(j) == expected);
                } else {
                    assert(post.betree.wip_branches[j]
                        == pre.betree.wip_branches[j]);
                    let cached = pre.betree.wip_branches[j];
                    let stable = mini_allocator_allocated_addrs(
                        cached.mini_allocator,
                    );
                    assert(pre.i().wip_branches_disjoint());
                    assert(pre.i().wip_branches[j].mini_allocator
                        == cached.mini_allocator);
                    assert(pre.i().wip_branches[idx].mini_allocator
                        == pre_cached.mini_allocator);
                    assert(cached.mini_allocator.all_aus()
                        .disjoint(selected_aus));
                    mini_allocator_allocated_addrs_subset_all_aus(
                        cached.mini_allocator,
                    );
                    addresses_in_aus_preserves_disjointness(
                        cached.mini_allocator.all_aus(),
                        selected_aus,
                    );
                    assert(stable.disjoint(writes.dom()));
                    assert(stable.disjoint(addresses_in_aus(deallocs)));
                    disk_access_empty_alloc_visible_stable(
                        pre.disk,
                        new_disk,
                        deallocs,
                        guard_aus,
                        reads,
                        writes,
                        stable,
                    );
                    to_branch_nodes_restrict_agrees(
                        new_disk.visible(),
                        pre.disk.visible(),
                        stable,
                    );
                }
            }
        );
        AllocationBranchBetree::State::branch_build_delta_witness(
            pre.i(),
            idx,
            post.i().wip_branches[idx],
            BuildEvent::Seal{aux_ptr},
            allocs,
            deallocs,
        );
        Self::rooted_branch_build_preserves_staged_nodes(
            pre,
            post,
            lbl,
            new_betree,
            new_disk,
            idx,
            post_branch,
            BranchBuildEvent::Seal{aux_ptr},
            access,
        );
    }

    */

    proof fn branch_begin_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, post.disk,
            ),
            CachedBranchBetree::State::branch_begin(
                pre.betree, new_betree, lbl.cached_i(),
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::branch_begin(
                pre.i(),
                post.i(),
                lbl.i(pre),
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, post.disk,
        );
        let effect_access = lbl.arrow_InternalAllocAccess_access();
        effect_access.cached_empty_is_empty();
        assert(lbl.arrow_InternalAllocAccess_allocs().is_empty());
        assert(lbl.arrow_InternalAllocAccess_deallocs().is_empty());
        assert(effect_access.reads() == Map::<Address, RawPage>::empty());
        assert(effect_access.writes() == Map::<Address, RawPage>::empty());
        disk_access_empty_effect_is_extension(
            pre.disk,
            post.disk,
            lbl.arrow_InternalAllocAccess_allocs(),
            lbl.arrow_InternalAllocAccess_guard_aus(),
        );
        disk_extend_empty_is_identity(pre.disk, post.disk);

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        pre.wip_alloc_aus_agree();
        assert(pre.i().branch_allocator_aus()
            == cached_bulk_branch_alloc_aus(pre.betree.wip_branches));
        assert(pre.i().is_fresh(allocs));
        assert(post.disk == pre.disk);

        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().push(AllocationBulkBranch::new(allocs)),
            idx => {
                if idx < pre.betree.wip_branches.len() {
                    assert(post.betree.wip_branches[idx]
                        == pre.betree.wip_branches[idx]);
                } else {
                    assert(idx == pre.betree.wip_branches.len());
                    assert(post.betree.wip_branches[idx]
                        == CachedBulkBranch::new(allocs));
                }
            }
        );
        assert(post.staged_nodes_inv()) by {
            assert forall |idx: int|
                0 <= idx < post.betree.wip_branches.len()
                && post.betree.wip_branches[idx].is_building()
                implies #[trigger]
                    post.betree.wip_branches[idx].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[idx]
                                    .mini_allocator,
                            ),
                        ) by {
                if idx < pre.betree.wip_branches.len() {
                    assert(post.betree.wip_branches[idx]
                        == pre.betree.wip_branches[idx]);
                    assert(pre.betree.wip_branches[idx].is_building());
                    assert(pre.betree.wip_branches[idx].staged_nodes()
                        == to_branch_nodes(pre.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                pre.betree.wip_branches[idx]
                                    .mini_allocator,
                            ),
                        ));
                } else {
                    assert(idx == pre.betree.wip_branches.len());
                    assert(post.betree.wip_branches[idx]
                        == CachedBulkBranch::new(allocs));
                    empty_mini_allocator_has_no_allocated_addrs(allocs);
                }
            }
        }
        assert(post.sealed_wip_nodes_inv());
        assert(post.compactor_receipts_inv());
    }

    proof fn branch_fill_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
        post_branch: CachedBulkBranch,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            CachedBranchBetree::State::branch_fill(
                pre.betree, new_betree, lbl.cached_i(),
                idx,
                post_branch,
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::branch_fill(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
                post.i().wip_branches[idx],
                lbl.arrow_InternalAllocAccess_allocs(),
                lbl.arrow_InternalAllocAccess_deallocs(),
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        let effect_access = lbl.arrow_InternalAllocAccess_access();
        effect_access.cached_empty_is_empty();
        assert(lbl.arrow_InternalAllocAccess_deallocs().is_empty());
        assert(effect_access.reads() == Map::<Address, RawPage>::empty());
        assert(effect_access.writes() == Map::<Address, RawPage>::empty());
        disk_access_empty_effect_is_extension(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAllocAccess_allocs(),
            lbl.arrow_InternalAllocAccess_guard_aus(),
        );

        let allocs = lbl.arrow_InternalAllocAccess_allocs();
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let pre_cached = pre.betree.wip_branches[idx];
        let pre_branch = pre.wip_branch_i(idx);
        pre.wip_alloc_aus_agree();
        assert(pre.i().is_fresh(allocs));
        assert(pre.i().wip_branches_inv());
        assert(pre.i().wip_branches[idx].inv());
        assert(pre_branch == pre.i().wip_branches[idx]);
        assert(pre_branch.mini_allocator.wf());
        let betree_addrs = addresses_in_aus(pre.betree.betree_aus.dom());
        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );
        addresses_in_aus_preserves_disjointness(
            allocs,
            pre.betree.betree_aus.dom(),
        );
        addresses_in_aus_preserves_disjointness(
            allocs,
            summary_aus(pre.betree.branch_summary),
        );
        disk_extend_visible_outside_allocs(
            pre.disk,
            new_disk,
            allocs,
            betree_addrs,
        );
        disk_extend_visible_outside_allocs(
            pre.disk,
            new_disk,
            allocs,
            sealed_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            betree_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            sealed_addrs,
        );
        assert(post.visible_betree_entries() == pre.visible_betree_entries());
        assert(post.visible_sealed_branch_entries()
            == pre.visible_sealed_branch_entries());
        assert(post.linked_i() == pre.linked_i());
        mini_allocator_add_aus_preserves_allocated_addrs(
            pre_cached.mini_allocator,
            allocs,
        );
        assert(post.disk == new_disk);
        assert(post_branch == pre_cached.fill_aus(allocs));
        let pre_allocated = mini_allocator_allocated_addrs(pre_cached.mini_allocator);
        mini_allocator_allocated_addrs_subset_all_aus(pre_cached.mini_allocator);
        addresses_in_aus_preserves_disjointness(
            allocs,
            pre_cached.mini_allocator.all_aus(),
        );
        disk_extend_visible_outside_allocs(
            pre.disk,
            new_disk,
            allocs,
            pre_allocated,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            pre_allocated,
        );
        assert(post.wip_branch_i(idx)
            == pre_branch.fill_aus(allocs));

        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().update(idx, post.wip_branch_i(idx)),
            j => {
                if j == idx {
                    assert(post.betree.wip_branches[j] == post_branch);
                } else {
                    assert(post.betree.wip_branches[j]
                        == pre.betree.wip_branches[j]);
                    let cached = pre.betree.wip_branches[j];
                    let allocated = mini_allocator_allocated_addrs(cached.mini_allocator);
                    AllocationBulkBranch::alloc_aus_ensures(pre.i().wip_branches, j);
                    mini_allocator_allocated_addrs_subset_all_aus(cached.mini_allocator);
                    assert(cached.mini_allocator.all_aus()
                        <= pre.i().branch_allocator_aus());
                    assert(allocs.disjoint(cached.mini_allocator.all_aus()));
                    addresses_in_aus_preserves_disjointness(
                        allocs,
                        cached.mini_allocator.all_aus(),
                    );
                    disk_extend_visible_outside_allocs(
                        pre.disk,
                        new_disk,
                        allocs,
                        allocated,
                    );
                    to_branch_nodes_restrict_agrees(
                        new_disk.visible(),
                        pre.disk.visible(),
                        allocated,
                    );
                }
            }
        );
        assert(post.staged_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_building()
                implies #[trigger]
                    post.betree.wip_branches[j].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[j]
                                    .mini_allocator,
                            ),
                        ) by {
                let source = pre.betree.wip_branches[j];
                let target = post.betree.wip_branches[j];
                let allocated = mini_allocator_allocated_addrs(
                    source.mini_allocator,
                );
                assert(source.is_building());
                assert(source.staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        allocated,
                    ));
                if j == idx {
                    assert(target == source.fill_aus(allocs));
                    mini_allocator_add_aus_preserves_allocated_addrs(
                        source.mini_allocator,
                        allocs,
                    );
                    assert(mini_allocator_allocated_addrs(
                        target.mini_allocator,
                    ) == allocated);
                } else {
                    assert(target == source);
                    mini_allocator_allocated_addrs_subset_all_aus(
                        source.mini_allocator,
                    );
                    AllocationBulkBranch::alloc_aus_ensures(
                        pre.i().wip_branches,
                        j,
                    );
                    assert(source.mini_allocator.all_aus()
                        <= pre.i().branch_allocator_aus());
                    assert(allocs.disjoint(
                        source.mini_allocator.all_aus(),
                    ));
                    addresses_in_aus_preserves_disjointness(
                        allocs,
                        source.mini_allocator.all_aus(),
                    );
                    disk_extend_visible_outside_allocs(
                        pre.disk,
                        new_disk,
                        allocs,
                        allocated,
                    );
                    to_branch_nodes_restrict_agrees(
                        new_disk.visible(),
                        pre.disk.visible(),
                        allocated,
                    );
                }
                transfer_staged_nodes_alignment(
                    pre.disk,
                    new_disk,
                    source,
                    target,
                );
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[j].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[j]
                                .mini_allocator,
                        ),
                    ) by {
                let source = pre.betree.wip_branches[j];
                let allocated = mini_allocator_allocated_addrs(
                    source.mini_allocator,
                );
                assert(j != idx);
                assert(post.betree.wip_branches[j] == source);
                assert(source.is_sealed());
                assert(source.sealed_branch().disk_view.entries
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        allocated,
                    ));
                mini_allocator_allocated_addrs_subset_all_aus(
                    source.mini_allocator,
                );
                AllocationBulkBranch::alloc_aus_ensures(
                    pre.i().wip_branches,
                    j,
                );
                assert(source.mini_allocator.all_aus()
                    <= pre.i().branch_allocator_aus());
                assert(allocs.disjoint(
                    source.mini_allocator.all_aus(),
                ));
                addresses_in_aus_preserves_disjointness(
                    allocs,
                    source.mini_allocator.all_aus(),
                );
                disk_extend_visible_outside_allocs(
                    pre.disk,
                    new_disk,
                    allocs,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        }
        Self::unchanged_compactor_receipts_preserve_inv(pre, post);
    }

    proof fn branch_abort_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
        new_betree: CachedBranchBetree::State,
        new_disk: CachingDisk::State,
        idx: int,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::internal_alloc_access(
                pre, post, lbl, new_betree, new_disk,
            ),
            CachedBranchBetree::State::branch_abort(
                pre.betree, new_betree, lbl.cached_i(),
                idx,
            ),
        ensures
            post.semantic_selector_inv(),
            post.staged_nodes_inv(),
            post.sealed_wip_nodes_inv(),
            post.compactor_receipts_inv(),
            AllocationBranchBetree::State::branch_abort(
                pre.i(),
                post.i(),
                lbl.i(pre),
                idx,
            ),
    {
        CachingDiskBranchBetree::State::internal_alloc_access_effect(
            pre, post, lbl, new_betree, new_disk,
        );
        let effect_access = lbl.arrow_InternalAllocAccess_access();
        effect_access.cached_empty_is_empty();
        assert(lbl.arrow_InternalAllocAccess_allocs().is_empty());
        assert(effect_access.reads() == Map::<Address, RawPage>::empty());
        assert(effect_access.writes() == Map::<Address, RawPage>::empty());
        disk_access_empty_alloc_access_is_forget(
            pre.disk,
            new_disk,
            lbl.arrow_InternalAllocAccess_deallocs(),
            lbl.arrow_InternalAllocAccess_guard_aus(),
        );

        assert(post.disk == new_disk);
        let deallocs = lbl.arrow_InternalAllocAccess_deallocs();
        let guard_aus = lbl.arrow_InternalAllocAccess_guard_aus();
        let forgotten_aus = deallocs - guard_aus;
        let betree_addrs = addresses_in_aus(pre.betree.betree_aus.dom());
        let sealed_addrs = addresses_in_aus(
            summary_aus(pre.betree.branch_summary),
        );
        AllocationBulkBranch::alloc_aus_ensures(pre.i().wip_branches, idx);
        assert(deallocs == pre.i().wip_branches[idx].mini_allocator.all_aus());
        assert(deallocs <= pre.i().branch_allocator_aus());
        assert(pre.i().betree_aus.dom().disjoint(deallocs));
        assert(summary_aus(pre.i().branch_summary).disjoint(deallocs));
        assert(forgotten_aus.disjoint(pre.betree.betree_aus.dom()));
        assert(forgotten_aus.disjoint(
            summary_aus(pre.betree.branch_summary),
        ));
        addresses_in_aus_preserves_disjointness(
            forgotten_aus,
            pre.betree.betree_aus.dom(),
        );
        addresses_in_aus_preserves_disjointness(
            forgotten_aus,
            summary_aus(pre.betree.branch_summary),
        );
        disk_forget_visible_outside_aus(
            pre.disk,
            new_disk,
            forgotten_aus,
            betree_addrs,
        );
        disk_forget_visible_outside_aus(
            pre.disk,
            new_disk,
            forgotten_aus,
            sealed_addrs,
        );
        to_betree_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            betree_addrs,
        );
        to_branch_nodes_restrict_agrees(
            new_disk.visible(),
            pre.disk.visible(),
            sealed_addrs,
        );
        assert(post.visible_betree_entries() == pre.visible_betree_entries());
        assert(post.visible_sealed_branch_entries()
            == pre.visible_sealed_branch_entries());
        assert(post.linked_i() == pre.linked_i());
        assert_seqs_equal!(
            post.wip_branches_i(),
            pre.wip_branches_i().remove(idx),
            j => {
                let pre_idx = if j < idx { j } else { j + 1 };
                assert(post.betree.wip_branches[j]
                    == pre.betree.wip_branches[pre_idx]);
                let cached = pre.betree.wip_branches[pre_idx];
                let allocated = mini_allocator_allocated_addrs(cached.mini_allocator);
                mini_allocator_allocated_addrs_subset_all_aus(cached.mini_allocator);
                assert(pre.i().wip_branches_disjoint());
                assert(pre_idx != idx);
                assert(pre.i().wip_branches[pre_idx].mini_allocator.all_aus()
                    .disjoint(pre.i().wip_branches[idx].mini_allocator.all_aus()));
                assert(cached.mini_allocator.all_aus().disjoint(deallocs));
                assert(cached.mini_allocator.all_aus().disjoint(
                    forgotten_aus,
                ));
                addresses_in_aus_preserves_disjointness(
                    forgotten_aus,
                    cached.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk,
                    new_disk,
                    forgotten_aus,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        );
        assert(post.staged_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_building()
                implies #[trigger]
                    post.betree.wip_branches[j].staged_nodes()
                        == to_branch_nodes(post.disk.visible()).restrict(
                            mini_allocator_allocated_addrs(
                                post.betree.wip_branches[j]
                                    .mini_allocator,
                            ),
                        ) by {
                let pre_idx = if j < idx { j } else { j + 1 };
                let source = pre.betree.wip_branches[pre_idx];
                let target = post.betree.wip_branches[j];
                let allocated = mini_allocator_allocated_addrs(
                    source.mini_allocator,
                );
                assert(target == source);
                assert(source.is_building());
                assert(source.staged_nodes()
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        allocated,
                    ));
                mini_allocator_allocated_addrs_subset_all_aus(
                    source.mini_allocator,
                );
                assert(pre.i().wip_branches_disjoint());
                assert(pre_idx != idx);
                assert(pre.i().wip_branches[pre_idx]
                    .mini_allocator.all_aus().disjoint(
                        pre.i().wip_branches[idx]
                            .mini_allocator.all_aus(),
                    ));
                assert(source.mini_allocator.all_aus()
                    .disjoint(forgotten_aus));
                addresses_in_aus_preserves_disjointness(
                    forgotten_aus,
                    source.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk,
                    new_disk,
                    forgotten_aus,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
                transfer_staged_nodes_alignment(
                    pre.disk,
                    new_disk,
                    source,
                    target,
                );
            }
        }
        assert(post.sealed_wip_nodes_inv()) by {
            assert forall |j: int|
                0 <= j < post.betree.wip_branches.len()
                && post.betree.wip_branches[j].is_sealed()
                implies #[trigger]
                    post.betree.wip_branches[j].sealed_branch()
                        .disk_view.entries
                    == to_branch_nodes(post.disk.visible()).restrict(
                        mini_allocator_allocated_addrs(
                            post.betree.wip_branches[j]
                                .mini_allocator,
                        ),
                    ) by {
                let pre_idx = if j < idx { j } else { j + 1 };
                let source = pre.betree.wip_branches[pre_idx];
                let allocated = mini_allocator_allocated_addrs(
                    source.mini_allocator,
                );
                assert(post.betree.wip_branches[j] == source);
                assert(source.is_sealed());
                assert(source.sealed_branch().disk_view.entries
                    == to_branch_nodes(pre.disk.visible()).restrict(
                        allocated,
                    ));
                mini_allocator_allocated_addrs_subset_all_aus(
                    source.mini_allocator,
                );
                assert(pre.i().wip_branches_disjoint());
                assert(pre_idx != idx);
                assert(pre.i().wip_branches[pre_idx]
                    .mini_allocator == source.mini_allocator);
                assert(pre.i().wip_branches[idx]
                    .mini_allocator.all_aus() == deallocs);
                assert(pre.i().wip_branches[pre_idx]
                    .mini_allocator.all_aus().disjoint(
                        pre.i().wip_branches[idx]
                            .mini_allocator.all_aus(),
                    ));
                assert(source.mini_allocator.all_aus()
                    .disjoint(deallocs));
                addresses_in_aus_preserves_disjointness(
                    forgotten_aus,
                    source.mini_allocator.all_aus(),
                );
                disk_forget_visible_outside_aus(
                    pre.disk,
                    new_disk,
                    forgotten_aus,
                    allocated,
                );
                to_branch_nodes_restrict_agrees(
                    new_disk.visible(),
                    pre.disk.visible(),
                    allocated,
                );
            }
        }
        Self::unchanged_compactor_receipts_preserve_inv(pre, post);
    }

    pub proof fn next_refines(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranchBetree::Label,
    )
        requires
            pre.refinement_inv(),
            CachingDiskBranchBetree::State::next(pre, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationBranchBetree::State::next(
                pre.i(),
                post.i(),
                lbl.i(pre),
            ),
    {
        reveal(CachingDiskBranchBetree::State::next);
        reveal(CachingDiskBranchBetree::State::next_by);
        reveal(AllocationBranchBetree::State::next);
        reveal(AllocationBranchBetree::State::next_by);

        let step = choose |step: CachingDiskBranchBetree::Step|
            CachingDiskBranchBetree::State::next_by(
                pre,
                post,
                lbl,
                step,
            );
        match step {
            CachingDiskBranchBetree::Step::disk_internal(new_disk) => {
                Self::disk_internal_stutters(pre, post, lbl, new_disk);
                assert(post.staged_nodes_inv());
                assert(post.sealed_wip_nodes_inv());
                assert(post.compactor_receipts_inv());
                assert(AllocationBranchBetree::State::next_by(
                    pre.i(),
                    post.i(),
                    lbl.i(pre),
                    AllocationBranchBetree::Step::internal_noop(),
                ));
            }
            CachingDiskBranchBetree::Step::query() => {
                let access = lbl.arrow_Query_access();
                reveal(CachedBranchBetree::State::next);
                reveal(CachedBranchBetree::State::next_by);
                let cached_step = choose |cached_step: CachedBranchBetree::Step|
                    CachedBranchBetree::State::next_by(
                        pre.betree,
                        post.betree,
                        lbl.cached_i(),
                        cached_step,
                    );
                match cached_step {
                    CachedBranchBetree::Step::query(receipt, ..) => {
                        Self::query_refines(pre, post, lbl, receipt, access);
                    }
                    _ => { assert(false); },
                }
                assert(post.staged_nodes_inv());
                assert(post.sealed_wip_nodes_inv());
                assert(post.compactor_receipts_inv());
                assert(AllocationBranchBetree::State::next_by(
                    pre.i(),
                    post.i(),
                    lbl.i(pre),
                    AllocationBranchBetree::Step::au_likes_noop(
                        post.i().betree,
                    ),
                ));
            }
            CachingDiskBranchBetree::Step::put(new_betree) => {
                Self::put_refines(pre, post, lbl, new_betree);
                assert(post.staged_nodes_inv());
                assert(post.sealed_wip_nodes_inv());
                assert(post.compactor_receipts_inv());
                assert(AllocationBranchBetree::State::next_by(
                    pre.i(),
                    post.i(),
                    lbl.i(pre),
                    AllocationBranchBetree::Step::au_likes_noop(
                        post.i().betree,
                    ),
                ));
            }
            CachingDiskBranchBetree::Step::freeze_as() => {
                Self::freeze_as_refines(pre, post, lbl);
                assert(post.staged_nodes_inv());
                assert(post.sealed_wip_nodes_inv());
                assert(post.compactor_receipts_inv());
                assert(AllocationBranchBetree::State::next_by(
                    pre.i(),
                    post.i(),
                    lbl.i(pre),
                    AllocationBranchBetree::Step::au_likes_noop(
                        post.i().betree,
                    ),
                ));
            }
            CachingDiskBranchBetree::Step::internal_access(
                new_betree, new_disk,
            ) => {
                let access = lbl.arrow_InternalAccess_access();
                Self::next_refines_cached(pre, post, lbl);
                reveal(CachedBranchBetree::State::next);
                reveal(CachedBranchBetree::State::next_by);
                let cached_step = choose |cached_step: CachedBranchBetree::Step|
                    CachedBranchBetree::State::next_by(
                        pre.betree, new_betree, lbl.cached_i(), cached_step,
                    );
                match cached_step {
                    CachedBranchBetree::Step::compact_begin(
                        path, start, end, ..
                    ) => {
                        Self::compact_begin_refines(
                            pre, post, lbl, new_betree,
                            path, start, end, access,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(),
                            post.i(),
                            lbl.i(pre),
                            AllocationBranchBetree::Step::internal_compact_begin(
                                Path {
                                    linked: pre.linked_i(),
                                    key: path.key,
                                    depth: path.depth(),
                                },
                                start,
                                end,
                                post.i().compactors.last(),
                            ),
                        ));
                    }
                    CachedBranchBetree::Step::compact_scan_page(
                        input_idx, ..
                    ) => {
                        Self::compact_scan_page_refines(
                            pre, post, lbl, new_betree, input_idx, access,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(),
                            post.i(),
                            lbl.i(pre),
                            AllocationBranchBetree::Step::internal_noop(),
                        ));
                    }
                    _ => { assert(false); }
                }
            }
            CachingDiskBranchBetree::Step::internal_alloc_access(
                new_betree, new_disk,
            ) => {
                let access = lbl.arrow_InternalAllocAccess_access();
                Self::next_refines_cached(pre, post, lbl);
                reveal(CachedBranchBetree::State::next);
                reveal(CachedBranchBetree::State::next_by);
                let cached_step = choose |cached_step: CachedBranchBetree::Step|
                    CachedBranchBetree::State::next_by(
                        pre.betree, new_betree, lbl.cached_i(), cached_step,
                    );
                match cached_step {
                    CachedBranchBetree::Step::branch_begin() => {
                        Self::branch_begin_refines(pre, post, lbl, new_betree);
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::branch_begin(),
                        ));
                    }
                    CachedBranchBetree::Step::branch_fill(
                        idx, post_branch,
                    ) => {
                        Self::branch_fill_refines(
                            pre, post, lbl, new_betree, new_disk,
                            idx, post_branch,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::branch_fill(
                                idx,
                                post.i().wip_branches[idx],
                                lbl.arrow_InternalAllocAccess_allocs(),
                                lbl.arrow_InternalAllocAccess_deallocs(),
                            ),
                        ));
                    }
                    CachedBranchBetree::Step::branch_build(
                        idx, post_branch, event,
                    ) => {
                        match event {
                            CachedBulkBranchEvent::StagePage{addr, ..} => {
                                Self::branch_stage_page_refines(
                                    pre, post, lbl, new_betree, new_disk,
                                    idx, post_branch, addr, access,
                                );
                                assert(AllocationBranchBetree::State::next_by(
                                    pre.i(), post.i(), lbl.i(pre),
                                    AllocationBranchBetree::Step::branch_build(
                                        idx,
                                        post.i().wip_branches[idx],
                                        BulkBranchEvent::StagePage{addr},
                                        lbl.arrow_InternalAllocAccess_allocs(),
                                        lbl.arrow_InternalAllocAccess_deallocs(),
                                    ),
                                ));
                            }
                            CachedBulkBranchEvent::BulkSeal{
                                root, aux_ptr, ..
                            } => {
                                Self::branch_bulk_seal_refines(
                                    pre, post, lbl, new_betree, new_disk,
                                    idx, post_branch, root, aux_ptr, access,
                                );
                                assert(AllocationBranchBetree::State::next_by(
                                    pre.i(), post.i(), lbl.i(pre),
                                    AllocationBranchBetree::Step::branch_build(
                                        idx,
                                        post.i().wip_branches[idx],
                                        BulkBranchEvent::BulkSeal {
                                            root,
                                            aux_ptr,
                                            branch: post.i().wip_branches[idx]
                                                .sealed_branch(),
                                        },
                                        lbl.arrow_InternalAllocAccess_allocs(),
                                        lbl.arrow_InternalAllocAccess_deallocs(),
                                    ),
                                ));
                            }
                        }
                    }
                    CachedBranchBetree::Step::branch_abort(idx) => {
                        Self::branch_abort_refines(
                            pre, post, lbl, new_betree, new_disk, idx,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::branch_abort(idx),
                        ));
                    }
                    CachedBranchBetree::Step::flush_memtable(
                        branch_idx, new_root_addr, ..
                    ) => {
                        Self::flush_memtable_refines(
                            pre, post, lbl, new_betree, new_disk,
                            branch_idx, new_root_addr, access,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::internal_flush_memtable(
                                post.i().betree, branch_idx, new_root_addr,
                            ),
                        ));
                    }
                    CachedBranchBetree::Step::grow(new_root_addr, ..) => {
                        Self::grow_refines(
                            pre, post, lbl, new_betree, new_disk,
                            new_root_addr, access,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::internal_grow(
                                post.i().betree, new_root_addr,
                            ),
                        ));
                    }
                    CachedBranchBetree::Step::split(
                        path, request, new_addrs, path_addrs, ..
                    ) => {
                        Self::split_refines(
                            pre, post, lbl, new_betree, new_disk, path, request,
                            new_addrs, path_addrs, access,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::internal_split(
                                post.i().betree,
                                Path {
                                    linked: pre.linked_i(),
                                    key: path.key,
                                    depth: path.depth(),
                                },
                                request, new_addrs, path_addrs,
                            ),
                        ));
                    }
                    CachedBranchBetree::Step::flush(
                        path, child_idx, buffer_gc, new_addrs, path_addrs, ..
                    ) => {
                        Self::flush_refines(
                            pre, post, lbl, new_betree, new_disk, path, child_idx,
                            buffer_gc, new_addrs, path_addrs, access,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::internal_flush(
                                post.i().betree,
                                Path {
                                    linked: pre.linked_i(),
                                    key: path.key,
                                    depth: path.depth(),
                                },
                                child_idx, buffer_gc, new_addrs, path_addrs,
                            ),
                        ));
                    }
                    CachedBranchBetree::Step::compact_abort(input_idx) => {
                        Self::compact_abort_refines(
                            pre, post, lbl, new_betree, new_disk, input_idx,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::internal_compact_abort(
                                input_idx, post.i().betree,
                            ),
                        ));
                    }
                    CachedBranchBetree::Step::compact_complete(
                        input_idx, branch_idx, path, start, end,
                        new_node_addr, path_addrs, ..
                    ) => {
                        let linked_path = Path {
                            linked: pre.linked_i(),
                            key: path.key,
                            depth: path.depth(),
                        };
                        Self::compact_complete_refines(
                            pre, post, lbl, new_betree, new_disk, input_idx,
                            branch_idx, path, start, end, new_node_addr,
                            path_addrs, access,
                        );
                        assert(AllocationBranchBetree::State::next_by(
                            pre.i(), post.i(), lbl.i(pre),
                            AllocationBranchBetree::Step::internal_compact_complete(
                                post.i().betree, linked_path, start, end, input_idx,
                                branch_idx, new_node_addr, path_addrs,
                            ),
                        ));
                    }
                    _ => { assert(false); }
                }
                assert(post.staged_nodes_inv());
                assert(post.sealed_wip_nodes_inv());
                assert(post.compactor_receipts_inv());
            }
            CachingDiskBranchBetree::Step::internal_noop() => {
                Self::internal_noop_stutters(pre, post, lbl);
                assert(post.staged_nodes_inv());
                assert(post.sealed_wip_nodes_inv());
                assert(post.compactor_receipts_inv());
                assert(AllocationBranchBetree::State::next_by(
                    pre.i(),
                    post.i(),
                    lbl.i(pre),
                    AllocationBranchBetree::Step::internal_noop(),
                ));
            }
            _ => {
                assert(false);
            }
        }
        assert(post.staged_nodes_inv());
        assert(post.sealed_wip_nodes_inv());
        assert(post.compactor_receipts_inv());
        assert(AllocationBranchBetree::State::next(
            pre.i(),
            post.i(),
            lbl.i(pre),
        ));
        CachingDiskBranchBetree::State::inv_next(pre, post, lbl);
        AllocationBranchBetree::State::inv_next(
            pre.i(),
            post.i(),
            lbl.i(pre),
        );
    }
}

} // verus!
