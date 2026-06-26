// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// CachedBranch variant using CachingDisk for partial branch-node access.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::map_lib::lemma_values_finite;
use vstd::assert_maps_equal;
use vstd::assert_seqs_equal;
use vstd::assert_sets_equal;

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::{
    branch_summary_insert_ensures, map_with_disjoint_values, summary_aus,
};
use crate::allocation_layer::Likes_v::restrict_domain_au;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::Utils_v::{lemma_union_set_of_sets_contains, lemma_union_set_of_sets_subset};
use crate::betree::LinkedBranch_v::{
    DiskView, LinkedBranch, Path, Refinement_v as LinkedBranchRefinement, SplitArg,
};
use crate::disk::GenericDisk_v::{
    addrs_closed, addrs_with_different_au, AU, Address, Pointer, Ranking, to_aus,
    to_aus_finite,
};
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::spec::AsyncDisk_t::RawPage;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, nop_delta};
use crate::implementation::AllocationBranchStack_v::*;
use crate::implementation::CachedBranch_v::*;
use crate::implementation::CachingDisk_v::*;

verus!{

pub open spec fn to_branch_nodes(raw_pages: Map<Address, RawPage>) -> LoadedBranch
{
    Map::new(
        |addr: Address| raw_pages.contains_key(addr),
        |addr: Address| raw_page_to_branch_node(raw_pages[addr]),
    )
}

pub open spec fn active_loaded_nodes_of(
    disk: CachingDisk::State,
    mini_allocator: MiniAllocator,
) -> LoadedBranch
{
    let nodes = to_branch_nodes(disk.visible());
    nodes.restrict(Set::new(|addr: Address|
        nodes.contains_key(addr) && mini_allocator_allocated_addrs(mini_allocator).contains(addr)
    ))
}

pub open spec fn mini_allocator_allocated_addrs(
    mini_allocator: MiniAllocator,
) -> Set<Address>
{
    Set::new(|addr: Address| {
        &&& mini_allocator.allocs.contains_key(addr.au)
        &&& (mini_allocator.allocs[addr.au].reserved
            + mini_allocator.allocs[addr.au].observed).contains(addr)
    })
}

pub proof fn mini_allocator_allocated_addrs_subset_all_aus(mini_allocator: MiniAllocator)
    ensures
        forall |addr: Address| #[trigger] mini_allocator_allocated_addrs(mini_allocator).contains(addr)
            ==> mini_allocator.all_aus().contains(addr.au),
{
}

pub proof fn mini_allocator_add_aus_preserves_allocated_addrs(
    mini_allocator: MiniAllocator,
    aus: Set<AU>,
)
    requires
        mini_allocator.wf(),
        aus.disjoint(mini_allocator.all_aus()),
    ensures
        mini_allocator_allocated_addrs(mini_allocator.add_aus(aus))
            == mini_allocator_allocated_addrs(mini_allocator),
{
    assert_sets_equal!(
        mini_allocator_allocated_addrs(mini_allocator.add_aus(aus)),
        mini_allocator_allocated_addrs(mini_allocator),
        addr => {
            if mini_allocator_allocated_addrs(mini_allocator.add_aus(aus)).contains(addr) {
                assert(mini_allocator.add_aus(aus).allocs.contains_key(addr.au));
                if mini_allocator.allocs.contains_key(addr.au) {
                    assert(mini_allocator.add_aus(aus).allocs[addr.au]
                        == mini_allocator.allocs[addr.au]);
                } else {
                    assert(aus.contains(addr.au));
                    assert(mini_allocator.add_aus(aus).allocs[addr.au]
                        == crate::allocation_layer::MiniAllocator_v::PageAllocator::new(addr.au));
                    assert(false);
                }
            }
            if mini_allocator_allocated_addrs(mini_allocator).contains(addr) {
                assert(mini_allocator.allocs.contains_key(addr.au));
                assert(mini_allocator.all_aus().contains(addr.au));
                assert(!aus.contains(addr.au));
                assert(mini_allocator.add_aus(aus).allocs[addr.au]
                    == mini_allocator.allocs[addr.au]);
            }
        }
    );
}

pub open spec fn sealed_nodes_of(
    raw_pages: Map<Address, RawPage>,
    branch_summary: Map<AU, Summary>,
) -> LoadedBranch
{
    to_branch_nodes(raw_pages).restrict(addresses_in_aus(summary_aus(branch_summary)))
}

pub open spec fn active_branch_i_of(
    active_branch: CachedBranch::State,
    mini_allocator: MiniAllocator,
    disk: CachingDisk::State,
) -> AllocationBranch
{
    AllocationBranch{
        sealed: false,
        branch: if active_branch.root is Some {
            Some(LinkedBranch{
                root: active_branch.root.unwrap(),
                disk_view: DiskView{entries: active_loaded_nodes_of(disk, mini_allocator)},
            })
        } else {
            None
        },
        mini_allocator,
    }
}

pub open spec fn sealed_summary_aus_up_to(
    sealed_roots: Seq<Address>,
    branch_summary: Map<AU, Summary>,
    end: nat,
) -> Set<AU>
    decreases end
{
    if end == 0 {
        Set::empty()
    } else {
        let idx = (end - 1) as int;
        let root = sealed_roots[idx];
        let rest = sealed_summary_aus_up_to(sealed_roots, branch_summary, (end - 1) as nat);
        if branch_summary.contains_key(root.au) {
            rest + branch_summary[root.au]
        } else {
            rest
        }
    }
}

pub open spec fn root_aus_up_to(sealed_roots: Seq<Address>, end: nat) -> Set<AU>
    decreases end
{
    if end == 0 {
        Set::empty()
    } else {
        root_aus_up_to(sealed_roots, (end - 1) as nat).insert(sealed_roots[(end - 1) as int].au)
    }
}

pub proof fn root_aus_up_to_contains(
    sealed_roots: Seq<Address>,
    end: nat,
    idx: int,
)
    requires
        0 <= idx < end,
    ensures
        root_aus_up_to(sealed_roots, end).contains(sealed_roots[idx].au),
    decreases end
{
    let last = (end - 1) as int;
    if idx == last {
    } else {
        assert(0 <= idx < end - 1);
        root_aus_up_to_contains(sealed_roots, (end - 1) as nat, idx);
    }
}

pub proof fn root_aus_up_to_member_has_index(
    sealed_roots: Seq<Address>,
    end: nat,
    au: AU,
) -> (idx: int)
    requires
        root_aus_up_to(sealed_roots, end).contains(au),
    ensures
        0 <= idx < end,
        sealed_roots[idx].au == au,
    decreases end
{
    let last = (end - 1) as int;
    if root_aus_up_to(sealed_roots, (end - 1) as nat).contains(au) {
        root_aus_up_to_member_has_index(sealed_roots, (end - 1) as nat, au)
    } else {
        assert(sealed_roots[last].au == au);
        last
    }
}

pub proof fn root_aus_up_to_full(
    sealed_roots: Seq<Address>,
)
    ensures
        root_aus_up_to(sealed_roots, sealed_roots.len() as nat) =~= to_aus(sealed_roots.to_set()),
{
    assert forall |au: AU| #[trigger] root_aus_up_to(sealed_roots, sealed_roots.len() as nat).contains(au)
        <==> to_aus(sealed_roots.to_set()).contains(au)
    by {
        if root_aus_up_to(sealed_roots, sealed_roots.len() as nat).contains(au) {
            let idx = root_aus_up_to_member_has_index(sealed_roots, sealed_roots.len() as nat, au);
            assert(sealed_roots.to_set().contains(sealed_roots[idx]));
            crate::disk::GenericDisk_v::to_aus_domain(sealed_roots.to_set());
        } else if to_aus(sealed_roots.to_set()).contains(au) {
            let root = choose |root: Address| sealed_roots.to_set().contains(root) && root.au == au;
            let idx = choose |i: int| 0 <= i < sealed_roots.len() && sealed_roots[i] == root;
            root_aus_up_to_contains(sealed_roots, sealed_roots.len() as nat, idx);
        }
    }
}

pub open spec fn sealed_summary_aus_between(
    sealed_roots: Seq<Address>,
    branch_summary: Map<AU, Summary>,
    start: nat,
    end: nat,
) -> Set<AU>
{
    sealed_summary_aus_up_to(sealed_roots, branch_summary, end)
        .difference(sealed_summary_aus_up_to(sealed_roots, branch_summary, start))
}

pub proof fn sealed_summary_aus_up_to_monotonic(
    sealed_roots: Seq<Address>,
    branch_summary: Map<AU, Summary>,
    start: nat,
    end: nat,
)
    requires start <= end
    ensures
        sealed_summary_aus_up_to(sealed_roots, branch_summary, start)
            <= sealed_summary_aus_up_to(sealed_roots, branch_summary, end),
    decreases end
{
    if start == end {
    } else {
        sealed_summary_aus_up_to_monotonic(
            sealed_roots,
            branch_summary,
            start,
            (end - 1) as nat,
        );
        assert forall |au: AU| #[trigger] sealed_summary_aus_up_to(
            sealed_roots,
            branch_summary,
            start,
        ).contains(au)
            implies sealed_summary_aus_up_to(sealed_roots, branch_summary, end).contains(au)
        by {
            assert(sealed_summary_aus_up_to(sealed_roots, branch_summary, (end - 1) as nat).contains(au));
        }
    }
}

pub proof fn sealed_summary_aus_up_to_split(
    sealed_roots: Seq<Address>,
    branch_summary: Map<AU, Summary>,
    start: nat,
    end: nat,
)
    requires start <= end
    ensures
        sealed_summary_aus_up_to(sealed_roots, branch_summary, end)
            == sealed_summary_aus_up_to(sealed_roots, branch_summary, start)
                + sealed_summary_aus_between(sealed_roots, branch_summary, start, end),
{
    sealed_summary_aus_up_to_monotonic(sealed_roots, branch_summary, start, end);
    assert_sets_equal!(
        sealed_summary_aus_up_to(sealed_roots, branch_summary, end),
        sealed_summary_aus_up_to(sealed_roots, branch_summary, start)
            + sealed_summary_aus_between(sealed_roots, branch_summary, start, end),
        au => {
            if sealed_summary_aus_up_to(sealed_roots, branch_summary, end).contains(au) {
                if !sealed_summary_aus_up_to(sealed_roots, branch_summary, start).contains(au) {
                    assert(sealed_summary_aus_between(sealed_roots, branch_summary, start, end).contains(au));
                }
            } else {
                if sealed_summary_aus_up_to(sealed_roots, branch_summary, start).contains(au) {
                    assert(false);
                }
                if sealed_summary_aus_between(sealed_roots, branch_summary, start, end).contains(au) {
                    assert(false);
                }
            }
        }
    );
}

pub proof fn sealed_summary_aus_up_to_push_insert_unchanged(
    sealed_roots: Seq<Address>,
    branch_summary: Map<AU, Summary>,
    new_root: Address,
    new_summary: Summary,
    end: nat,
)
    requires
        end <= sealed_roots.len(),
        !branch_summary.contains_key(new_root.au),
        forall |i: int| 0 <= i < end ==> branch_summary.contains_key(sealed_roots[i].au),
    ensures
        sealed_summary_aus_up_to(
            sealed_roots.push(new_root),
            branch_summary.insert(new_root.au, new_summary),
            end,
        ) == sealed_summary_aus_up_to(sealed_roots, branch_summary, end),
    decreases end
{
    if end == 0 {
    } else {
        let idx = (end - 1) as int;
        assert(0 <= idx < sealed_roots.len());
        assert(sealed_roots.push(new_root)[idx] == sealed_roots[idx]);
        assert(branch_summary.contains_key(sealed_roots[idx].au));
        assert(sealed_roots[idx].au != new_root.au);
        sealed_summary_aus_up_to_push_insert_unchanged(
            sealed_roots,
            branch_summary,
            new_root,
            new_summary,
            (end - 1) as nat,
        );
        assert(branch_summary.insert(new_root.au, new_summary).contains_key(sealed_roots[idx].au));
        assert(branch_summary.insert(new_root.au, new_summary)[sealed_roots[idx].au]
            == branch_summary[sealed_roots[idx].au]);
    }
}

pub proof fn sealed_summary_aus_up_to_contains_root_summary(
    sealed_roots: Seq<Address>,
    branch_summary: Map<AU, Summary>,
    end: nat,
    idx: int,
    au: AU,
)
    requires
        0 <= idx < end,
        branch_summary.contains_key(sealed_roots[idx].au),
        branch_summary[sealed_roots[idx].au].contains(au),
    ensures
        sealed_summary_aus_up_to(sealed_roots, branch_summary, end).contains(au),
    decreases end
{
    let last = (end - 1) as int;
    if idx == last {
    } else {
        assert(0 <= idx < end - 1);
        sealed_summary_aus_up_to_contains_root_summary(
            sealed_roots,
            branch_summary,
            (end - 1) as nat,
            idx,
            au,
        );
    }
}

pub proof fn sealed_summary_aus_up_to_subset_summary_aus(
    sealed_roots: Seq<Address>,
    branch_summary: Map<AU, Summary>,
    end: nat,
)
    requires
        branch_summary.values().finite(),
    ensures
        sealed_summary_aus_up_to(sealed_roots, branch_summary, end)
            <= summary_aus(branch_summary),
    decreases end
{
    if end == 0 {
    } else {
        sealed_summary_aus_up_to_subset_summary_aus(
            sealed_roots,
            branch_summary,
            (end - 1) as nat,
        );
        assert forall |au: AU| #[trigger] sealed_summary_aus_up_to(
            sealed_roots,
            branch_summary,
            end,
        ).contains(au)
            implies summary_aus(branch_summary).contains(au)
        by {
            if !sealed_summary_aus_up_to(sealed_roots, branch_summary, (end - 1) as nat).contains(au) {
                let root = sealed_roots[(end - 1) as int];
                assert(branch_summary.contains_key(root.au));
                assert(branch_summary[root.au].contains(au));
                assert(branch_summary.values().contains(branch_summary[root.au]));
                crate::betree::Utils_v::lemma_union_set_of_sets_subset(
                    branch_summary.values(),
                    branch_summary[root.au],
                );
            }
        }
    }
}

pub proof fn clean_aus_persistent_visible_eq(disk: CachingDisk::State, aus: Set<AU>)
    requires
        disk.inv(),
        disk.aus_clean_or_evictable(aus),
    ensures
        disk.persistent.restrict(addresses_in_aus(aus))
            == disk.visible().restrict(addresses_in_aus(aus)),
{
    assert_maps_equal!(
        disk.persistent.restrict(addresses_in_aus(aus)),
        disk.visible().restrict(addresses_in_aus(aus)),
        addr => {
            if addresses_in_aus(aus).contains(addr) {
                if disk.cache.contains_key(addr) {
                    assert(disk.aus_clean_or_evictable(aus));
                    assert(disk.status.contains_key(addr));
                    assert(disk.status[addr] == PageStatus::Clean);
                    assert(disk.persistent.contains_key(addr));
                    assert(disk.persistent[addr] == disk.cache[addr]);
                }
            }
        }
    );
}

pub proof fn disk_growth_visible_preserves_outside_aus(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    aus: Set<AU>,
)
    requires
        pre_disk.cache <= post_disk.cache,
        pre_disk.persistent <= post_disk.persistent,
        post_disk.cache.dom() - pre_disk.cache.dom() <= addresses_in_aus(aus),
        post_disk.persistent.dom() - pre_disk.persistent.dom() <= addresses_in_aus(aus),
    ensures
        forall |addr: Address| !addresses_in_aus(aus).contains(addr) ==> {
            &&& post_disk.visible().contains_key(addr) <==> pre_disk.visible().contains_key(addr)
            &&& post_disk.visible().contains_key(addr) ==> post_disk.visible()[addr] == pre_disk.visible()[addr]
        },
{
    assert forall |addr: Address| !addresses_in_aus(aus).contains(addr) implies {
        &&& post_disk.visible().contains_key(addr) <==> pre_disk.visible().contains_key(addr)
        &&& post_disk.visible().contains_key(addr) ==> post_disk.visible()[addr] == pre_disk.visible()[addr]
    } by {
            if post_disk.visible().contains_key(addr) {
            if post_disk.cache.contains_key(addr) {
                assert(post_disk.cache.dom().contains(addr));
                if !pre_disk.cache.contains_key(addr) {
                    assert((post_disk.cache.dom() - pre_disk.cache.dom()).contains(addr));
                    assert(addresses_in_aus(aus).contains(addr));
                    assert(false);
                }
                assert(post_disk.cache[addr] == pre_disk.cache[addr]);
            } else {
                assert(post_disk.persistent.contains_key(addr));
                assert(post_disk.persistent.dom().contains(addr));
                if !pre_disk.persistent.contains_key(addr) {
                    assert((post_disk.persistent.dom() - pre_disk.persistent.dom()).contains(addr));
                    assert(addresses_in_aus(aus).contains(addr));
                    assert(false);
                }
                if pre_disk.cache.contains_key(addr) {
                    assert(post_disk.cache.contains_key(addr));
                    assert(false);
                }
                assert(post_disk.persistent[addr] == pre_disk.persistent[addr]);
            }
        }
        if pre_disk.visible().contains_key(addr) {
            if pre_disk.cache.contains_key(addr) {
                assert(post_disk.cache.contains_key(addr));
                assert(post_disk.cache[addr] == pre_disk.cache[addr]);
            } else {
                assert(pre_disk.persistent.contains_key(addr));
                assert(post_disk.persistent.contains_key(addr));
                assert(post_disk.persistent[addr] == pre_disk.persistent[addr]);
                if post_disk.cache.contains_key(addr) {
                    assert(post_disk.cache.dom().contains(addr));
                    if !pre_disk.cache.contains_key(addr) {
                        assert((post_disk.cache.dom() - pre_disk.cache.dom()).contains(addr));
                        assert(addresses_in_aus(aus).contains(addr));
                    }
                    assert(false);
                }
            }
        }
    }
}

pub proof fn disk_growth_visible_aus_subset(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    aus: Set<AU>,
)
    requires
        pre_disk.cache <= post_disk.cache,
        pre_disk.persistent <= post_disk.persistent,
        post_disk.cache.dom() - pre_disk.cache.dom() <= addresses_in_aus(aus),
        post_disk.persistent.dom() - pre_disk.persistent.dom() <= addresses_in_aus(aus),
    ensures
        to_aus(post_disk.visible().dom()) <= to_aus(pre_disk.visible().dom()) + aus,
{
    disk_growth_visible_preserves_outside_aus(pre_disk, post_disk, aus);
    assert forall |au: AU| #[trigger] to_aus(post_disk.visible().dom()).contains(au)
        implies (to_aus(pre_disk.visible().dom()) + aus).contains(au) by {
        let addr = choose |addr: Address| post_disk.visible().dom().contains(addr) && addr.au == au;
        if addresses_in_aus(aus).contains(addr) {
            assert(aus.contains(au));
        } else {
            assert(pre_disk.visible().contains_key(addr));
            crate::disk::GenericDisk_v::to_aus_domain(pre_disk.visible().dom());
            assert(to_aus(pre_disk.visible().dom()).contains(au));
        }
    }
}

pub proof fn disk_growth_preserves_aus_clean_or_evictable(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    growth_aus: Set<AU>,
    clean_aus: Set<AU>,
)
    requires
        pre_disk.inv(),
        pre_disk.aus_clean_or_evictable(clean_aus),
        pre_disk.cache <= post_disk.cache,
        pre_disk.status <= post_disk.status,
        pre_disk.persistent <= post_disk.persistent,
        post_disk.cache.dom() - pre_disk.cache.dom() <= addresses_in_aus(growth_aus),
        clean_aus.disjoint(growth_aus),
    ensures
        post_disk.aus_clean_or_evictable(clean_aus),
{
    assert forall |addr: Address| #[trigger] post_disk.cache.contains_key(addr)
        && clean_aus.contains(addr.au)
        implies {
            &&& post_disk.status.contains_key(addr)
            &&& post_disk.status[addr] == PageStatus::Clean
            &&& post_disk.persistent.contains_key(addr)
            &&& post_disk.persistent[addr] == post_disk.cache[addr]
        }
    by {
        if !pre_disk.cache.contains_key(addr) {
            assert(post_disk.cache.dom().contains(addr));
            assert((post_disk.cache.dom() - pre_disk.cache.dom()).contains(addr));
            assert(addresses_in_aus(growth_aus).contains(addr));
            assert(growth_aus.contains(addr.au));
            assert(false);
        }
        assert(pre_disk.status.contains_key(addr));
        assert(pre_disk.status[addr] == PageStatus::Clean);
        assert(pre_disk.persistent.contains_key(addr));
        assert(pre_disk.persistent[addr] == pre_disk.cache[addr]);
        assert(post_disk.status.contains_key(addr));
        assert(post_disk.status[addr] == pre_disk.status[addr]);
        assert(post_disk.persistent.contains_key(addr));
        assert(post_disk.persistent[addr] == pre_disk.persistent[addr]);
        assert(post_disk.cache[addr] == pre_disk.cache[addr]);
    }
}

pub proof fn disk_growth_preserves_sealed_nodes(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    branch_summary: Map<AU, Summary>,
    aus: Set<AU>,
)
    requires
        pre_disk.cache <= post_disk.cache,
        pre_disk.persistent <= post_disk.persistent,
        post_disk.cache.dom() - pre_disk.cache.dom() <= addresses_in_aus(aus),
        post_disk.persistent.dom() - pre_disk.persistent.dom() <= addresses_in_aus(aus),
        aus.disjoint(summary_aus(branch_summary)),
    ensures
        sealed_nodes_of(post_disk.visible(), branch_summary)
            == sealed_nodes_of(pre_disk.visible(), branch_summary),
{
    disk_growth_visible_preserves_outside_aus(pre_disk, post_disk, aus);
    let sealed_addrs = addresses_in_aus(summary_aus(branch_summary));
    assert_maps_equal!(
        sealed_nodes_of(post_disk.visible(), branch_summary),
        sealed_nodes_of(pre_disk.visible(), branch_summary),
        addr => {
            if sealed_addrs.contains(addr) {
                assert(!addresses_in_aus(aus).contains(addr)) by {
                    if addresses_in_aus(aus).contains(addr) {
                        assert(aus.contains(addr.au));
                        assert(summary_aus(branch_summary).contains(addr.au));
                        assert(false);
                    }
                }
            }
        }
    );
}

pub proof fn disk_growth_preserves_active_loaded_nodes(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    pre_mini_allocator: MiniAllocator,
    post_mini_allocator: MiniAllocator,
    aus: Set<AU>,
)
    requires
        pre_mini_allocator.wf(),
        post_mini_allocator == pre_mini_allocator.add_aus(aus),
        aus.disjoint(pre_mini_allocator.all_aus()),
        pre_disk.cache <= post_disk.cache,
        pre_disk.persistent <= post_disk.persistent,
        post_disk.cache.dom() - pre_disk.cache.dom() <= addresses_in_aus(aus),
        post_disk.persistent.dom() - pre_disk.persistent.dom() <= addresses_in_aus(aus),
    ensures
        active_loaded_nodes_of(post_disk, post_mini_allocator)
            == active_loaded_nodes_of(pre_disk, pre_mini_allocator),
{
    mini_allocator_add_aus_preserves_allocated_addrs(pre_mini_allocator, aus);
    disk_growth_visible_preserves_outside_aus(pre_disk, post_disk, aus);
    assert_maps_equal!(
        active_loaded_nodes_of(post_disk, post_mini_allocator),
        active_loaded_nodes_of(pre_disk, pre_mini_allocator),
        addr => {
            if active_loaded_nodes_of(post_disk, post_mini_allocator).contains_key(addr) {
                assert(mini_allocator_allocated_addrs(post_mini_allocator).contains(addr));
                assert(mini_allocator_allocated_addrs(pre_mini_allocator).contains(addr));
                mini_allocator_allocated_addrs_subset_all_aus(pre_mini_allocator);
                assert(pre_mini_allocator.all_aus().contains(addr.au));
                assert(!aus.contains(addr.au));
                assert(!addresses_in_aus(aus).contains(addr));
                assert(post_disk.visible().contains_key(addr));
                assert(pre_disk.visible().contains_key(addr));
                assert(post_disk.visible()[addr] == pre_disk.visible()[addr]);
            }
            if active_loaded_nodes_of(pre_disk, pre_mini_allocator).contains_key(addr) {
                assert(mini_allocator_allocated_addrs(pre_mini_allocator).contains(addr));
                assert(mini_allocator_allocated_addrs(post_mini_allocator).contains(addr));
                mini_allocator_allocated_addrs_subset_all_aus(pre_mini_allocator);
                assert(pre_mini_allocator.all_aus().contains(addr.au));
                assert(!aus.contains(addr.au));
                assert(!addresses_in_aus(aus).contains(addr));
                assert(pre_disk.visible().contains_key(addr));
                assert(post_disk.visible().contains_key(addr));
                assert(post_disk.visible()[addr] == pre_disk.visible()[addr]);
            }
        }
    );
}

pub proof fn disk_growth_preserves_loaded_metadata(
    pre: CachingDiskBranch::State,
    post_disk: CachingDisk::State,
    aus: Set<AU>,
)
    requires
        pre.inv(),
        pre.metadata_loaded,
        post_disk.inv(),
        pre.disk.cache <= post_disk.cache,
        pre.disk.persistent <= post_disk.persistent,
        post_disk.cache.dom() - pre.disk.cache.dom() <= addresses_in_aus(aus),
        post_disk.persistent.dom() - pre.disk.persistent.dom() <= addresses_in_aus(aus),
        aus.disjoint(summary_aus(pre.branch_summary)),
    ensures
        branch_summary_reads_valid(pre.sealed_roots, to_branch_nodes(post_disk.visible())),
        pre.branch_summary.dom() =~= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat),
        loaded_branch_summary_agrees(
            pre.sealed_roots,
            to_branch_nodes(post_disk.visible()),
            pre.branch_summary,
        ),
        completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible()))
            == pre.branch_summary,
        sealed_nodes_of(post_disk.visible(), pre.branch_summary)
            == sealed_nodes_of(pre.disk.visible(), pre.branch_summary),
{
    assert(pre.branch_metadata_loaded());
    disk_growth_visible_preserves_outside_aus(pre.disk, post_disk, aus);
    disk_growth_preserves_sealed_nodes(pre.disk, post_disk, pre.branch_summary, aus);
    assert(pre.branch_summary == pre.interpreted_branch_summary());
    branch_summary_from_reads_up_to_self_ensures(
        pre.sealed_roots,
        pre.visible_branch_nodes(),
        pre.sealed_roots.len() as nat,
    );
    assert(pre.branch_summary.dom() =~= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat)) by {
        assert(pre.interpreted_branch_summary().dom()
            =~= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat));
    }
    assert(branch_summary_reads_valid(pre.sealed_roots, to_branch_nodes(post_disk.visible()))) by {
        assert forall |i: int| #![trigger pre.sealed_roots[i]]
            0 <= i < pre.sealed_roots.len()
            implies root_summary_read_valid(pre.sealed_roots[i], to_branch_nodes(post_disk.visible()))
        by {
            assert(pre.loaded_branch_summary_agrees());
            let root = pre.sealed_roots[i];
            root_aus_up_to_contains(pre.sealed_roots, pre.sealed_roots.len() as nat, i);
            assert(pre.branch_summary.dom().contains(root.au));
            assert(pre.branch_summary.contains_key(root.au));
            assert(root_summary_read_valid(root, pre.visible_branch_nodes()));
            assert(root_summary_from_read(root, pre.visible_branch_nodes()) == pre.branch_summary[root.au]);
            pre.sealed_stack_i().root_au_in_summary(pre.branch_summary, root);
            assert(summary_aus(pre.branch_summary).contains(root.au)) by {
                assert(pre.branch_summary.values().contains(pre.branch_summary[root.au]));
                assert(pre.branch_summary[root.au].contains(root.au));
                lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[root.au]);
            }
            assert(!addresses_in_aus(aus).contains(root)) by {
                if addresses_in_aus(aus).contains(root) {
                    assert(aus.contains(root.au));
                    assert(false);
                }
            }
            assert(to_branch_nodes(post_disk.visible())[root] == pre.visible_branch_nodes()[root]);
            if pre.visible_branch_nodes()[root] is Index {
                let aux = pre.visible_branch_nodes()[root]->aux_ptr.unwrap();
                pre.loaded_index_root_aux_in_summary(root, aux);
                assert(summary_aus(pre.branch_summary).contains(aux.au)) by {
                    assert(pre.branch_summary.values().contains(pre.branch_summary[root.au]));
                    lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[root.au]);
                }
                assert(!addresses_in_aus(aus).contains(aux)) by {
                    if addresses_in_aus(aus).contains(aux) {
                        assert(aus.contains(aux.au));
                        assert(false);
                    }
                }
                assert(to_branch_nodes(post_disk.visible())[aux] == pre.visible_branch_nodes()[aux]);
            }
        }
    };
    assert forall |i: int| 0 <= i < pre.sealed_roots.len() implies {
        &&& pre.branch_summary.contains_key(pre.sealed_roots[i].au)
        &&& root_summary_from_read(pre.sealed_roots[i], to_branch_nodes(post_disk.visible()))
            == pre.branch_summary[pre.sealed_roots[i].au]
    } by {
        assert(pre.loaded_branch_summary_agrees());
        let root = pre.sealed_roots[i];
        root_aus_up_to_contains(pre.sealed_roots, pre.sealed_roots.len() as nat, i);
        assert(pre.branch_summary.dom().contains(root.au));
        assert(pre.branch_summary.contains_key(root.au));
        assert(root_summary_from_read(root, pre.visible_branch_nodes()) == pre.branch_summary[root.au]);
        assert(root_summary_read_valid(root, pre.visible_branch_nodes()));
        assert(to_branch_nodes(post_disk.visible())[root] == pre.visible_branch_nodes()[root]) by {
            pre.sealed_stack_i().root_au_in_summary(pre.branch_summary, root);
            assert(summary_aus(pre.branch_summary).contains(root.au)) by {
                assert(pre.branch_summary.values().contains(pre.branch_summary[root.au]));
                assert(pre.branch_summary[root.au].contains(root.au));
                lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[root.au]);
            }
            assert(!addresses_in_aus(aus).contains(root)) by {
                if addresses_in_aus(aus).contains(root) {
                    assert(aus.contains(root.au));
                    assert(false);
                }
            }
        };
        if pre.visible_branch_nodes()[root] is Index {
            let aux = pre.visible_branch_nodes()[root]->aux_ptr.unwrap();
            assert(to_branch_nodes(post_disk.visible())[aux] == pre.visible_branch_nodes()[aux]) by {
                pre.loaded_index_root_aux_in_summary(root, aux);
                assert(summary_aus(pre.branch_summary).contains(aux.au)) by {
                    assert(pre.branch_summary.values().contains(pre.branch_summary[root.au]));
                    lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[root.au]);
                }
                assert(!addresses_in_aus(aus).contains(aux)) by {
                    if addresses_in_aus(aus).contains(aux) {
                        assert(aus.contains(aux.au));
                        assert(false);
                    }
                }
            };
        }
    };
    branch_summary_from_reads_up_to_ensures(
        pre.sealed_roots,
        to_branch_nodes(post_disk.visible()),
        pre.branch_summary,
        pre.sealed_roots.len() as nat,
    );
    assert(completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible()))
        == pre.branch_summary) by {
        assert_maps_equal!(
            completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible())),
            pre.branch_summary,
            au => {
                if completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible())).contains_key(au) {
                    assert(completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible())).dom().contains(au));
                    let idx = root_aus_up_to_member_has_index(pre.sealed_roots, pre.sealed_roots.len() as nat, au);
                    assert(completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible()))[au]
                        == pre.branch_summary[au]);
                }
                if pre.branch_summary.contains_key(au) {
                    assert(root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat).contains(au));
                    assert(completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible())).dom().contains(au));
                }
            }
        );
    };
    assert(loaded_branch_summary_agrees(
        pre.sealed_roots,
        to_branch_nodes(post_disk.visible()),
        pre.branch_summary,
    )) by {
        assert(pre.branch_summary.dom() <= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat));
        assert forall |i: int| #![trigger pre.sealed_roots[i]]
            0 <= i < pre.sealed_roots.len() && pre.branch_summary.contains_key(pre.sealed_roots[i].au)
            implies {
                &&& root_summary_read_valid(pre.sealed_roots[i], to_branch_nodes(post_disk.visible()))
                &&& pre.branch_summary[pre.sealed_roots[i].au]
                    == root_summary_from_read(pre.sealed_roots[i], to_branch_nodes(post_disk.visible()))
            }
        by {
        }
    };
}

pub proof fn access_preserves_sealed_nodes(
    pre_disk: CachingDisk::State,
    post_disk: CachingDisk::State,
    branch_summary: Map<AU, Summary>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre_disk.inv(),
        post_disk.inv(),
        CachingDisk::State::next(
            pre_disk,
            post_disk,
            CachingDisk::Label::Access{reads, writes},
        ),
        writes.dom().disjoint(addresses_in_aus(summary_aus(branch_summary))),
    ensures
        sealed_nodes_of(post_disk.visible(), branch_summary)
            == sealed_nodes_of(pre_disk.visible(), branch_summary),
{
    CachingDisk::State::access_visible_effect(pre_disk, post_disk, reads, writes);
    let sealed_addrs = addresses_in_aus(summary_aus(branch_summary));
    assert_maps_equal!(
        sealed_nodes_of(post_disk.visible(), branch_summary),
        sealed_nodes_of(pre_disk.visible(), branch_summary),
        addr => {
            if sealed_nodes_of(post_disk.visible(), branch_summary).contains_key(addr) {
                assert(sealed_addrs.contains(addr));
                if writes.contains_key(addr) {
                    assert(writes.dom().contains(addr));
                    assert(false);
                }
            }
            if sealed_nodes_of(pre_disk.visible(), branch_summary).contains_key(addr) {
                assert(sealed_addrs.contains(addr));
                if writes.contains_key(addr) {
                    assert(writes.dom().contains(addr));
                    assert(false);
                }
            }
        }
    );
}

pub proof fn access_preserves_loaded_metadata(
    pre: CachingDiskBranch::State,
    post_disk: CachingDisk::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
	)
	    requires
	        pre.inv(),
	        pre.metadata_loaded,
	        post_disk.inv(),
        CachingDisk::State::next(
            pre.disk,
            post_disk,
            CachingDisk::Label::Access{reads, writes},
        ),
        writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary))),
    ensures
        branch_summary_reads_valid(pre.sealed_roots, to_branch_nodes(post_disk.visible())),
        pre.branch_summary.dom() =~= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat),
        loaded_branch_summary_agrees(
            pre.sealed_roots,
            to_branch_nodes(post_disk.visible()),
            pre.branch_summary,
        ),
        completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible()))
            == pre.branch_summary,
        sealed_nodes_of(post_disk.visible(), pre.branch_summary)
            == sealed_nodes_of(pre.disk.visible(), pre.branch_summary),
	{
	    assert(pre.branch_metadata_loaded());
	    CachingDisk::State::access_visible_effect(pre.disk, post_disk, reads, writes);
    access_preserves_sealed_nodes(pre.disk, post_disk, pre.branch_summary, reads, writes);
    assert(pre.branch_summary == pre.interpreted_branch_summary());
    branch_summary_from_reads_up_to_self_ensures(
        pre.sealed_roots,
        pre.visible_branch_nodes(),
        pre.sealed_roots.len() as nat,
    );
    assert(pre.branch_summary.dom() =~= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat)) by {
        assert(pre.interpreted_branch_summary().dom()
            =~= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat));
    }
    assert(branch_summary_reads_valid(pre.sealed_roots, to_branch_nodes(post_disk.visible()))) by {
        assert forall |i: int| #![trigger pre.sealed_roots[i]]
            0 <= i < pre.sealed_roots.len()
            implies root_summary_read_valid(pre.sealed_roots[i], to_branch_nodes(post_disk.visible()))
        by {
            assert(pre.loaded_branch_summary_agrees());
            let root = pre.sealed_roots[i];
            root_aus_up_to_contains(pre.sealed_roots, pre.sealed_roots.len() as nat, i);
            assert(pre.branch_summary.dom().contains(root.au));
            assert(pre.branch_summary.contains_key(root.au));
            assert(root_summary_read_valid(root, pre.visible_branch_nodes()));
            assert(root_summary_from_read(root, pre.visible_branch_nodes()) == pre.branch_summary[root.au]);
            pre.sealed_stack_i().root_au_in_summary(pre.branch_summary, root);
            assert(summary_aus(pre.branch_summary).contains(root.au)) by {
                assert(pre.branch_summary.values().contains(pre.branch_summary[root.au]));
                assert(pre.branch_summary[root.au].contains(root.au));
                lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[root.au]);
            }
            assert(!writes.dom().contains(root)) by {
                if writes.dom().contains(root) {
                    assert(addresses_in_aus(summary_aus(pre.branch_summary)).contains(root));
                    assert(false);
                }
            }
            assert(to_branch_nodes(post_disk.visible())[root] == pre.visible_branch_nodes()[root]);
            if pre.visible_branch_nodes()[root] is Index {
                let aux = pre.visible_branch_nodes()[root]->aux_ptr.unwrap();
                pre.loaded_index_root_aux_in_summary(root, aux);
                assert(summary_aus(pre.branch_summary).contains(aux.au)) by {
                    assert(pre.branch_summary.values().contains(pre.branch_summary[root.au]));
                    lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[root.au]);
                }
                assert(!writes.dom().contains(aux)) by {
                    if writes.dom().contains(aux) {
                        assert(addresses_in_aus(summary_aus(pre.branch_summary)).contains(aux));
                        assert(false);
                    }
                }
                assert(to_branch_nodes(post_disk.visible())[aux] == pre.visible_branch_nodes()[aux]);
            }
        }
    };
    assert forall |i: int| 0 <= i < pre.sealed_roots.len() implies {
        &&& pre.branch_summary.contains_key(pre.sealed_roots[i].au)
        &&& root_summary_from_read(pre.sealed_roots[i], to_branch_nodes(post_disk.visible()))
            == pre.branch_summary[pre.sealed_roots[i].au]
    } by {
        assert(pre.loaded_branch_summary_agrees());
        let root = pre.sealed_roots[i];
        root_aus_up_to_contains(pre.sealed_roots, pre.sealed_roots.len() as nat, i);
        assert(pre.branch_summary.dom().contains(root.au));
        assert(pre.branch_summary.contains_key(root.au));
        assert(root_summary_from_read(root, pre.visible_branch_nodes()) == pre.branch_summary[root.au]);
        assert(root_summary_read_valid(root, pre.visible_branch_nodes()));
        assert(to_branch_nodes(post_disk.visible())[root] == pre.visible_branch_nodes()[root]) by {
            pre.sealed_stack_i().root_au_in_summary(pre.branch_summary, root);
            assert(summary_aus(pre.branch_summary).contains(root.au)) by {
                assert(pre.branch_summary.values().contains(pre.branch_summary[root.au]));
                assert(pre.branch_summary[root.au].contains(root.au));
                lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[root.au]);
            }
            assert(!writes.dom().contains(root)) by {
                if writes.dom().contains(root) {
                    assert(addresses_in_aus(summary_aus(pre.branch_summary)).contains(root));
                    assert(false);
                }
            }
        };
        if pre.visible_branch_nodes()[root] is Index {
            let aux = pre.visible_branch_nodes()[root]->aux_ptr.unwrap();
            assert(to_branch_nodes(post_disk.visible())[aux] == pre.visible_branch_nodes()[aux]) by {
                pre.loaded_index_root_aux_in_summary(root, aux);
                assert(summary_aus(pre.branch_summary).contains(aux.au)) by {
                    assert(pre.branch_summary.values().contains(pre.branch_summary[root.au]));
                    lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[root.au]);
                }
                assert(!writes.dom().contains(aux)) by {
                    if writes.dom().contains(aux) {
                        assert(addresses_in_aus(summary_aus(pre.branch_summary)).contains(aux));
                        assert(false);
                    }
                }
            };
        }
    };
    branch_summary_from_reads_up_to_ensures(
        pre.sealed_roots,
        to_branch_nodes(post_disk.visible()),
        pre.branch_summary,
        pre.sealed_roots.len() as nat,
    );
    assert(completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible()))
        == pre.branch_summary) by {
        assert_maps_equal!(
            completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible())),
            pre.branch_summary,
            au => {
                if completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible())).contains_key(au) {
                    assert(completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible())).dom().contains(au));
                    let idx = root_aus_up_to_member_has_index(pre.sealed_roots, pre.sealed_roots.len() as nat, au);
                    assert(completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible()))[au]
                        == pre.branch_summary[au]);
                }
                if pre.branch_summary.contains_key(au) {
                    assert(root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat).contains(au));
                    assert(completed_branch_summary_from_reads(pre.sealed_roots, to_branch_nodes(post_disk.visible())).dom().contains(au));
                }
            }
        );
    };
    assert(loaded_branch_summary_agrees(
        pre.sealed_roots,
        to_branch_nodes(post_disk.visible()),
        pre.branch_summary,
    )) by {
        assert(pre.branch_summary.dom() <= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat));
        assert forall |i: int| #![trigger pre.sealed_roots[i]]
            0 <= i < pre.sealed_roots.len() && pre.branch_summary.contains_key(pre.sealed_roots[i].au)
            implies {
                &&& root_summary_read_valid(pre.sealed_roots[i], to_branch_nodes(post_disk.visible()))
                &&& pre.branch_summary[pre.sealed_roots[i].au]
                    == root_summary_from_read(pre.sealed_roots[i], to_branch_nodes(post_disk.visible()))
            }
        by {
        }
    };
}

pub proof fn access_preserves_sealed_stack_i(
    pre: CachingDiskBranch::State,
    post: CachingDiskBranch::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
	)
	    requires
	        pre.inv(),
	        pre.metadata_loaded,
	        post.inv(),
        CachingDisk::State::next(
            pre.disk,
            post.disk,
            CachingDisk::Label::Access{reads, writes},
        ),
        writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary))),
        post.sealed_roots == pre.sealed_roots,
        post.branch_summary == pre.branch_summary,
    ensures
        post.branch_metadata_loaded(),
        post.interpreted_branch_summary() == pre.interpreted_branch_summary(),
        post.sealed_stack_i() == pre.sealed_stack_i(),
	{
	    assert(pre.branch_metadata_loaded());
	    access_preserves_loaded_metadata(pre, post.disk, reads, writes);
    assert(pre.branch_summary == pre.interpreted_branch_summary());
    assert(post.interpreted_branch_summary() == pre.branch_summary);
    assert(post.branch_metadata_loaded());
    assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
    assert(post.sealed_stack_i().sealed_roots == pre.sealed_stack_i().sealed_roots);
    assert(post.sealed_stack_i().sealed_disk.entries == pre.sealed_stack_i().sealed_disk.entries) by {
        assert(post.sealed_stack_i().sealed_disk.entries
            == sealed_nodes_of(post.disk.visible(), post.interpreted_branch_summary()));
        assert(pre.sealed_stack_i().sealed_disk.entries
            == sealed_nodes_of(pre.disk.visible(), pre.interpreted_branch_summary()));
        assert(sealed_nodes_of(post.disk.visible(), post.interpreted_branch_summary())
            == sealed_nodes_of(post.disk.visible(), pre.branch_summary));
        assert(sealed_nodes_of(pre.disk.visible(), pre.interpreted_branch_summary())
            == sealed_nodes_of(pre.disk.visible(), pre.branch_summary));
        assert(sealed_nodes_of(post.disk.visible(), pre.branch_summary)
            == sealed_nodes_of(pre.disk.visible(), pre.branch_summary));
    };
    assert(post.sealed_stack_i().sealed_disk == pre.sealed_stack_i().sealed_disk);
}

pub proof fn access_preserves_persisted_prefix_clean(
    pre: CachingDiskBranch::State,
    post_disk: CachingDisk::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
	)
	    requires
	        pre.inv(),
	        pre.metadata_loaded,
	        post_disk.inv(),
        CachingDisk::State::next(
            pre.disk,
            post_disk,
            CachingDisk::Label::Access{reads, writes},
        ),
	        writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary))),
	    ensures
	        post_disk.aus_clean_or_evictable(sealed_summary_aus_up_to(
	            pre.sealed_roots,
	            pre.branch_summary,
	            pre.persisted_root_count,
	        )),
	{
	    assert(pre.branch_metadata_loaded());
	    assert(pre.branch_summary == pre.interpreted_branch_summary());
	    pre.i().sealed_stack.sealed_disk.build_branch_summary_finite(
	        pre.i().sealed_stack.sealed_roots.to_set(),
	    );
	    assert(pre.branch_summary.values().finite());
	    sealed_summary_aus_up_to_subset_summary_aus(
	        pre.sealed_roots,
	        pre.branch_summary,
	        pre.persisted_root_count,
	    );
	    let persisted_aus = sealed_summary_aus_up_to(
	        pre.sealed_roots,
	        pre.branch_summary,
	        pre.persisted_root_count,
	    );
    assert(writes.dom().disjoint(addresses_in_aus(persisted_aus))) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
	            implies !addresses_in_aus(persisted_aus).contains(addr) by {
	            assert(!addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr));
	        }
	    };
    CachingDisk::State::access_preserves_aus_clean_or_evictable(
        pre.disk,
        post_disk,
        reads,
        writes,
        persisted_aus,
    );
}

proof fn query_read_node_matches_visible(
    disk: CachingDisk::State,
    reads: Map<Address, RawPage>,
    addr: Address,
)
    requires
        reads <= disk.cache,
        reads.contains_key(addr),
    ensures
        to_branch_nodes(disk.visible()).contains_key(addr),
        to_branch_nodes(reads)[addr] == to_branch_nodes(disk.visible())[addr],
{
    assert(disk.cache.contains_key(addr));
    assert(disk.visible().contains_key(addr));
    assert(reads[addr] == disk.cache[addr]);
    assert(disk.visible()[addr] == disk.cache[addr]);
}

proof fn child_branch_inv_internal_from_parent(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    child_idx: int,
)
    requires
        branch.inv_internal(ranking),
        branch.root().valid_child_index(child_idx),
    ensures
        branch.child_at_idx(child_idx).inv_internal(ranking),
{
    assert(branch.child_at_idx(child_idx).valid_ranking(ranking)) by {
        assert(branch.disk_view.valid_ranking(ranking));
        assert(ranking.contains_key(branch.root));
        assert(branch.disk_view.node_children_respects_rank(ranking, branch.root));
        assert(ranking.contains_key(branch.root()->children[child_idx]));
    };
    assert(branch.child_at_idx(child_idx).keys_strictly_sorted_internal(ranking));
    assert(branch.child_at_idx(child_idx).all_keys_in_range_internal(ranking));
}

proof fn leaf_append_route_equiv(leaf: BranchNode, keys: Seq<Key>)
    requires
        leaf is Leaf,
        leaf.wf(),
        leaf.keys_strictly_sorted(),
        leaf->keys.len() > 0,
        keys.len() > 0,
        Key::is_strictly_sorted(keys),
        Key::lt(leaf->keys.last(), keys[0]),
    ensures
        leaf.route(keys[0]) == leaf.route(keys.last()),
{
    let last_idx = leaf->keys.len() - 1;
    Key::strictly_sorted_implies_sorted(leaf->keys);
    Key::strictly_sorted_implies_sorted(keys);
    Key::lte_transitive_forall();
    assert(0 <= last_idx < leaf->keys.len());
    assert(Key::lte(leaf->keys[last_idx], keys[0]));
    Key::largest_lte_is_lemma(leaf->keys, keys[0], last_idx);
    assert(Key::lte(keys[0], keys.last()));
    assert(Key::lte(leaf->keys[last_idx], keys.last()));
    Key::largest_lte_is_lemma(leaf->keys, keys.last(), last_idx);
}

proof fn receipt_path_valid_for_append(
    disk: CachingDisk::State,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    keys: Seq<Key>,
    msgs: Seq<Message>,
)
    requires
        reads <= disk.cache,
        branch.inv_internal(ranking),
        receipt.root == branch.root,
        keys.len() > 0,
        loaded_append_ready(receipt, to_branch_nodes(reads), keys, msgs),
        forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            ==> branch.disk_view.entries[addr] == to_branch_nodes(disk.visible())[addr],
    ensures
        ({
            let path = Path{branch, key: keys[0], depth: receipt.depth()};
            &&& path.valid()
            &&& path.target().has_root()
            &&& path.target().root == receipt.target().addr
            &&& path.target().root() == receipt.target().node
            &&& path.target().disk_view == branch.disk_view
            &&& path.path_equiv(keys.last())
        }),
    decreases receipt.depth(),
{
    let read_nodes = to_branch_nodes(reads);
    let path = Path{branch, key: keys[0], depth: receipt.depth()};
    let root = branch.root;

    assert(receipt.valid_for(receipt.root, read_nodes));
    assert(receipt.root == root);
    assert(receipt.key == keys[0]);
    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
    }
    assert(read_nodes.contains_key(root));
    query_read_node_matches_visible(disk, reads, root);
    assert(branch.disk_view.entries.contains_key(root));
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == branch.root());

    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.target() == receipt.lines[0]);
        assert(path.valid());
        assert(path.target() == branch);
        assert(path.target().has_root());
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        leaf_append_route_equiv(receipt.target().node, keys);
        assert(path.path_equiv(keys.last()));
    } else {
        assert(receipt.lines.len() > 1);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx = branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), receipt.key);
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, read_nodes);
        assert(child_branch.root == child_receipt.root) by {
            assert(receipt.lines[0].node->children[child_idx] == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx] == receipt.lines[1].addr);
            assert(child_branch.root == branch.root()->children[child_idx]);
            assert(child_receipt.root == receipt.lines[1].addr);
        }
        assert(child_receipt.target() == receipt.target()) by {
            assert(child_receipt.lines.last() == receipt.lines.last());
        }
        assert(child_receipt.path_equiv(keys.last())) by {
            assert forall |i: int|
                0 <= i < child_receipt.lines.len() - 1
                implies child_receipt.lines[i].node.route(child_receipt.key)
                    == #[trigger] child_receipt.lines[i].node.route(keys.last())
            by {
                assert(child_receipt.lines[i] == receipt.lines[i + 1]);
                assert(0 <= i + 1 < receipt.lines.len() - 1);
            }
        }
        assert(loaded_append_ready(child_receipt, read_nodes, keys, msgs));
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        receipt_path_valid_for_append(
            disk,
            child_branch,
            ranking,
            reads,
            child_receipt,
            keys,
            msgs,
        );
        assert(path.subpath() == Path{
            branch: child_branch,
            key: keys[0],
            depth: child_receipt.depth(),
        });
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(path.target().has_root());
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().disk_view == branch.disk_view);
        assert(receipt.path_equiv(keys.last()));
        assert(branch.root().route(receipt.key) == branch.root().route(keys.last()));
        assert(path.path_equiv(keys.last()));
    }
}

pub proof fn receipt_path_valid_for_split(
    disk: CachingDisk::State,
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    reads: Map<Address, RawPage>,
    receipt: LoadedPathReceipt,
    split_arg: SplitArg,
    new_child_addr: Address,
)
    requires
        reads <= disk.cache,
        branch.inv_internal(ranking),
        receipt.root == branch.root,
        loaded_split_ready(receipt, to_branch_nodes(reads), split_arg),
        branch.disk_view.is_fresh(set!{new_child_addr}),
        forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            ==> branch.disk_view.entries[addr] == to_branch_nodes(disk.visible())[addr],
    ensures
        ({
            let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
            &&& path.valid()
            &&& path.target().root == receipt.target().addr
            &&& path.target().root() == receipt.target().node
            &&& path.target().disk_view == branch.disk_view
            &&& path.target().can_split_child_of_index(split_arg, new_child_addr)
        }),
    decreases receipt.depth(),
{
    let read_nodes = to_branch_nodes(reads);
    let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
    let root = branch.root;

    assert(receipt.valid_for(receipt.root, read_nodes));
    assert(receipt.key == split_arg.get_pivot());
    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
    }
    assert(read_nodes.contains_key(root));
    query_read_node_matches_visible(disk, reads, root);
    assert(branch.disk_view.entries.contains_key(root));
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == branch.root());

    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.target() == receipt.lines[0]);
        assert(path.valid());
        assert(path.target() == branch);
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().root() is Index);
        let child_idx = path.target().root().route(split_arg.get_pivot()) + 1;
        LinkedBranchRefinement::lemma_route_ensures(path.target().root(), split_arg.get_pivot());
        assert(path.target().root().valid_child_index(child_idx));
        assert(path.target().root()->children[child_idx] == receipt.child_addr());
        let child_branch = path.target().child_at_idx(child_idx);
        assert(child_branch.root == receipt.child_addr());
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        assert(child_branch.disk_view.entries.contains_key(child_branch.root));
        assert(read_nodes.contains_key(receipt.child_addr()));
        query_read_node_matches_visible(disk, reads, receipt.child_addr());
        assert(read_nodes[receipt.child_addr()] == branch.disk_view.entries[receipt.child_addr()]);
        assert(child_branch.root() == read_nodes[receipt.child_addr()]);
        assert(child_branch.has_root()) by {
            assert(loaded_line_wf(read_nodes, receipt.child_addr()));
            assert(!(read_nodes[receipt.child_addr()] is Auxiliary));
        }
        assert(split_arg.wf(child_branch)) by {
            assert(split_arg_matches_child(read_nodes[receipt.child_addr()], split_arg));
            assert(child_branch.root() == read_nodes[receipt.child_addr()]);
        }
        assert(child_branch.disk_view.is_fresh(set!{new_child_addr}));
        assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
    } else {
        assert(receipt.lines.len() > 1);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx = branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), receipt.key);
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, read_nodes);
        assert(child_branch.root == child_receipt.root) by {
            assert(receipt.lines[0].node->children[child_idx] == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx] == receipt.lines[1].addr);
            assert(child_branch.root == branch.root()->children[child_idx]);
            assert(child_receipt.root == receipt.lines[1].addr);
        }
        assert(child_receipt.target() == receipt.target()) by {
            assert(child_receipt.lines.last() == receipt.lines.last());
        }
        assert(child_receipt.child_addr() == receipt.child_addr()) by {
            assert(child_receipt.target() == receipt.target());
        }
        assert(loaded_split_ready(child_receipt, read_nodes, split_arg));
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        receipt_path_valid_for_split(
            disk,
            child_branch,
            ranking,
            reads,
            child_receipt,
            split_arg,
            new_child_addr,
        );
        assert(path.subpath() == Path{
            branch: child_branch,
            key: split_arg.get_pivot(),
            depth: child_receipt.depth(),
        });
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().disk_view == branch.disk_view);
        assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
    }
}

pub proof fn receipt_path_valid_for_split_from_loaded(
    branch: LinkedBranch<Summary>,
    ranking: Ranking,
    read_nodes: LoadedBranch,
    receipt: LoadedPathReceipt,
    split_arg: SplitArg,
    new_child_addr: Address,
)
    requires
        branch.inv_internal(ranking),
        receipt.root == branch.root,
        loaded_split_ready(receipt, read_nodes, split_arg),
        branch.disk_view.is_fresh(set!{new_child_addr}),
        forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr)
            && read_nodes.contains_key(addr)
            ==> branch.disk_view.entries[addr] == read_nodes[addr],
    ensures
        ({
            let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
            &&& path.valid()
            &&& path.target().root == receipt.target().addr
            &&& path.target().root() == receipt.target().node
            &&& path.target().disk_view == branch.disk_view
            &&& path.target().can_split_child_of_index(split_arg, new_child_addr)
        }),
    decreases receipt.depth(),
{
    let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
    let root = branch.root;

    assert(receipt.valid_for(receipt.root, read_nodes));
    assert(receipt.key == split_arg.get_pivot());
    assert(receipt.needed_addrs().contains(root)) by {
        assert(receipt.lines[0].addr == receipt.root);
    }
    assert(read_nodes.contains_key(root));
    assert(branch.disk_view.entries.contains_key(root));
    assert(read_nodes[root] == branch.disk_view.entries[root]);
    assert(receipt.lines[0].node == branch.root());

    if receipt.depth() == 0 {
        assert(receipt.lines.len() == 1);
        assert(receipt.target() == receipt.lines[0]);
        assert(path.valid());
        assert(path.target() == branch);
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().root() is Index);
        let child_idx = path.target().root().route(split_arg.get_pivot()) + 1;
        LinkedBranchRefinement::lemma_route_ensures(path.target().root(), split_arg.get_pivot());
        assert(path.target().root().valid_child_index(child_idx));
        assert(path.target().root()->children[child_idx] == receipt.child_addr());
        let child_branch = path.target().child_at_idx(child_idx);
        assert(child_branch.root == receipt.child_addr());
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        assert(child_branch.disk_view.entries.contains_key(child_branch.root));
        assert(read_nodes.contains_key(receipt.child_addr()));
        assert(read_nodes[receipt.child_addr()] == branch.disk_view.entries[receipt.child_addr()]);
        assert(child_branch.root() == read_nodes[receipt.child_addr()]);
        assert(child_branch.has_root()) by {
            assert(loaded_line_wf(read_nodes, receipt.child_addr()));
            assert(!(read_nodes[receipt.child_addr()] is Auxiliary));
        }
        assert(split_arg.wf(child_branch)) by {
            assert(split_arg_matches_child(read_nodes[receipt.child_addr()], split_arg));
            assert(child_branch.root() == read_nodes[receipt.child_addr()]);
        }
        assert(child_branch.disk_view.is_fresh(set!{new_child_addr}));
        assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
    } else {
        assert(receipt.lines.len() > 1);
        assert(receipt.lines[0].node is Index);
        assert(branch.root() is Index);
        let child_idx = branch.root().route(receipt.key) + 1;
        LinkedBranchRefinement::lemma_route_ensures(branch.root(), receipt.key);
        assert(branch.root().valid_child_index(child_idx));
        let child_branch = branch.child_at_idx(child_idx);
        let child_receipt = receipt.tail();
        receipt_valid_implies_tail_valid(receipt, read_nodes);
        assert(child_branch.root == child_receipt.root) by {
            assert(receipt.lines[0].node->children[child_idx] == receipt.lines[1].addr);
            assert(branch.root()->children[child_idx] == receipt.lines[1].addr);
            assert(child_branch.root == branch.root()->children[child_idx]);
            assert(child_receipt.root == receipt.lines[1].addr);
        }
        assert(child_receipt.target() == receipt.target()) by {
            assert(child_receipt.lines.last() == receipt.lines.last());
        }
        assert(child_receipt.child_addr() == receipt.child_addr()) by {
            assert(child_receipt.target() == receipt.target());
        }
        assert(loaded_split_ready(child_receipt, read_nodes, split_arg));
        child_branch_inv_internal_from_parent(branch, ranking, child_idx);
        assert forall |addr: Address| #[trigger] child_branch.disk_view.entries.contains_key(addr)
            && read_nodes.contains_key(addr)
            implies child_branch.disk_view.entries[addr] == read_nodes[addr] by {
            assert(child_branch.disk_view == branch.disk_view);
        }
        receipt_path_valid_for_split_from_loaded(
            child_branch,
            ranking,
            read_nodes,
            child_receipt,
            split_arg,
            new_child_addr,
        );
        assert(path.subpath() == Path{
            branch: child_branch,
            key: split_arg.get_pivot(),
            depth: child_receipt.depth(),
        });
        assert(path.valid());
        assert(path.target() == path.subpath().target());
        assert(path.target().root == receipt.target().addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().disk_view == branch.disk_view);
        assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
    }
}

proof fn mini_allocator_all_minus_removable_is_reserved(mini_allocator: MiniAllocator)
    requires
        mini_allocator.wf(),
    ensures
        mini_allocator.all_aus().difference(mini_allocator.removable_aus())
            == mini_allocator.reserved_aus(),
{
    assert(mini_allocator.all_aus().difference(mini_allocator.removable_aus())
        =~= mini_allocator.reserved_aus()) by {
        assert forall |au: AU|
            #[trigger] mini_allocator.all_aus().difference(mini_allocator.removable_aus()).contains(au)
            <==> mini_allocator.reserved_aus().contains(au)
        by {
            if mini_allocator.all_aus().difference(mini_allocator.removable_aus()).contains(au) {
                assert(mini_allocator.allocs.contains_key(au));
                assert(!mini_allocator.removable_aus().contains(au));
                assert(!mini_allocator.can_remove(au));
                if mini_allocator.allocs[au].has_no_outstanding_refs() {
                    assert(mini_allocator.can_remove(au));
                    assert(false);
                }
            } else if mini_allocator.reserved_aus().contains(au) {
                assert(mini_allocator.allocs.contains_key(au));
                assert(!mini_allocator.allocs[au].has_no_outstanding_refs());
                assert(!mini_allocator.can_remove(au));
                assert(!mini_allocator.removable_aus().contains(au));
            }
        }
    };
}

pub open spec fn active_query_roots(active_branch: CachedBranch::State) -> Seq<Address>
{
    if active_branch.root is Some {
        seq![active_branch.root.unwrap()]
    } else {
        seq![]
    }
}

pub open spec fn query_roots(sealed_roots: Seq<Address>, active_branch: CachedBranch::State) -> Seq<Address>
{
    sealed_roots + active_query_roots(active_branch)
}

pub open spec fn query_receipts_valid(
    roots: Seq<Address>,
    receipts: Seq<LoadedPathReceipt>,
    read_nodes: LoadedBranch,
    key: Key,
) -> bool
{
    &&& receipts.len() <= roots.len()
    &&& forall |i: int| #![trigger receipts[i]] 0 <= i < receipts.len()
        ==> {
            let receipt = receipts[i];
            let root_idx = roots.len() as int - receipts.len() as int + i;
            &&& receipt.key == key
            &&& receipt.valid_for(roots[root_idx], read_nodes)
            &&& receipt.target().node is Leaf
    }
    &&& receipts.len() < roots.len() ==>
        query_from_receipts_up_to(receipts, receipts.len() as nat) is Define
}

pub open spec fn query_from_receipts_up_to(
    receipts: Seq<LoadedPathReceipt>,
    end: nat,
) -> Message
    recommends
        end <= receipts.len(),
    decreases end
{
    if end == 0 {
        Message::Update{delta: nop_delta()}
    } else {
        let idx = (end - 1) as int;
        let branch_msg = receipts[idx].result();
        query_from_receipts_up_to(receipts, (end - 1) as nat).merge(branch_msg)
    }
}

pub open spec fn split_read_addrs(receipt: LoadedPathReceipt) -> Set<Address>
    recommends
        receipt.lines.len() > 0,
        receipt.target().node is Index,
{
    receipt.needed_addrs().insert(receipt.child_addr())
}

pub open spec fn branch_summary_reads_valid(
    sealed_roots: Seq<Address>,
    read_nodes: LoadedBranch,
) -> bool
{
    forall |i: int| #![trigger sealed_roots[i]]
        0 <= i < sealed_roots.len()
        ==> root_summary_read_valid(sealed_roots[i], read_nodes)
}

pub open spec fn branch_summary_from_reads_up_to(
    sealed_roots: Seq<Address>,
    read_nodes: LoadedBranch,
    end: nat,
) -> Map<AU, Summary>
    recommends
        end <= sealed_roots.len(),
        branch_summary_reads_valid(sealed_roots, read_nodes),
    decreases end
{
    if end == 0 {
        Map::empty()
    } else {
        let idx = (end - 1) as int;
        let root = sealed_roots[idx];
        branch_summary_from_reads_up_to(sealed_roots, read_nodes, (end - 1) as nat)
            .insert(root.au, root_summary_from_read(root, read_nodes))
    }
}

pub open spec fn completed_branch_summary_from_reads(
    sealed_roots: Seq<Address>,
    read_nodes: LoadedBranch,
) -> Map<AU, Summary>
    recommends
        branch_summary_reads_valid(sealed_roots, read_nodes),
{
    branch_summary_from_reads_up_to(sealed_roots, read_nodes, sealed_roots.len() as nat)
}

pub open spec fn loaded_branch_summary_agrees(
    sealed_roots: Seq<Address>,
    read_nodes: LoadedBranch,
    branch_summary: Map<AU, Summary>,
) -> bool
{
    &&& branch_summary.dom() <= root_aus_up_to(sealed_roots, sealed_roots.len() as nat)
    &&& forall |i: int| #![trigger sealed_roots[i]]
        0 <= i < sealed_roots.len() && branch_summary.contains_key(sealed_roots[i].au)
        ==> {
            &&& root_summary_read_valid(sealed_roots[i], read_nodes)
            &&& branch_summary[sealed_roots[i].au]
                == root_summary_from_read(sealed_roots[i], read_nodes)
        }
}

pub proof fn branch_summary_from_reads_up_to_ensures(
    sealed_roots: Seq<Address>,
    read_nodes: LoadedBranch,
    branch_summary: Map<AU, Summary>,
    end: nat,
)
    requires
        end <= sealed_roots.len(),
        crate::disk::GenericDisk_v::set_addrs_disjoint_aus(sealed_roots.to_set()),
        branch_summary_reads_valid(sealed_roots, read_nodes),
        forall |i: int| 0 <= i < end ==> {
            &&& branch_summary.contains_key(sealed_roots[i].au)
            &&& root_summary_from_read(sealed_roots[i], read_nodes)
                == branch_summary[sealed_roots[i].au]
        },
    ensures
        branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom()
            =~= root_aus_up_to(sealed_roots, end),
        forall |i: int| 0 <= i < end ==>
            #[trigger] branch_summary_from_reads_up_to(sealed_roots, read_nodes, end)
                [sealed_roots[i].au] == branch_summary[sealed_roots[i].au],
    decreases end
{
    if end == 0 {
        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom()
            =~= Set::<AU>::empty());
    } else {
        let idx = (end - 1) as int;
        let root = sealed_roots[idx];
        branch_summary_from_reads_up_to_ensures(
            sealed_roots,
            read_nodes,
            branch_summary,
            (end - 1) as nat,
        );
        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom()
            =~= root_aus_up_to(sealed_roots, end)) by {
            assert_maps_equal!(
                branch_summary_from_reads_up_to(sealed_roots, read_nodes, end),
                branch_summary_from_reads_up_to(sealed_roots, read_nodes, end),
                au => {}
            );
            assert forall |au: AU|
                #[trigger] branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom().contains(au)
                <==> root_aus_up_to(sealed_roots, end).contains(au)
            by {
                if branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom().contains(au) {
                    if au == root.au {
                    } else {
                        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, (end - 1) as nat).dom().contains(au));
                        assert(root_aus_up_to(sealed_roots, (end - 1) as nat).contains(au));
                    }
                } else if root_aus_up_to(sealed_roots, end).contains(au) {
                    if au == root.au {
                        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).contains_key(au));
                    } else {
                        assert(root_aus_up_to(sealed_roots, (end - 1) as nat).contains(au));
                        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, (end - 1) as nat).dom().contains(au));
                    }
                }
            }
        };
        assert forall |i: int| 0 <= i < end implies
            #[trigger] branch_summary_from_reads_up_to(sealed_roots, read_nodes, end)
                [sealed_roots[i].au] == branch_summary[sealed_roots[i].au]
        by {
            if i == idx {
                assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end)[root.au]
                    == root_summary_from_read(root, read_nodes));
            } else {
                assert(0 <= i < end - 1);
                if sealed_roots[i].au == root.au {
                    assert(sealed_roots.to_set().contains(sealed_roots[i]));
                    assert(sealed_roots.to_set().contains(root));
                    if sealed_roots[i] != root {
                        assert(addrs_with_different_au(sealed_roots[i], root));
                        assert(sealed_roots[i].au != root.au);
                        assert(false);
                    }
                    assert(root_summary_from_read(sealed_roots[i], read_nodes)
                        == root_summary_from_read(root, read_nodes));
                } else {
                    assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end)[sealed_roots[i].au]
                        == branch_summary_from_reads_up_to(sealed_roots, read_nodes, (end - 1) as nat)[sealed_roots[i].au]);
                }
            }
        };
    }
}

pub proof fn branch_summary_from_reads_up_to_self_ensures(
    sealed_roots: Seq<Address>,
    read_nodes: LoadedBranch,
    end: nat,
)
    requires
        end <= sealed_roots.len(),
        crate::disk::GenericDisk_v::set_addrs_disjoint_aus(sealed_roots.to_set()),
        branch_summary_reads_valid(sealed_roots, read_nodes),
    ensures
        branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom()
            =~= root_aus_up_to(sealed_roots, end),
        forall |i: int| 0 <= i < end ==>
            #[trigger] branch_summary_from_reads_up_to(sealed_roots, read_nodes, end)
                [sealed_roots[i].au] == root_summary_from_read(sealed_roots[i], read_nodes),
    decreases end
{
    if end == 0 {
        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom()
            =~= Set::<AU>::empty());
    } else {
        let idx = (end - 1) as int;
        let root = sealed_roots[idx];
        branch_summary_from_reads_up_to_self_ensures(
            sealed_roots,
            read_nodes,
            (end - 1) as nat,
        );
        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom()
            =~= root_aus_up_to(sealed_roots, end)) by {
            assert forall |au: AU|
                #[trigger] branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom().contains(au)
                <==> root_aus_up_to(sealed_roots, end).contains(au)
            by {
                if branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).dom().contains(au) {
                    if au == root.au {
                    } else {
                        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, (end - 1) as nat).dom().contains(au));
                        assert(root_aus_up_to(sealed_roots, (end - 1) as nat).contains(au));
                    }
                } else if root_aus_up_to(sealed_roots, end).contains(au) {
                    if au == root.au {
                        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end).contains_key(au));
                    } else {
                        assert(root_aus_up_to(sealed_roots, (end - 1) as nat).contains(au));
                        assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, (end - 1) as nat).dom().contains(au));
                    }
                }
            }
        };
        assert forall |i: int| 0 <= i < end implies
            #[trigger] branch_summary_from_reads_up_to(sealed_roots, read_nodes, end)
                [sealed_roots[i].au] == root_summary_from_read(sealed_roots[i], read_nodes)
        by {
            if i == idx {
                assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end)[root.au]
                    == root_summary_from_read(root, read_nodes));
            } else {
                assert(0 <= i < end - 1);
                if sealed_roots[i].au == root.au {
                    assert(sealed_roots.to_set().contains(sealed_roots[i]));
                    assert(sealed_roots.to_set().contains(root));
                    if sealed_roots[i] != root {
                        assert(addrs_with_different_au(sealed_roots[i], root));
                        assert(sealed_roots[i].au != root.au);
                        assert(false);
                    }
                } else {
                    assert(branch_summary_from_reads_up_to(sealed_roots, read_nodes, end)[sealed_roots[i].au]
                        == branch_summary_from_reads_up_to(sealed_roots, read_nodes, (end - 1) as nat)[sealed_roots[i].au]);
                }
            }
        };
    }
}

#[verifier::ext_equal]
pub struct CachingDiskBranchMetadata {
    pub sealed_roots: Seq<Address>,
    pub seq_end: nat,
}

#[verifier::ext_equal]
pub struct CachingDiskBranchImage {
    pub persistent: Map<Address, RawPage>,
    pub sealed_roots: Seq<Address>,
    pub seq_end: nat,
}

impl CachingDiskBranchImage {
    pub open spec fn persistent_branch_nodes(self) -> LoadedBranch {
        to_branch_nodes(self.persistent)
    }

    pub open spec fn branch_summary(self) -> Map<AU, Summary>
        recommends branch_summary_reads_valid(self.sealed_roots, self.persistent_branch_nodes())
    {
        branch_summary_from_reads_up_to(
            self.sealed_roots,
            self.persistent_branch_nodes(),
            self.sealed_roots.len() as nat,
        )
    }

    pub open spec fn live_persistent_aus(self) -> Set<AU>
        recommends branch_summary_reads_valid(self.sealed_roots, self.persistent_branch_nodes())
    {
        summary_aus(self.branch_summary())
    }

    pub open spec fn live_persistent(self) -> Map<Address, RawPage>
        recommends branch_summary_reads_valid(self.sealed_roots, self.persistent_branch_nodes())
    {
        self.persistent.restrict(addresses_in_aus(self.live_persistent_aus()))
    }

    pub open spec fn loadable(self) -> bool {
        branch_summary_reads_valid(self.sealed_roots, self.persistent_branch_nodes())
    }

    pub open spec fn stack_wf(self) -> bool {
        &&& branch_summary_reads_valid(self.sealed_roots, self.persistent_branch_nodes())
        &&& self.sealed_stack_i().wf(self.branch_summary())
    }

    pub open spec fn wf(self) -> bool {
        &&& self.loadable()
        &&& self.stack_wf()
    }

    pub proof fn branch_summary_finite(self)
        requires
            self.stack_wf(),
        ensures
            self.branch_summary().dom().finite(),
            self.branch_summary().values().finite(),
    {
        let summary = self.branch_summary();
        assert(self.sealed_stack_i().wf(summary));
        to_aus_finite(self.sealed_roots.to_set());
        assert(summary.dom() == to_aus(self.sealed_roots.to_set()));
        assert(summary.dom().finite());
        lemma_values_finite(summary);
    }

    pub proof fn index_root_aux_in_summary(self, root: Address, aux: Address)
        requires
            self.stack_wf(),
            self.sealed_roots.to_set().contains(root),
            self.persistent_branch_nodes().contains_key(root),
            self.persistent_branch_nodes()[root] is Index,
            self.persistent_branch_nodes()[root]->aux_ptr == Some(aux),
        ensures
            self.branch_summary().contains_key(root.au),
            self.branch_summary()[root.au].contains(aux.au),
            summary_aus(self.branch_summary()).contains(aux.au),
    {
        let summary = self.branch_summary();
        assert(self.sealed_stack_i().wf(summary));
        self.sealed_stack_i().root_au_in_summary(summary, root);
        self.sealed_stack_i().tight_branch_facts(summary, root);
        let branch = self.sealed_stack_i().tight_branch(root, summary[root.au]);
        assert(tight_branch_in_loose_disk(
            self.sealed_stack_i().sealed_disk,
            root,
            summary[root.au],
            branch,
        ));
        assert(branch.disk_view.entries.contains_key(root));
        assert(branch.disk_view.entries[root] == branch.root());
        assert(branch.disk_view.entries <= self.sealed_stack_i().sealed_disk.entries);
        assert(self.sealed_stack_i().sealed_disk.entries.contains_key(root));
        assert(self.sealed_stack_i().sealed_disk.entries[root] == branch.disk_view.entries[root]);
        assert(self.sealed_stack_i().sealed_disk.entries[root] == self.persistent_branch_nodes()[root]) by {
            assert(summary_aus(summary).contains(root.au));
            assert(self.live_persistent().contains_key(root));
        };
        assert(branch.root() == self.persistent_branch_nodes()[root]);
        assert(branch.root() is Index);
        assert(branch.root()->aux_ptr == Some(aux));
        assert(branch.sealed_root());
        assert(branch.disk_view.valid_address(aux));
        assert(branch.disk_view.entries.contains_key(aux));
        assert(branch.full_repr().contains(aux));
        assert(addrs_closed(branch.full_repr(), branch.get_summary()));
        assert(branch.get_summary() == summary[root.au]);
        assert(summary[root.au].contains(aux.au));
        self.branch_summary_finite();
        assert(summary.values().contains(summary[root.au]));
        lemma_union_set_of_sets_subset(summary.values(), summary[root.au]);
    }

    pub open spec fn sealed_stack_i(self) -> SealedAllocationBranchStack {
        SealedAllocationBranchStack{
            sealed_roots: self.sealed_roots,
            sealed_disk: BufferDisk{entries: to_branch_nodes(self.live_persistent())},
        }
    }

    pub proof fn write_outside_summary_aus_preserves_sealed_stack(
        pre: Self,
        post: Self,
        addr: Address,
        data: RawPage,
    )
        requires
            pre.wf(),
            post.sealed_roots == pre.sealed_roots,
            post.seq_end == pre.seq_end,
            post.persistent == pre.persistent.insert(addr, data),
            !addresses_in_aus(summary_aus(pre.branch_summary())).contains(addr),
        ensures
            post.wf(),
            post.branch_summary() == pre.branch_summary(),
            post.live_persistent() == pre.live_persistent(),
            post.sealed_stack_i() == pre.sealed_stack_i(),
    {
        let pre_summary = pre.branch_summary();
        let pre_nodes = pre.persistent_branch_nodes();
        let post_nodes = post.persistent_branch_nodes();
        pre.branch_summary_finite();

        assert(branch_summary_reads_valid(post.sealed_roots, post_nodes)) by {
            assert forall |i: int| #![trigger post.sealed_roots[i]]
                0 <= i < post.sealed_roots.len()
                implies root_summary_read_valid(post.sealed_roots[i], post_nodes)
            by {
                let root = post.sealed_roots[i];
                assert(pre.sealed_roots[i] == root);
                assert(root_summary_read_valid(root, pre_nodes));
                assert(pre_summary.contains_key(root.au)) by {
                    assert(pre.sealed_stack_i().wf(pre_summary));
                    assert(pre.sealed_roots.to_set().contains(root));
                    pre.sealed_stack_i().root_au_in_summary(pre_summary, root);
                }
                assert(pre.sealed_roots.to_set().contains(root));
                pre.sealed_stack_i().root_au_in_summary(pre_summary, root);
                assert(pre_summary[root.au].contains(root.au));
                assert(pre_summary.values().finite());
                assert(summary_aus(pre_summary).contains(root.au)) by {
                    assert(pre_summary.values().contains(pre_summary[root.au]));
                    lemma_union_set_of_sets_subset(pre_summary.values(), pre_summary[root.au]);
                }
                assert(addr != root);
                assert(post.persistent[root] == pre.persistent[root]);
                assert(post_nodes[root] == pre_nodes[root]);
                if pre_nodes[root] is Index {
                    let aux = pre_nodes[root]->aux_ptr.unwrap();
                    assert(pre_nodes.contains_key(aux));
                    assert(pre_nodes[aux] is Auxiliary);
                    pre.index_root_aux_in_summary(root, aux);
                    assert(pre_summary[root.au].contains(aux.au));
                    assert(pre_summary.values().finite());
                    assert(summary_aus(pre_summary).contains(aux.au)) by {
                        assert(pre_summary.values().contains(pre_summary[root.au]));
                        lemma_union_set_of_sets_subset(pre_summary.values(), pre_summary[root.au]);
                    }
                    assert(addr != aux);
                    assert(post.persistent[aux] == pre.persistent[aux]);
                    assert(post_nodes[aux] == pre_nodes[aux]);
                }
            }
        }

        assert forall |i: int| #![trigger post.sealed_roots[i]]
            0 <= i < post.sealed_roots.len()
            implies root_summary_from_read(post.sealed_roots[i], post_nodes)
                == root_summary_from_read(pre.sealed_roots[i], pre_nodes)
        by {
            let root = post.sealed_roots[i];
            assert(pre.sealed_roots[i] == root);
            assert(root_summary_read_valid(root, post_nodes));
            assert(root_summary_read_valid(root, pre_nodes));
            assert(pre_summary.contains_key(root.au)) by {
                assert(pre.sealed_roots.to_set().contains(root));
                pre.sealed_stack_i().root_au_in_summary(pre_summary, root);
            }
            assert(pre_summary[root.au].contains(root.au)) by {
                pre.sealed_stack_i().root_au_in_summary(pre_summary, root);
            }
            assert(pre_summary.values().finite());
            assert(summary_aus(pre_summary).contains(root.au)) by {
                assert(pre_summary.values().contains(pre_summary[root.au]));
                lemma_union_set_of_sets_subset(pre_summary.values(), pre_summary[root.au]);
            }
            assert(addr != root);
            assert(post_nodes[root] == pre_nodes[root]);
            if pre_nodes[root] is Index {
                let aux = pre_nodes[root]->aux_ptr.unwrap();
                pre.index_root_aux_in_summary(root, aux);
                assert(pre_summary[root.au].contains(aux.au));
                assert(summary_aus(pre_summary).contains(aux.au)) by {
                    assert(pre_summary.values().contains(pre_summary[root.au]));
                    lemma_union_set_of_sets_subset(pre_summary.values(), pre_summary[root.au]);
                }
                assert(addr != aux);
                assert(post_nodes[aux] == pre_nodes[aux]);
            }
        }

        assert(post.branch_summary() == pre.branch_summary()) by {
            assert(pre_summary.values().finite());
            assert(crate::disk::GenericDisk_v::set_addrs_disjoint_aus(pre.sealed_roots.to_set()));
            branch_summary_from_reads_up_to_self_ensures(
                pre.sealed_roots,
                post_nodes,
                pre.sealed_roots.len() as nat,
            );
            branch_summary_from_reads_up_to_self_ensures(
                pre.sealed_roots,
                pre_nodes,
                pre.sealed_roots.len() as nat,
            );
            assert_maps_equal!(post.branch_summary(), pre.branch_summary(), au => {
                if post.branch_summary().contains_key(au) {
                    assert(root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat).contains(au));
                    let idx = root_aus_up_to_member_has_index(
                        pre.sealed_roots,
                        pre.sealed_roots.len() as nat,
                        au,
                    );
                    assert(post.branch_summary()[au]
                        == root_summary_from_read(pre.sealed_roots[idx], post_nodes));
                    assert(pre.branch_summary()[au]
                        == root_summary_from_read(pre.sealed_roots[idx], pre_nodes));
                }
                if pre.branch_summary().contains_key(au) {
                    assert(root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat).contains(au));
                    let idx = root_aus_up_to_member_has_index(
                        pre.sealed_roots,
                        pre.sealed_roots.len() as nat,
                        au,
                    );
                    assert(post.branch_summary()[au]
                        == root_summary_from_read(pre.sealed_roots[idx], post_nodes));
                    assert(pre.branch_summary()[au]
                        == root_summary_from_read(pre.sealed_roots[idx], pre_nodes));
                }
            });
        }

        assert(post.live_persistent() == pre.live_persistent()) by {
            assert_maps_equal!(post.live_persistent(), pre.live_persistent(), a => {
                assert(post.branch_summary() == pre.branch_summary());
                if addresses_in_aus(summary_aus(pre_summary)).contains(a) {
                    assert(a != addr);
                    assert(post.persistent[a] == pre.persistent[a]);
                }
            });
        }
        assert(post.sealed_stack_i() == pre.sealed_stack_i());
        assert(post.stack_wf()) by {
            assert(post.branch_summary() == pre.branch_summary());
            assert(post.sealed_stack_i() == pre.sealed_stack_i());
            assert(pre.stack_wf());
        }
        assert(post.wf());
    }

    pub proof fn same_summary_aus_preserves_sealed_stack(
        pre: Self,
        post: Self,
    )
        requires
            pre.wf(),
            post.sealed_roots == pre.sealed_roots,
            post.seq_end == pre.seq_end,
            post.persistent.restrict(addresses_in_aus(summary_aus(pre.branch_summary())))
                == pre.persistent.restrict(addresses_in_aus(summary_aus(pre.branch_summary()))),
        ensures
            post.wf(),
            post.branch_summary() == pre.branch_summary(),
            post.live_persistent() == pre.live_persistent(),
            post.sealed_stack_i() == pre.sealed_stack_i(),
    {
        let pre_summary = pre.branch_summary();
        let pre_nodes = pre.persistent_branch_nodes();
        let post_nodes = post.persistent_branch_nodes();
        let summary_addrs = addresses_in_aus(summary_aus(pre_summary));
        pre.branch_summary_finite();
        assert(post.persistent.restrict(summary_addrs)
            == pre.persistent.restrict(summary_addrs));

        assert(branch_summary_reads_valid(post.sealed_roots, post_nodes)) by {
            assert forall |i: int| #![trigger post.sealed_roots[i]]
                0 <= i < post.sealed_roots.len()
                implies root_summary_read_valid(post.sealed_roots[i], post_nodes)
            by {
                let root = post.sealed_roots[i];
                assert(pre.sealed_roots[i] == root);
                assert(root_summary_read_valid(root, pre_nodes));
                assert(pre.sealed_roots.to_set().contains(root));
                pre.sealed_stack_i().root_au_in_summary(pre_summary, root);
                assert(pre_summary[root.au].contains(root.au));
                assert(pre_summary.values().finite());
                assert(summary_aus(pre_summary).contains(root.au)) by {
                    assert(pre_summary.values().contains(pre_summary[root.au]));
                    lemma_union_set_of_sets_subset(pre_summary.values(), pre_summary[root.au]);
                }
                assert(summary_addrs.contains(root));
                assert(pre.persistent.contains_key(root));
                assert(pre.persistent.restrict(summary_addrs).contains_key(root));
                assert(post.persistent.restrict(summary_addrs).contains_key(root));
                assert(post.persistent.contains_key(root));
                assert(post.persistent.restrict(summary_addrs)[root]
                    == pre.persistent.restrict(summary_addrs)[root]);
                assert(post.persistent.restrict(summary_addrs)[root] == post.persistent[root]);
                assert(pre.persistent.restrict(summary_addrs)[root] == pre.persistent[root]);
                assert(post.persistent[root] == pre.persistent[root]);
                assert(post_nodes[root] == pre_nodes[root]);
                if pre_nodes[root] is Index {
                    let aux = pre_nodes[root]->aux_ptr.unwrap();
                    pre.index_root_aux_in_summary(root, aux);
                    assert(pre_summary[root.au].contains(aux.au));
                    assert(summary_aus(pre_summary).contains(aux.au)) by {
                        assert(pre_summary.values().contains(pre_summary[root.au]));
                        lemma_union_set_of_sets_subset(pre_summary.values(), pre_summary[root.au]);
                    }
                    assert(summary_addrs.contains(aux));
                    assert(pre.persistent.contains_key(aux));
                    assert(pre.persistent.restrict(summary_addrs).contains_key(aux));
                    assert(post.persistent.restrict(summary_addrs).contains_key(aux));
                    assert(post.persistent.contains_key(aux));
                    assert(post.persistent.restrict(summary_addrs)[aux]
                        == pre.persistent.restrict(summary_addrs)[aux]);
                    assert(post.persistent.restrict(summary_addrs)[aux] == post.persistent[aux]);
                    assert(pre.persistent.restrict(summary_addrs)[aux] == pre.persistent[aux]);
                    assert(post.persistent[aux] == pre.persistent[aux]);
                    assert(post_nodes[aux] == pre_nodes[aux]);
                }
            }
        }

        assert forall |i: int| #![trigger post.sealed_roots[i]]
            0 <= i < post.sealed_roots.len()
            implies root_summary_from_read(post.sealed_roots[i], post_nodes)
                == root_summary_from_read(pre.sealed_roots[i], pre_nodes)
        by {
            let root = post.sealed_roots[i];
            assert(pre.sealed_roots[i] == root);
            assert(root_summary_read_valid(root, post_nodes));
            assert(root_summary_read_valid(root, pre_nodes));
            pre.sealed_stack_i().root_au_in_summary(pre_summary, root);
            assert(pre_summary[root.au].contains(root.au));
            assert(pre_summary.values().finite());
            assert(summary_aus(pre_summary).contains(root.au)) by {
                assert(pre_summary.values().contains(pre_summary[root.au]));
                lemma_union_set_of_sets_subset(pre_summary.values(), pre_summary[root.au]);
            }
            assert(summary_addrs.contains(root));
            assert(pre.persistent.contains_key(root));
            assert(pre.persistent.restrict(summary_addrs).contains_key(root));
            assert(post.persistent.restrict(summary_addrs).contains_key(root));
            assert(post.persistent.contains_key(root));
            assert(post.persistent.restrict(summary_addrs)[root]
                == pre.persistent.restrict(summary_addrs)[root]);
            assert(post.persistent.restrict(summary_addrs)[root] == post.persistent[root]);
            assert(pre.persistent.restrict(summary_addrs)[root] == pre.persistent[root]);
            assert(post.persistent[root] == pre.persistent[root]);
            assert(post_nodes[root] == pre_nodes[root]);
            if pre_nodes[root] is Index {
                let aux = pre_nodes[root]->aux_ptr.unwrap();
                pre.index_root_aux_in_summary(root, aux);
                assert(pre_summary[root.au].contains(aux.au));
                assert(summary_aus(pre_summary).contains(aux.au)) by {
                    assert(pre_summary.values().contains(pre_summary[root.au]));
                    lemma_union_set_of_sets_subset(pre_summary.values(), pre_summary[root.au]);
                }
                assert(summary_addrs.contains(aux));
                assert(pre.persistent.contains_key(aux));
                assert(pre.persistent.restrict(summary_addrs).contains_key(aux));
                assert(post.persistent.restrict(summary_addrs).contains_key(aux));
                assert(post.persistent.contains_key(aux));
                assert(post.persistent.restrict(summary_addrs)[aux]
                    == pre.persistent.restrict(summary_addrs)[aux]);
                assert(post.persistent.restrict(summary_addrs)[aux] == post.persistent[aux]);
                assert(pre.persistent.restrict(summary_addrs)[aux] == pre.persistent[aux]);
                assert(post.persistent[aux] == pre.persistent[aux]);
                assert(post_nodes[aux] == pre_nodes[aux]);
            }
        }

        assert(post.branch_summary() == pre.branch_summary()) by {
            pre.sealed_stack_i().sealed_disk.build_branch_summary_finite(pre.sealed_roots.to_set());
            assert(crate::disk::GenericDisk_v::set_addrs_disjoint_aus(pre.sealed_roots.to_set()));
            branch_summary_from_reads_up_to_self_ensures(
                pre.sealed_roots,
                post_nodes,
                pre.sealed_roots.len() as nat,
            );
            branch_summary_from_reads_up_to_self_ensures(
                pre.sealed_roots,
                pre_nodes,
                pre.sealed_roots.len() as nat,
            );
            assert_maps_equal!(post.branch_summary(), pre.branch_summary(), au => {
                if post.branch_summary().contains_key(au) {
                    assert(root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat).contains(au));
                    let idx = root_aus_up_to_member_has_index(
                        pre.sealed_roots,
                        pre.sealed_roots.len() as nat,
                        au,
                    );
                    assert(post.branch_summary()[au]
                        == root_summary_from_read(pre.sealed_roots[idx], post_nodes));
                    assert(pre.branch_summary()[au]
                        == root_summary_from_read(pre.sealed_roots[idx], pre_nodes));
                }
                if pre.branch_summary().contains_key(au) {
                    assert(root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat).contains(au));
                    let idx = root_aus_up_to_member_has_index(
                        pre.sealed_roots,
                        pre.sealed_roots.len() as nat,
                        au,
                    );
                    assert(post.branch_summary()[au]
                        == root_summary_from_read(pre.sealed_roots[idx], post_nodes));
                    assert(pre.branch_summary()[au]
                        == root_summary_from_read(pre.sealed_roots[idx], pre_nodes));
                }
            });
        }

        assert(post.live_persistent() == pre.live_persistent()) by {
            assert_maps_equal!(post.live_persistent(), pre.live_persistent(), a => {
                assert(post.branch_summary() == pre.branch_summary());
                if summary_addrs.contains(a) {
                    if pre.live_persistent().contains_key(a) {
                        assert(pre.persistent.contains_key(a));
                        assert(pre.persistent.restrict(summary_addrs).contains_key(a));
                        assert(post.persistent.restrict(summary_addrs).contains_key(a));
                        assert(post.persistent.contains_key(a));
                        assert(post.persistent.restrict(summary_addrs)[a]
                            == pre.persistent.restrict(summary_addrs)[a]);
                        assert(post.persistent.restrict(summary_addrs)[a] == post.persistent[a]);
                        assert(pre.persistent.restrict(summary_addrs)[a] == pre.persistent[a]);
                    }
                    if post.live_persistent().contains_key(a) {
                        assert(post.persistent.contains_key(a));
                        assert(post.persistent.restrict(summary_addrs).contains_key(a));
                        assert(pre.persistent.restrict(summary_addrs).contains_key(a));
                        assert(pre.persistent.contains_key(a));
                        assert(post.persistent.restrict(summary_addrs)[a]
                            == pre.persistent.restrict(summary_addrs)[a]);
                        assert(post.persistent.restrict(summary_addrs)[a] == post.persistent[a]);
                        assert(pre.persistent.restrict(summary_addrs)[a] == pre.persistent[a]);
                    }
                }
            });
        }
        assert(post.sealed_stack_i() == pre.sealed_stack_i());
        assert(post.stack_wf()) by {
            assert(post.branch_summary() == pre.branch_summary());
            assert(post.sealed_stack_i() == pre.sealed_stack_i());
            assert(pre.stack_wf());
        }
        assert(post.wf());
    }

    pub proof fn branch_summary_matches_stack(self)
        requires
            self.stack_wf(),
        ensures
            self.branch_summary() == self.branch_summary(),
    {
    }
}

pub open spec fn empty_caching_disk_branch_image() -> CachingDiskBranchImage {
    CachingDiskBranchImage{
        persistent: Map::empty(),
        sealed_roots: Seq::empty(),
        seq_end: 0,
    }
}

pub proof fn empty_caching_disk_branch_image_wf()
    ensures
        empty_caching_disk_branch_image().wf(),
{
    let image = empty_caching_disk_branch_image();
    let sealed_disk = BufferDisk{entries: to_branch_nodes(image.live_persistent())};
    let branch_summary = image.branch_summary();
    assert(image.sealed_roots.to_set() =~= Set::<Address>::empty());
    assert(branch_summary_reads_valid(image.sealed_roots, image.persistent_branch_nodes())) by {
        assert forall |i: int| #![trigger image.sealed_roots[i]]
            0 <= i < image.sealed_roots.len()
            implies root_summary_read_valid(image.sealed_roots[i], image.persistent_branch_nodes())
        by {
            assert(false);
        }
    }
    assert(image.branch_summary() =~= Map::<AU, Summary>::empty()) by {
        assert_maps_equal!(image.branch_summary(), Map::<AU, Summary>::empty(), au => {
            if image.branch_summary().contains_key(au) {
                assert(false);
            }
        });
    }
    assert(image.live_persistent() =~= Map::<Address, RawPage>::empty()) by {
        assert_maps_equal!(image.live_persistent(), Map::<Address, RawPage>::empty(), addr => {
            if image.live_persistent().contains_key(addr) {
                assert(image.persistent.contains_key(addr));
                assert(false);
            }
        });
    }
    assert(sealed_disk.entries =~= Map::<Address, BranchNode>::empty()) by {
        assert_maps_equal!(sealed_disk.entries, Map::<Address, BranchNode>::empty());
    }
    assert(sealed_disk.sealed_branch_roots(image.sealed_roots.to_set())) by {
        assert forall |root: Address| #[trigger] image.sealed_roots.to_set().contains(root)
            implies sealed_disk.get_branch(root).valid_sealed_branch()
        by {
            assert(false);
        }
    }
    sealed_disk.build_branch_domain(image.sealed_roots.to_set());
    assert(sealed_disk.build_branch_summary(image.sealed_roots.to_set()) =~= Map::<AU, Summary>::empty()) by {
        assert_maps_equal!(sealed_disk.build_branch_summary(image.sealed_roots.to_set()), Map::<AU, Summary>::empty(), au => {
            if sealed_disk.build_branch_summary(image.sealed_roots.to_set()).contains_key(au) {
                assert(sealed_disk.build_branch_summary(image.sealed_roots.to_set()).dom().contains(au));
                assert(false);
            }
        });
    }
    assert(branch_summary == sealed_disk.build_branch_summary(image.sealed_roots.to_set()));
    assert(branch_summary.dom() =~= Set::<AU>::empty());
    assert(branch_summary =~= Map::<AU, Summary>::empty()) by {
        assert_maps_equal!(branch_summary, Map::<AU, Summary>::empty(), au => {
            if branch_summary.contains_key(au) {
                assert(branch_summary.dom().contains(au));
                assert(false);
            }
        });
    }
    assert(map_with_disjoint_values(branch_summary)) by {
        assert forall |a: AU, b: AU| #[trigger] branch_summary.contains_key(a)
            && #[trigger] branch_summary.contains_key(b)
            && a != b
            implies branch_summary[a].disjoint(branch_summary[b])
        by {
            assert(false);
        }
    }
    assert(addrs_closed(sealed_disk.entries.dom(), summary_aus(branch_summary))) by {
        assert forall |addr: Address| #[trigger] sealed_disk.entries.dom().contains(addr)
            implies summary_aus(branch_summary).contains(addr.au)
        by {
            assert(false);
        }
    }
    assert(image.wf());
}

state_machine!{ CachingDiskBranch {
	    fields {
	        pub sealed_roots: Seq<Address>,
	        pub branch_summary: Map<AU, Summary>,
	        pub metadata_loaded: bool,
	        pub persisted_root_count: nat,
	        pub active_branch: CachedBranch::State,
	        pub mini_allocator: MiniAllocator,
	        pub disk: CachingDisk::State,
        pub seq_end: nat,
    }

    pub open spec fn visible_branch_nodes(self) -> LoadedBranch {
        to_branch_nodes(self.disk.visible())
    }

    pub open spec fn interpreted_branch_summary(self) -> Map<AU, Summary>
        recommends
            branch_summary_reads_valid(self.sealed_roots, self.visible_branch_nodes()),
    {
        completed_branch_summary_from_reads(self.sealed_roots, self.visible_branch_nodes())
    }

    pub open spec fn branch_metadata_loaded(self) -> bool {
        self.branch_summary == self.interpreted_branch_summary()
    }

    pub open spec fn loaded_branch_summary_agrees(self) -> bool {
        loaded_branch_summary_agrees(
            self.sealed_roots,
            self.visible_branch_nodes(),
            self.branch_summary,
        )
    }

    pub enum Label {
        QueryLabel{ key: Key, msg: Message },
        AppendLabel{ keys: Seq<Key>, msgs: Seq<Message> },
        FreezeAsLabel{ image: CachingDiskBranchMetadata },
        FreezePrepared{ image: CachingDiskBranchMetadata },
        LoadMetadata{ root: Address, discovered_aus: Set<AU> },
        Internal,
        InternalAlloc{ allocs: Set<AU>, deallocs: Set<AU> },
    }

    init!{ initialize(
        image: CachingDiskBranchImage,
    ) {
        require CachingDiskBranch::State::can_load_from_persistent(image);
        let loaded = CachingDiskBranch::State::load_from_persistent(image);

        init sealed_roots = loaded.sealed_roots;
        init branch_summary = loaded.branch_summary;
        init metadata_loaded = loaded.metadata_loaded;
        init persisted_root_count = loaded.persisted_root_count;
        init active_branch = loaded.active_branch;
        init mini_allocator = loaded.mini_allocator;
        init disk = loaded.disk;
        init seq_end = loaded.seq_end;
    }}

    transition!{ disk_internal(lbl: Label, new_disk: CachingDisk::State) {
        require lbl is Internal;
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Internal{},
        );

        update disk = new_disk;
    }}

    transition!{ observe_persisted_roots(lbl: Label, target_count: nat) {
        require lbl is Internal;
        require pre.metadata_loaded;
        require pre.persisted_root_count <= target_count;
        require target_count <= pre.sealed_roots.len();
        let aus = sealed_summary_aus_between(
            pre.sealed_roots,
            pre.branch_summary,
            pre.persisted_root_count,
            target_count,
        );
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::ObserveCleanAUs{aus},
        );

        update persisted_root_count = target_count;
    }}

    transition!{ load_metadata(
        lbl: Label,
        reads: Map<Address, RawPage>,
    ) {
        require let Label::LoadMetadata{root, discovered_aus} = lbl;
        require pre.sealed_roots.to_set().contains(root);
        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads, writes: Map::empty()},
        );

	        let read_nodes = to_branch_nodes(reads);
	        require root_summary_read_valid(root, read_nodes);
	        require discovered_aus == root_summary_from_read(root, read_nodes);
	        let new_branch_summary = pre.branch_summary.insert(root.au, discovered_aus);

	        update branch_summary = new_branch_summary;
	        update metadata_loaded =
	            root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat)
	                <= new_branch_summary.dom();
	    }}

    transition!{ query(
        lbl: Label,
        receipts: Seq<LoadedPathReceipt>,
        reads: Map<Address, RawPage>,
    ) {
	        require let Label::QueryLabel{key, msg} = lbl;
	        require pre.metadata_loaded;
	        require CachingDisk::State::next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads, writes: Map::empty()},
        );

        let read_nodes = to_branch_nodes(reads);
        let roots = query_roots(pre.sealed_roots, pre.active_branch);
        require query_receipts_valid(roots, receipts, read_nodes, key);
        require msg == query_from_receipts_up_to(receipts, receipts.len() as nat);
    }}

    transition!{ append(
        lbl: Label,
        new_disk: CachingDisk::State,
        new_active_branch: CachedBranch::State,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
	) {
        require let Label::AppendLabel{keys, msgs} = lbl;
        require pre.metadata_loaded;

        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Access{reads, writes},
        );

        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let init_addr = if init_root is Some { init_root.unwrap() } else { arbitrary() };
        let branch_lbl = if pre.active_branch.root is Some {
            CachedBranch::Label::Append{
                mini_allocator: pre.mini_allocator,
                receipt,
                keys,
                msgs,
                read_nodes,
                write_nodes,
            }
        } else {
            CachedBranch::Label::Initialize{
                mini_allocator: pre.mini_allocator,
                init_root: init_addr,
                keys,
                msgs,
                write_nodes,
            }
        };
        let new_mini_allocator = if pre.active_branch.root is Some {
            pre.mini_allocator
        } else {
            pre.mini_allocator.allocate(init_addr)
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);
        require (pre.active_branch.root is Some <==> init_root is None);

        update active_branch = new_active_branch;
        update mini_allocator = new_mini_allocator;
        update disk = new_disk;
        update seq_end = pre.seq_end + keys.len();
    }}

    transition!{ freeze_as(lbl: Label) {
        require let Label::FreezeAsLabel{image: frozen_image} = lbl;
        require pre.metadata_loaded;
        require pre.active_branch.root is None;
        require frozen_image == pre.freeze_metadata();
    }}

    transition!{ freeze_prepared(lbl: Label) {
        require let Label::FreezePrepared{image} = lbl;
        require image.sealed_roots.len() <= pre.persisted_root_count;
        require pre.sealed_roots.subrange(0, image.sealed_roots.len() as int) == image.sealed_roots;
    }}

    transition!{ internal_noop(lbl: Label) {
        require lbl is Internal;
    }}

    transition!{ internal_grow(
        lbl: Label,
        new_disk: CachingDisk::State,
        new_root_addr: Address,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) {
	        require lbl is Internal;
	        require pre.metadata_loaded;
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Access{reads, writes},
        );

        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let new_active_branch = CachedBranch::State{root: Some(new_root_addr)};
        let branch_lbl = CachedBranch::Label::Grow{
            mini_allocator: pre.mini_allocator,
            new_root_addr,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl);
        let new_mini_allocator = pre.mini_allocator.allocate(new_root_addr);

        update active_branch = new_active_branch;
        update mini_allocator = new_mini_allocator;
        update disk = new_disk;
    }}

    transition!{ internal_split(
        lbl: Label,
        new_disk: CachingDisk::State,
        new_child_addr: Address,
        receipt: LoadedPathReceipt,
        split_arg: SplitArg,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) {
	        require lbl is Internal;
	        require pre.metadata_loaded;
        require CachingDisk::State::next(
            pre.disk,
            new_disk,
            CachingDisk::Label::Access{reads, writes},
        );

        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = CachedBranch::Label::Split{
            mini_allocator: pre.mini_allocator,
            new_child_addr,
            receipt,
            split_arg,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, pre.active_branch, branch_lbl);

        require split_read_addrs(receipt) <= reads.dom();
        let new_mini_allocator = pre.mini_allocator.allocate(new_child_addr);

        update active_branch = pre.active_branch;
        update mini_allocator = new_mini_allocator;
        update disk = new_disk;
    }}

    transition!{ internal_seal(
        lbl: Label,
        written_disk: CachingDisk::State,
        aux_ptr: Pointer,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) {
	        require lbl is Internal;
	        require pre.metadata_loaded;
        require CachingDisk::State::next(
            pre.disk,
            written_disk,
            CachingDisk::Label::Access{reads, writes},
        );

        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = CachedBranch::Label::Seal{
            mini_allocator: pre.mini_allocator,
            aux_ptr,
            read_nodes,
            write_nodes,
        };
        require CachedBranch::State::next(pre.active_branch, pre.active_branch, branch_lbl);

        let sealed_root = pre.active_branch.root.unwrap();
        let sealed_summary = pre.mini_allocator.reserved_aus();
        let next_mini_allocator = pre.mini_allocator
            .prune(sealed_summary);
        let new_branch_summary = pre.branch_summary.insert(
            sealed_root.au,
            sealed_summary,
        );

        require reads.contains_key(sealed_root);

        update sealed_roots = pre.sealed_roots.push(sealed_root);
        update branch_summary = new_branch_summary;
        update active_branch = CachedBranch::State::empty_active();
        update mini_allocator = next_mini_allocator;
        update disk = written_disk;
    }}

    transition!{ internal_fill_au(lbl: Label, aus: Set<AU>, new_disk: CachingDisk::State) {
	        require let Label::InternalAlloc{allocs, deallocs} = lbl;
	        require pre.metadata_loaded;
        require allocs == aus;
        require deallocs == Set::<AU>::empty();
        let new_mini_allocator = pre.mini_allocator.add_aus(aus);
        require aus.disjoint(summary_aus(pre.branch_summary));
        require aus.disjoint(pre.mini_allocator.all_aus());
        require new_disk.inv();
        require pre.disk.cache <= new_disk.cache;
        require pre.disk.status <= new_disk.status;
        require pre.disk.persistent <= new_disk.persistent;
        require new_disk.cache.dom() <= addresses_in_aus(
            summary_aus(pre.branch_summary) + pre.mini_allocator.all_aus() + aus,
        );
        require new_disk.status.dom() <= addresses_in_aus(
            summary_aus(pre.branch_summary) + pre.mini_allocator.all_aus() + aus,
        );
        require new_disk.persistent.dom() <= addresses_in_aus(
            summary_aus(pre.branch_summary) + pre.mini_allocator.all_aus() + aus,
        );
        require new_disk.cache.dom() - pre.disk.cache.dom() <= addresses_in_aus(aus);
        require new_disk.status.dom() - pre.disk.status.dom() <= addresses_in_aus(aus);
        require new_disk.persistent.dom() - pre.disk.persistent.dom() <= addresses_in_aus(aus);
        require new_disk.cache.dom() <= Set::new(|addr: Address| addr.wf());
        require new_disk.persistent.dom() <= Set::new(|addr: Address| addr.wf());

        update mini_allocator = new_mini_allocator;
        update disk = new_disk;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.disk.inv()
        &&& self.active_branch.wf()
        &&& self.mini_allocator.wf()
        &&& self.persisted_root_count <= self.sealed_roots.len()
        &&& branch_summary_reads_valid(self.sealed_roots, self.visible_branch_nodes())
	        &&& self.branch_summary.dom().finite()
	        &&& self.branch_summary.values().finite()
	        &&& self.loaded_branch_summary_agrees()
	        &&& self.metadata_loaded ==> self.branch_metadata_loaded()
	        &&& self.metadata_loaded ==>
                summary_aus(self.branch_summary).disjoint(self.mini_allocator.all_aus())
	        &&& self.sealed_stack_i().wf(self.interpreted_branch_summary())
        &&& self.active_branch_i().inv()
        &&& summary_aus(self.interpreted_branch_summary()).disjoint(self.mini_allocator.all_aus())
        &&& self.disk.aus_clean_or_evictable(sealed_summary_aus_up_to(
            self.sealed_roots,
            self.interpreted_branch_summary(),
            self.persisted_root_count,
        ))
        &&& self.active_branch.root is None ==>
            active_loaded_nodes_of(self.disk, self.mini_allocator) == Map::<Address, BranchNode>::empty()
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(
        post: Self,
        image: CachingDiskBranchImage,
    ) {
        reveal(CachingDiskBranch::State::initialize);
        assert(post.disk.inv());
        assert(post.active_branch.wf());
        assert(post.mini_allocator.wf());
        assert(post.persisted_root_count == post.sealed_roots.len());
        assert(post.sealed_roots == image.sealed_roots);
        assert(post.branch_summary == Map::<AU, Summary>::empty());
        assert(post.branch_summary.dom().finite());
        lemma_values_finite(post.branch_summary);
        assert(post.branch_summary.values().finite());
        assert(post.active_branch == CachedBranch::State::empty_active());
        assert(post.mini_allocator == MiniAllocator::empty());
        assert(post.mini_allocator.all_aus() =~= Set::<AU>::empty());
        assert(post.seq_end == image.seq_end);
        assert(branch_summary_reads_valid(post.sealed_roots, post.visible_branch_nodes()));
        assert(post.loaded_branch_summary_agrees()) by {
            assert(post.branch_summary.dom() =~= Set::<AU>::empty());
            assert(post.branch_summary.dom() <= root_aus_up_to(post.sealed_roots, post.sealed_roots.len() as nat));
            assert forall |i: int| #![trigger post.sealed_roots[i]]
                0 <= i < post.sealed_roots.len() && post.branch_summary.contains_key(post.sealed_roots[i].au)
                implies {
                    &&& root_summary_read_valid(post.sealed_roots[i], post.visible_branch_nodes())
                    &&& post.branch_summary[post.sealed_roots[i].au]
                        == root_summary_from_read(post.sealed_roots[i], post.visible_branch_nodes())
                }
            by {
                assert(false);
            }
        };
        assert(post.visible_branch_nodes() == image.persistent_branch_nodes()) by {
            assert_maps_equal!(post.visible_branch_nodes(), image.persistent_branch_nodes(), addr => {
                if post.visible_branch_nodes().contains_key(addr) {
                    assert(post.disk.visible().contains_key(addr));
                    assert(image.persistent.contains_key(addr));
                }
                if image.persistent_branch_nodes().contains_key(addr) {
                    assert(image.persistent.contains_key(addr));
                    assert(post.disk.visible().contains_key(addr));
                }
            });
        };
        assert(post.interpreted_branch_summary() == image.branch_summary()) by {
            assert(post.sealed_roots == image.sealed_roots);
            assert(post.visible_branch_nodes() == image.persistent_branch_nodes());
        };
        assert(post.interpreted_sealed_stack_i().sealed_disk.entries =~= image.sealed_stack_i().sealed_disk.entries) by {
            let aus = image.live_persistent_aus();
            assert_maps_equal!(
                post.interpreted_sealed_stack_i().sealed_disk.entries,
                image.sealed_stack_i().sealed_disk.entries,
                addr => {
                    if post.interpreted_sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                        assert(post.interpreted_branch_summary() == image.branch_summary());
                        assert(addresses_in_aus(aus).contains(addr));
                        assert(image.persistent.contains_key(addr));
                        assert(image.live_persistent().contains_key(addr));
                    }
                    if image.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                        assert(image.live_persistent().contains_key(addr));
                        assert(addresses_in_aus(aus).contains(addr));
                    }
                }
            );
        };
        assert(post.interpreted_sealed_stack_i() == image.sealed_stack_i());
        assert(post.interpreted_branch_summary() == image.branch_summary()) by {
            assert(post.interpreted_branch_summary() == image.branch_summary());
            assert(post.sealed_stack_i() == image.sealed_stack_i());
        };
        assert(post.i().sealed_stack == image.sealed_stack_i());
        assert(post.i().branch_summary == image.branch_summary());
        assert(post.i().active_branch.inv());
        assert(image.sealed_stack_i().wf(image.branch_summary()));
        assert(image.live_persistent_aus() == summary_aus(image.branch_summary()));
        assert(summary_aus(post.interpreted_branch_summary()).disjoint(post.i().active_branch.mini_allocator.all_aus()));
        assert(post.i().wf());
        assert(post.disk.aus_clean_or_evictable(sealed_summary_aus_up_to(
            post.sealed_roots,
            post.interpreted_branch_summary(),
            post.persisted_root_count,
        ))) by {
            assert forall |addr: Address| #[trigger] post.disk.cache.contains_key(addr)
                && sealed_summary_aus_up_to(
                    post.sealed_roots,
                    post.interpreted_branch_summary(),
                    post.persisted_root_count,
                ).contains(addr.au)
                implies {
                    &&& post.disk.status.contains_key(addr)
                    &&& post.disk.status[addr] == PageStatus::Clean
                }
            by {
                assert(false);
            }
        };
        assert(active_loaded_nodes_of(post.disk, post.mini_allocator) == Map::<Address, BranchNode>::empty()) by {
            assert_maps_equal!(
                active_loaded_nodes_of(post.disk, post.mini_allocator),
                Map::<Address, BranchNode>::empty(),
                addr => {
                    if active_loaded_nodes_of(post.disk, post.mini_allocator).contains_key(addr) {
                        assert(post.disk.visible().contains_key(addr));
                        assert(post.mini_allocator.all_aus().contains(addr.au));
                        crate::disk::GenericDisk_v::to_aus_domain(post.disk.visible().dom());
                        assert(to_aus(post.disk.visible().dom()).contains(addr.au));
                        assert(false);
                    }
                }
            );
        };
        assert(post.freeze_image() == image);
    }

    #[inductive(disk_internal)]
    fn disk_internal_inductive(pre: Self, post: Self, lbl: Label, new_disk: CachingDisk::State) {
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Internal{});
        CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
        CachingDisk::State::internal_preserves_aus_clean_or_evictable(
            pre.disk,
            post.disk,
            sealed_summary_aus_up_to(
                pre.sealed_roots,
                pre.interpreted_branch_summary(),
                pre.persisted_root_count,
            ),
        );
        assert(post.sealed_roots == pre.sealed_roots);
        assert(post.branch_summary == pre.branch_summary);
        assert(post.persisted_root_count == pre.persisted_root_count);
        assert(post.active_branch == pre.active_branch);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.seq_end == pre.seq_end);
        assert(post.sealed_stack_i() == pre.sealed_stack_i());
        assert(post.active_branch_i() == pre.active_branch_i());
        assert(post.i() == pre.i());
    }

    #[inductive(observe_persisted_roots)]
    fn observe_persisted_roots_inductive(pre: Self, post: Self, lbl: Label, target_count: nat) {
        reveal(CachingDiskBranch::State::observe_persisted_roots);
        let old_aus = sealed_summary_aus_up_to(
            pre.sealed_roots,
            pre.interpreted_branch_summary(),
            pre.persisted_root_count,
        );
        let new_aus = sealed_summary_aus_up_to(
            pre.sealed_roots,
            pre.interpreted_branch_summary(),
            target_count,
        );
        let observed_aus = sealed_summary_aus_between(
            pre.sealed_roots,
            pre.interpreted_branch_summary(),
            pre.persisted_root_count,
            target_count,
        );
        sealed_summary_aus_up_to_split(
            pre.sealed_roots,
            pre.interpreted_branch_summary(),
            pre.persisted_root_count,
            target_count,
        );
        assert(post.disk == pre.disk);
        assert(post.sealed_roots == pre.sealed_roots);
        assert(post.branch_summary == pre.branch_summary);
        assert(post.persisted_root_count == target_count);
        assert(new_aus == old_aus + observed_aus);
        assert(post.disk.aus_clean_or_evictable(observed_aus)) by {
            assert(CachingDisk::State::next(
                pre.disk,
                pre.disk,
                CachingDisk::Label::ObserveCleanAUs{aus: observed_aus},
            ));
            reveal(CachingDisk::State::next);
            reveal(CachingDisk::State::next_by);
            assert(CachingDisk::State::observe_clean_aus(
                pre.disk,
                pre.disk,
                CachingDisk::Label::ObserveCleanAUs{aus: observed_aus},
            )) by {
                reveal(CachingDisk::State::observe_clean_aus);
            }
        };
        assert(post.disk.aus_clean_or_evictable(new_aus)) by {
            assert forall |addr: Address| #[trigger] post.disk.cache.contains_key(addr)
                && new_aus.contains(addr.au)
                implies {
                    &&& post.disk.status.contains_key(addr)
                    &&& post.disk.status[addr] == PageStatus::Clean
                }
            by {
                if old_aus.contains(addr.au) {
                    assert(pre.disk.aus_clean_or_evictable(old_aus));
                } else {
                    assert(observed_aus.contains(addr.au));
                    assert(post.disk.aus_clean_or_evictable(observed_aus));
                }
            }
        };
    }

    #[inductive(load_metadata)]
    fn load_metadata_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        reads: Map<Address, RawPage>,
    ) {
        reveal(CachingDiskBranch::State::load_metadata);
        CachingDisk::State::inv_next(
            pre.disk,
            pre.disk,
            CachingDisk::Label::Access{reads, writes: Map::empty()},
        );
        match lbl {
            Label::LoadMetadata{root, discovered_aus} => {
                let read_nodes = to_branch_nodes(reads);
                CachingDisk::State::access_visible_effect(
                    pre.disk,
                    pre.disk,
                    reads,
                    Map::empty(),
                );
                assert(post.disk == pre.disk);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.persisted_root_count == pre.persisted_root_count);
                assert(post.active_branch == pre.active_branch);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(post.seq_end == pre.seq_end);
                assert(post.branch_summary.dom().finite()) by {
                    assert(post.branch_summary.dom() <= pre.branch_summary.dom().insert(root.au));
                }
                lemma_values_finite(post.branch_summary);
                assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
                assert(post.sealed_stack_i() == pre.sealed_stack_i()) by {
                    assert_maps_equal!(
                        post.sealed_stack_i().sealed_disk.entries,
                        pre.sealed_stack_i().sealed_disk.entries,
                        addr => {}
                    );
                };
                assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
                assert(post.active_branch_i() == pre.active_branch_i());
                assert(post.i() == pre.i()) by {
                    assert(post.i().sealed_stack == post.sealed_stack_i());
                    assert(pre.i().sealed_stack == pre.sealed_stack_i());
                };
	                assert(post.loaded_branch_summary_agrees()) by {
	                    assert forall |au: AU| #[trigger] post.branch_summary.dom().contains(au)
	                        implies root_aus_up_to(post.sealed_roots, post.sealed_roots.len() as nat).contains(au)
                    by {
                        if pre.branch_summary.dom().contains(au) {
                            assert(pre.loaded_branch_summary_agrees());
                        } else {
                            assert(au == root.au);
                            let idx = choose |i: int| 0 <= i < pre.sealed_roots.len()
                                && pre.sealed_roots[i] == root;
                            root_aus_up_to_contains(pre.sealed_roots, pre.sealed_roots.len() as nat, idx);
                        }
                    }
                    assert forall |i: int| #![trigger post.sealed_roots[i]]
                        0 <= i < post.sealed_roots.len()
                            && post.branch_summary.contains_key(post.sealed_roots[i].au)
                        implies {
                            &&& root_summary_read_valid(post.sealed_roots[i], post.visible_branch_nodes())
                            &&& post.branch_summary[post.sealed_roots[i].au]
                                == root_summary_from_read(post.sealed_roots[i], post.visible_branch_nodes())
                        }
                    by {
                        assert(branch_summary_reads_valid(pre.sealed_roots, pre.visible_branch_nodes()));
                        if pre.branch_summary.contains_key(post.sealed_roots[i].au) {
                            assert(pre.loaded_branch_summary_agrees());
                        } else {
                            assert(post.sealed_roots[i].au == root.au);
                            assert(post.sealed_roots.to_set().contains(post.sealed_roots[i]));
                            assert(pre.sealed_roots.to_set().contains(root));
                            if post.sealed_roots[i] != root {
                                assert(addrs_with_different_au(post.sealed_roots[i], root));
                                assert(post.sealed_roots[i].au != root.au);
                                assert(false);
                            }
                            assert(read_nodes[root] == post.visible_branch_nodes()[root]) by {
                                assert(reads.contains_key(root));
                                assert(reads <= pre.disk.cache);
                                assert(pre.disk.cache.contains_key(root));
                                assert(pre.disk.visible()[root] == pre.disk.cache[root]);
                            }
	                        }
	                    }
	                };
	                if post.metadata_loaded {
	                    assert(root_aus_up_to(post.sealed_roots, post.sealed_roots.len() as nat)
	                        <= post.branch_summary.dom());
	                    branch_summary_from_reads_up_to_self_ensures(
	                        post.sealed_roots,
	                        post.visible_branch_nodes(),
	                        post.sealed_roots.len() as nat,
	                    );
	                    assert(post.interpreted_branch_summary() == post.branch_summary) by {
	                        assert_maps_equal!(
	                            post.interpreted_branch_summary(),
	                            post.branch_summary,
	                            au => {
	                                if post.interpreted_branch_summary().contains_key(au) {
	                                    assert(post.interpreted_branch_summary().dom().contains(au));
	                                    assert(root_aus_up_to(
	                                        post.sealed_roots,
	                                        post.sealed_roots.len() as nat,
	                                    ).contains(au));
	                                    assert(post.branch_summary.dom().contains(au));
	                                    let idx = root_aus_up_to_member_has_index(
	                                        post.sealed_roots,
	                                        post.sealed_roots.len() as nat,
	                                        au,
	                                    );
	                                    assert(post.sealed_roots[idx].au == au);
	                                    assert(post.branch_summary.contains_key(post.sealed_roots[idx].au));
	                                    assert(post.branch_summary[au]
	                                        == root_summary_from_read(
	                                            post.sealed_roots[idx],
	                                            post.visible_branch_nodes(),
	                                        ));
	                                    assert(post.interpreted_branch_summary()[au]
	                                        == root_summary_from_read(
	                                            post.sealed_roots[idx],
	                                            post.visible_branch_nodes(),
	                                        ));
	                                }
	                                if post.branch_summary.contains_key(au) {
	                                    assert(post.branch_summary.dom().contains(au));
	                                    assert(root_aus_up_to(
	                                        post.sealed_roots,
	                                        post.sealed_roots.len() as nat,
	                                    ).contains(au));
	                                    let idx = root_aus_up_to_member_has_index(
	                                        post.sealed_roots,
	                                        post.sealed_roots.len() as nat,
	                                        au,
	                                    );
	                                    assert(post.sealed_roots[idx].au == au);
	                                    assert(post.interpreted_branch_summary().contains_key(au));
	                                    assert(post.branch_summary[au]
	                                        == root_summary_from_read(
	                                            post.sealed_roots[idx],
	                                            post.visible_branch_nodes(),
	                                        ));
	                                    assert(post.interpreted_branch_summary()[au]
	                                        == root_summary_from_read(
	                                            post.sealed_roots[idx],
	                                            post.visible_branch_nodes(),
	                                        ));
	                                }
	                            }
	                        );
	                    };
	                }
	            },
	            _ => { }
	        }
    }

    #[inductive(query)]
    fn query_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        receipts: Seq<LoadedPathReceipt>,
        reads: Map<Address, RawPage>,
    ) {}

    #[inductive(append)]
    fn append_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_disk: CachingDisk::State,
        new_active_branch: CachedBranch::State,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) {
        reveal(CachingDiskBranch::State::append);
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);
        match lbl {
            Label::AppendLabel{keys, msgs} => {
                if pre.active_branch.root is Some {
                    assert(init_root is None);
                    let read_nodes = to_branch_nodes(reads);
                    let write_nodes = to_branch_nodes(writes);
                    let branch_lbl = CachedBranch::Label::Append{
                        mini_allocator: pre.mini_allocator,
                        receipt,
                        keys,
                        msgs,
                        read_nodes,
                        write_nodes,
                    };
                    let cb_step = choose |step: CachedBranch::Step|
                        CachedBranch::State::next_by(pre.active_branch, new_active_branch, branch_lbl, step);
                    match cb_step {
                        CachedBranch::Step::append_step() => {
                            assert(CachedBranch::State::append_step(pre.active_branch, new_active_branch, branch_lbl)) by {
                                reveal(CachedBranch::State::append_step);
                            }
                        },
                        _ => { assert(false); },
                    }
                    assert(new_active_branch == pre.active_branch);
                    CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Access{reads, writes});
                    pre.loaded_interpreted_wf();
                    let branch = pre.i().active_branch.branch.unwrap();
                    let path = Path{branch, key: keys[0], depth: receipt.depth()};
                    let target = receipt.target().addr;
                    let appended = branch.append(keys, msgs, path);

                    CachingDisk::State::access_visible_effect(pre.disk, post.disk, reads, writes);
                    assert(pre.i().active_branch.inv());
                    assert(branch.inv());
                    assert(pre.i().active_branch.branch == Some(branch));
                    assert(pre.active_branch.root == Some(branch.root));
                    assert(receipt.root == branch.root);

                    assert forall |addr: Address|
                        #[trigger] branch.disk_view.entries.contains_key(addr)
                        implies branch.disk_view.entries[addr] == to_branch_nodes(pre.disk.visible())[addr]
                    by {
                        assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                    }
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
                    assert(path.target().root == target);
                    assert(path.target().root() == receipt.target().node);
                    assert(path.target().disk_view == branch.disk_view);
                    assert(path.path_equiv(keys.last()));
                    assert(pre.i().active_branch.can_append(keys, msgs, path));
                    assert(path.target().has_root());
                    assert(path.target().disk_view.entries.contains_key(path.target().root));
                    assert(branch.disk_view.entries.contains_key(target));
                    assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                    assert(pre.i().active_branch.mini_allocator.page_is_reserved(target));
                    assert(pre.mini_allocator.page_is_reserved(target));
                    assert(pre.mini_allocator.all_aus().contains(target.au));
                    assert(post.mini_allocator == pre.mini_allocator);

                    assert(write_nodes == loaded_append_write_nodes(receipt, keys, msgs));
                    assert(write_nodes.contains_key(target));
                    assert(writes.contains_key(target));
                    assert(receipt.needed_addrs().contains(target)) by {
                        let i = receipt.lines.len() - 1;
                        assert(0 <= i < receipt.lines.len());
                        assert(receipt.lines[i].addr == target);
                    }
                    query_read_node_matches_visible(pre.disk, reads, target);
                    assert(read_nodes[target] == receipt.target().node);
                    assert(read_nodes[target] == branch.disk_view.entries[target]);

                    assert forall |addr: Address|
                        #[trigger] writes.contains_key(addr)
                        implies addr == target
                    by {
                        assert(write_nodes.contains_key(addr));
                    }
                    assert forall |addr: Address|
                        #[trigger] writes.contains_key(addr)
                        implies !summary_aus(pre.branch_summary).contains(addr.au)
                    by {
                        assert(addr == target);
                        assert(branch.disk_view.entries.contains_key(target));
                        assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                        assert(pre.i().active_branch.mini_allocator.page_is_reserved(target));
                        assert(pre.i().wf());
                    }
                    assert(writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary)))) by {
                        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                            implies !addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr) by {
                            assert(writes.contains_key(addr));
                        }
                    };
                    access_preserves_sealed_nodes(
                        pre.disk,
                        post.disk,
                        pre.branch_summary,
                        reads,
                        writes,
                    );
                    access_preserves_loaded_metadata(pre, post.disk, reads, writes);
                    assert(post.branch_summary == pre.branch_summary);
                    assert(post.interpreted_branch_summary() == pre.branch_summary);
                    assert(post.branch_metadata_loaded());
                    assert(post.loaded_branch_summary_agrees());
                    assert(post.sealed_stack_i() == pre.sealed_stack_i());
                    assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
                    access_preserves_persisted_prefix_clean(pre, post.disk, reads, writes);

                    assert(active_loaded_nodes_of(post.disk, post.mini_allocator) =~=
                        appended.disk_view.entries) by {
                        assert_maps_equal!(
                            active_loaded_nodes_of(post.disk, post.mini_allocator),
                            appended.disk_view.entries,
                            addr => {
                                if active_loaded_nodes_of(post.disk, post.mini_allocator).contains_key(addr) {
                                    assert(to_branch_nodes(post.disk.visible()).contains_key(addr));
                                    if writes.contains_key(addr) {
                                        assert(addr == target);
                                        assert(to_branch_nodes(post.disk.visible())[addr] == write_nodes[addr]);
                                        assert(write_nodes[addr] == loaded_append_write_nodes(receipt, keys, msgs)[addr]);
                                        assert(appended.disk_view.entries[addr] == write_nodes[addr]);
                                    } else {
                                        assert(pre.disk.visible().contains_key(addr));
                                        assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                                        assert(branch.disk_view.entries.contains_key(addr));
                                        assert(appended.disk_view.entries.contains_key(addr));
                                        assert(to_branch_nodes(post.disk.visible())[addr] == to_branch_nodes(pre.disk.visible())[addr]);
                                        assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator)[addr] == branch.disk_view.entries[addr]);
                                        assert(appended.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                                    }
                                }
                                if appended.disk_view.entries.contains_key(addr) {
                                    if addr == target {
                                        assert(writes.contains_key(addr));
                                        assert(post.disk.visible().contains_key(addr));
                                        assert(post.mini_allocator.all_aus().contains(addr.au));
                                        assert(to_branch_nodes(post.disk.visible())[addr] == write_nodes[addr]);
                                        assert(appended.disk_view.entries[addr] == write_nodes[addr]);
                                    } else {
                                        assert(branch.disk_view.entries.contains_key(addr));
                                        assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                                        assert(pre.disk.visible().contains_key(addr));
                                        assert(!writes.contains_key(addr));
                                        assert(post.disk.visible().contains_key(addr));
                                        assert(post.mini_allocator.all_aus().contains(addr.au));
                                        assert(to_branch_nodes(post.disk.visible())[addr] == to_branch_nodes(pre.disk.visible())[addr]);
                                        assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator)[addr] == branch.disk_view.entries[addr]);
                                        assert(appended.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                                    }
                                }
                            }
                        );
                    };
                    assert(post.i().active_branch == pre.i().active_branch.branch_append(keys, msgs, path));
                    assert(post.i().seq_end == pre.i().seq_end + keys.len());
                    AllocationBranch::build_next_preserves_inv(
                        pre.i().active_branch,
                        post.i().active_branch,
                        crate::allocation_layer::AllocationBranch_v::BuildEvent::Append{keys, msgs, path},
                        Set::empty(),
                        Set::empty(),
                    );
                    assert(post.i().wf());
                } else {
                    assert(init_root is Some);
                    let init_addr = init_root.unwrap();
                    let write_nodes = to_branch_nodes(writes);
                    let branch_lbl = CachedBranch::Label::Initialize{
                        mini_allocator: pre.mini_allocator,
                        init_root: init_addr,
                        keys,
                        msgs,
                        write_nodes,
                    };
                    let cb_step = choose |step: CachedBranch::Step|
                        CachedBranch::State::next_by(pre.active_branch, new_active_branch, branch_lbl, step);
                    match cb_step {
                        CachedBranch::Step::initialize_branch() => {
                            assert(CachedBranch::State::initialize_branch(pre.active_branch, new_active_branch, branch_lbl)) by {
                                reveal(CachedBranch::State::initialize_branch);
                            }
                        },
                        _ => { assert(false); },
                    }
	                    assert(new_active_branch == CachedBranch::State{root: Some(init_addr)});
                        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Access{reads, writes});
                        CachingDisk::State::access_visible_effect(pre.disk, post.disk, reads, writes);
                        pre.loaded_interpreted_wf();
                        assert(write_nodes == loaded_initialize_write_nodes(init_addr, keys, msgs));
                        assert(writes.dom() =~= set![init_addr]) by {
                            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                implies set![init_addr].contains(addr) by {
                                assert(write_nodes.contains_key(addr));
                            }
                            assert forall |addr: Address| #[trigger] set![init_addr].contains(addr)
                                implies writes.dom().contains(addr) by {
                                assert(write_nodes.contains_key(addr));
                            }
                        };
                        assert(!summary_aus(pre.branch_summary).contains(init_addr.au)) by {
                            assert(pre.mini_allocator.can_allocate(init_addr));
                            assert(pre.mini_allocator.all_aus().contains(init_addr.au));
                            assert(pre.i().wf());
                        }
                        assert(writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary)))) by {
                            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                implies !addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr) by {
                                assert(addr == init_addr);
                            }
                        };
                        access_preserves_sealed_nodes(pre.disk, post.disk, pre.branch_summary, reads, writes);
                        access_preserves_loaded_metadata(pre, post.disk, reads, writes);
                        assert(post.branch_summary == pre.branch_summary);
                        assert(post.interpreted_branch_summary() == pre.branch_summary);
                        assert(post.branch_metadata_loaded());
                        assert(post.loaded_branch_summary_agrees());
                        assert(post.sealed_stack_i() == pre.sealed_stack_i());
                        assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
                        pre.i().sealed_stack.sealed_disk.build_branch_summary_finite(
                            pre.i().sealed_stack.sealed_roots.to_set(),
                        );
                        assert(pre.branch_summary.values().finite());
                        sealed_summary_aus_up_to_subset_summary_aus(
                            pre.sealed_roots,
                            pre.branch_summary,
                            pre.persisted_root_count,
                        );
                        assert(writes.dom().disjoint(addresses_in_aus(sealed_summary_aus_up_to(
                            pre.sealed_roots,
                            pre.branch_summary,
                            pre.persisted_root_count,
                        )))) by {
                            let persisted_aus = sealed_summary_aus_up_to(
                                pre.sealed_roots,
                                pre.branch_summary,
                                pre.persisted_root_count,
                            );
                            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                implies !addresses_in_aus(persisted_aus).contains(addr) by {
                                assert(!addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr));
                            }
                        };
                        CachingDisk::State::access_preserves_aus_clean_or_evictable(
                            pre.disk,
                            post.disk,
                            reads,
                            writes,
                            sealed_summary_aus_up_to(pre.sealed_roots, pre.branch_summary, pre.persisted_root_count),
                        );
                        mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, init_addr);
                        assert(active_loaded_nodes_of(post.disk, post.mini_allocator) =~=
                            loaded_initialize_write_nodes(init_addr, keys, msgs)) by {
                            assert_maps_equal!(
                                active_loaded_nodes_of(post.disk, post.mini_allocator),
                                loaded_initialize_write_nodes(init_addr, keys, msgs),
                                addr => {
                                    if active_loaded_nodes_of(post.disk, post.mini_allocator).contains_key(addr) {
                                        assert(to_branch_nodes(post.disk.visible()).contains_key(addr));
                                        if writes.contains_key(addr) {
                                            assert(addr == init_addr);
                                        } else {
                                            assert(pre.disk.visible().contains_key(addr));
                                            assert(post.mini_allocator.all_aus().contains(addr.au));
                                            assert(pre.mini_allocator.all_aus().contains(addr.au));
                                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                                            assert(false);
                                        }
                                    }
                                    if loaded_initialize_write_nodes(init_addr, keys, msgs).contains_key(addr) {
                                        assert(addr == init_addr);
                                        assert(writes.contains_key(addr));
                                        assert(post.disk.visible().contains_key(addr));
                                        assert(post.mini_allocator.all_aus().contains(addr.au));
                                    }
                                }
                            );
                        };
                        assert(post.active_branch_i()
                            == pre.active_branch_i().branch_initialize(init_addr, keys, msgs));
                        AllocationBranch::build_next_preserves_inv(
                            pre.active_branch_i(),
                            post.active_branch_i(),
                            crate::allocation_layer::AllocationBranch_v::BuildEvent::Initialize{
                                addr: init_addr,
                                keys,
                                msgs,
                            },
                            Set::empty(),
                            Set::empty(),
                        );
                        assert(post.i().wf());
	                }
	            },
	            _ => { }
	        }
    }

    #[inductive(freeze_as)]
    fn freeze_as_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(freeze_prepared)]
    fn freeze_prepared_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(internal_noop)]
    fn internal_noop_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(internal_grow)]
    fn internal_grow_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_disk: CachingDisk::State,
        new_root_addr: Address,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) {
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Access{reads, writes});
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let old_root = pre.active_branch.root.unwrap();
        let branch = pre.i().active_branch.branch.unwrap();
        let grown = branch.grow(new_root_addr);

        CachingDisk::State::access_visible_effect(
            pre.disk,
            post.disk,
            reads,
            writes,
        );
        pre.loaded_interpreted_wf();
        mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, new_root_addr);

        assert(write_nodes == loaded_grow_write_nodes(old_root, new_root_addr));
        assert(writes.dom() =~= set![new_root_addr]) by {
            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                implies set![new_root_addr].contains(addr) by {
                assert(write_nodes.contains_key(addr));
            }
            assert forall |addr: Address| #[trigger] set![new_root_addr].contains(addr)
                implies writes.dom().contains(addr) by {
                assert(write_nodes.contains_key(addr));
            }
        };

        assert(!branch.disk_view.entries.contains_key(new_root_addr)) by {
            if branch.disk_view.entries.contains_key(new_root_addr) {
                assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                assert(pre.i().active_branch.mini_allocator.page_is_reserved(new_root_addr));
                assert(false);
            }
        }
        assert(branch.disk_view.is_fresh(set![new_root_addr])) by {
            assert forall |addr: Address| #[trigger] set![new_root_addr].contains(addr)
                implies !branch.disk_view.entries.contains_key(addr) by {
                assert(addr == new_root_addr);
            }
        };
        assert(pre.i().active_branch.can_grow(new_root_addr));

        assert(!summary_aus(pre.branch_summary).contains(new_root_addr.au)) by {
            assert(pre.mini_allocator.can_allocate(new_root_addr));
            assert(pre.mini_allocator.all_aus().contains(new_root_addr.au));
            assert(pre.i().wf());
        }
        assert(writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary)))) by {
            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                implies !addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr) by {
                assert(addr == new_root_addr);
            }
        };
        access_preserves_sealed_nodes(
            pre.disk,
            post.disk,
            pre.branch_summary,
            reads,
            writes,
        );
        access_preserves_loaded_metadata(pre, post.disk, reads, writes);
        assert(post.branch_summary == pre.branch_summary);
        assert(post.interpreted_branch_summary() == pre.branch_summary);
        assert(post.branch_metadata_loaded());
        assert(post.loaded_branch_summary_agrees());
        assert(post.sealed_stack_i() == pre.sealed_stack_i());
        assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
        access_preserves_persisted_prefix_clean(
            pre,
            post.disk,
            reads,
            writes,
        );

        assert(active_loaded_nodes_of(post.disk, post.mini_allocator) =~=
            grown.disk_view.entries) by {
            assert_maps_equal!(
                active_loaded_nodes_of(post.disk, post.mini_allocator),
                grown.disk_view.entries,
                addr => {
                    if active_loaded_nodes_of(post.disk, post.mini_allocator).contains_key(addr) {
                        assert(to_branch_nodes(post.disk.visible()).contains_key(addr));
                        if writes.contains_key(addr) {
                            assert(addr == new_root_addr);
                            assert(grown.disk_view.entries.contains_key(addr));
                            assert(to_branch_nodes(post.disk.visible())[addr] == write_nodes[addr]);
                            assert(write_nodes[addr] == loaded_grow_write_nodes(old_root, new_root_addr)[addr]);
                            assert(grown.disk_view.entries[addr] == loaded_grow_write_nodes(old_root, new_root_addr)[addr]);
                        } else {
                            assert(pre.disk.visible().contains_key(addr));
                            assert(post.mini_allocator.all_aus().contains(addr.au));
                            assert(pre.mini_allocator.all_aus().contains(addr.au));
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(grown.disk_view.entries.contains_key(addr));
                            assert(to_branch_nodes(post.disk.visible())[addr] == to_branch_nodes(pre.disk.visible())[addr]);
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator)[addr] == branch.disk_view.entries[addr]);
                            assert(grown.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                        }
                    }
                    if grown.disk_view.entries.contains_key(addr) {
                        if addr == new_root_addr {
                            assert(writes.contains_key(addr));
                            assert(post.disk.visible().contains_key(addr));
                            assert(post.mini_allocator.all_aus().contains(addr.au));
                            assert(to_branch_nodes(post.disk.visible())[addr] == write_nodes[addr]);
                            assert(write_nodes[addr] == loaded_grow_write_nodes(old_root, new_root_addr)[addr]);
                            assert(grown.disk_view.entries[addr] == loaded_grow_write_nodes(old_root, new_root_addr)[addr]);
                        } else {
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                            assert(pre.disk.visible().contains_key(addr));
                            assert(!writes.contains_key(addr));
                            assert(post.disk.visible().contains_key(addr));
                            assert(post.mini_allocator.all_aus().contains(addr.au));
                            assert(to_branch_nodes(post.disk.visible())[addr] == to_branch_nodes(pre.disk.visible())[addr]);
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator)[addr] == branch.disk_view.entries[addr]);
                            assert(grown.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                        }
                    }
                }
            );
        };

        assert(post.i().active_branch == pre.i().active_branch.branch_grow(new_root_addr));
        AllocationBranch::build_next_preserves_inv(
            pre.i().active_branch,
            post.i().active_branch,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Grow{addr: new_root_addr},
            Set::empty(),
            Set::empty(),
        );
        assert(post.i().wf());
    }

    #[inductive(internal_split)]
    fn internal_split_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_disk: CachingDisk::State,
        new_child_addr: Address,
        receipt: LoadedPathReceipt,
        split_arg: SplitArg,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) {
        CachingDisk::State::inv_next(pre.disk, post.disk, CachingDisk::Label::Access{reads, writes});
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch = pre.i().active_branch.branch.unwrap();
        let path = Path{branch, key: split_arg.get_pivot(), depth: receipt.depth()};
        let split_branch = branch.split(new_child_addr, path, split_arg);
        let parent_addr = receipt.target().addr;
        let child_addr = receipt.child_addr();

        CachingDisk::State::access_visible_effect(pre.disk, post.disk, reads, writes);
        pre.loaded_interpreted_wf();
        mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, new_child_addr);
        assert(pre.i().active_branch.inv());
        assert(branch.inv());
        assert(pre.i().active_branch.branch == Some(branch));
        assert(pre.active_branch.root == Some(branch.root));
        assert(receipt.root == branch.root);
        assert(receipt.key == split_arg.get_pivot());

        assert forall |addr: Address|
            #[trigger] branch.disk_view.entries.contains_key(addr)
            implies branch.disk_view.entries[addr] == to_branch_nodes(pre.disk.visible())[addr]
        by {
            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
        }

        assert(!branch.disk_view.entries.contains_key(new_child_addr)) by {
            if branch.disk_view.entries.contains_key(new_child_addr) {
                assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                assert(pre.i().active_branch.mini_allocator.page_is_reserved(new_child_addr));
                assert(false);
            }
        }
        assert(branch.disk_view.is_fresh(set!{new_child_addr})) by {
            assert forall |addr: Address| #[trigger] set![new_child_addr].contains(addr)
                implies !branch.disk_view.entries.contains_key(addr) by {
                assert(addr == new_child_addr);
            }
        };

        query_read_node_matches_visible(pre.disk, reads, parent_addr);
        query_read_node_matches_visible(pre.disk, reads, child_addr);
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
        assert(path.target().root == parent_addr);
        assert(path.target().root() == receipt.target().node);
        assert(path.target().disk_view == branch.disk_view);
        assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
        assert(pre.i().active_branch.can_split(new_child_addr, path, split_arg));

        LinkedBranchRefinement::split_refines(branch, new_child_addr, path, split_arg);
        assert(split_branch == branch.split(new_child_addr, path, split_arg));
        assert(split_branch.disk_view.entries.dom() =~= branch.disk_view.entries.dom().insert(new_child_addr));

        assert(write_nodes == loaded_split_write_nodes(
            receipt,
            read_nodes,
            split_arg,
            new_child_addr,
        ));
        assert(write_nodes.contains_key(parent_addr));
        assert(write_nodes.contains_key(child_addr));
        assert(write_nodes.contains_key(new_child_addr));
        assert(writes.contains_key(parent_addr));
        assert(writes.contains_key(child_addr));
        assert(writes.contains_key(new_child_addr));
        assert(split_branch.disk_view.entries[parent_addr] == write_nodes[parent_addr]);
        assert(split_branch.disk_view.entries[child_addr] == write_nodes[child_addr]);
        assert(split_branch.disk_view.entries[new_child_addr] == write_nodes[new_child_addr]);

        assert forall |addr: Address|
            #[trigger] writes.contains_key(addr)
            implies addr == parent_addr || addr == child_addr || addr == new_child_addr
        by {
            assert(write_nodes.contains_key(addr));
        }
        assert forall |addr: Address|
            #[trigger] writes.contains_key(addr)
            implies !summary_aus(pre.branch_summary).contains(addr.au)
        by {
            if addr == parent_addr || addr == child_addr {
                assert(branch.disk_view.entries.contains_key(addr));
                assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                assert(pre.i().active_branch.mini_allocator.page_is_reserved(addr));
                assert(pre.i().wf());
            } else {
                assert(addr == new_child_addr);
                assert(pre.mini_allocator.can_allocate(new_child_addr));
                assert(pre.mini_allocator.all_aus().contains(new_child_addr.au));
                assert(pre.i().wf());
            }
        }
        assert(writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary)))) by {
            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                implies !addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr) by {
                assert(writes.contains_key(addr));
            }
        };
        access_preserves_sealed_nodes(
            pre.disk,
            post.disk,
            pre.branch_summary,
            reads,
            writes,
        );
        access_preserves_loaded_metadata(pre, post.disk, reads, writes);
        assert(post.branch_summary == pre.branch_summary);
        assert(post.interpreted_branch_summary() == pre.branch_summary);
        assert(post.branch_metadata_loaded());
        assert(post.loaded_branch_summary_agrees());
        assert(post.sealed_stack_i() == pre.sealed_stack_i());
        assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
        access_preserves_persisted_prefix_clean(pre, post.disk, reads, writes);

        assert(active_loaded_nodes_of(post.disk, post.mini_allocator) =~=
            split_branch.disk_view.entries) by {
            assert_maps_equal!(
                active_loaded_nodes_of(post.disk, post.mini_allocator),
                split_branch.disk_view.entries,
                addr => {
                    if active_loaded_nodes_of(post.disk, post.mini_allocator).contains_key(addr) {
                        assert(to_branch_nodes(post.disk.visible()).contains_key(addr));
                        if writes.contains_key(addr) {
                            assert(addr == parent_addr || addr == child_addr || addr == new_child_addr);
                            assert(to_branch_nodes(post.disk.visible())[addr] == write_nodes[addr]);
                            assert(split_branch.disk_view.entries[addr] == write_nodes[addr]);
                        } else {
                            assert(pre.disk.visible().contains_key(addr));
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(split_branch.disk_view.entries.contains_key(addr));
                            assert(to_branch_nodes(post.disk.visible())[addr] == to_branch_nodes(pre.disk.visible())[addr]);
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator)[addr] == branch.disk_view.entries[addr]);
                            assert(split_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                        }
                    }
                    if split_branch.disk_view.entries.contains_key(addr) {
                        if addr == parent_addr || addr == child_addr || addr == new_child_addr {
                            assert(writes.contains_key(addr));
                            assert(post.disk.visible().contains_key(addr));
                            assert(post.mini_allocator.all_aus().contains(addr.au));
                            assert(to_branch_nodes(post.disk.visible())[addr] == write_nodes[addr]);
                            assert(split_branch.disk_view.entries[addr] == write_nodes[addr]);
                        } else {
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                            assert(pre.disk.visible().contains_key(addr));
                            assert(!writes.contains_key(addr));
                            assert(post.disk.visible().contains_key(addr));
                            assert(post.mini_allocator.all_aus().contains(addr.au));
                            assert(to_branch_nodes(post.disk.visible())[addr] == to_branch_nodes(pre.disk.visible())[addr]);
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator)[addr] == branch.disk_view.entries[addr]);
                            assert(split_branch.disk_view.entries[addr] == branch.disk_view.entries[addr]);
                        }
                    }
                }
            );
        };
        assert(post.i().active_branch == pre.i().active_branch.branch_split(new_child_addr, path, split_arg));
        AllocationBranch::build_next_preserves_inv(
            pre.i().active_branch,
            post.i().active_branch,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Split{
                addr: new_child_addr,
                path,
                split_arg,
            },
            Set::empty(),
            Set::empty(),
        );
        assert(post.i().wf());
    }

    #[inductive(internal_seal)]
    fn internal_seal_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        written_disk: CachingDisk::State,
        aux_ptr: Pointer,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) {
        reveal(CachingDiskBranch::State::internal_seal);
        reveal(CachedBranch::State::next);
        reveal(CachedBranch::State::next_by);
        CachingDisk::State::inv_next(pre.disk, written_disk, CachingDisk::Label::Access{reads, writes});
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let root = pre.active_branch.root.unwrap();
        let branch = pre.i().active_branch.branch.unwrap();
        let dealloc_aus = pre.i().active_branch.mini_allocator.removable_aus();
        let sealed_active = pre.i().active_branch.branch_seal(aux_ptr, dealloc_aus);
        let sealed_branch = sealed_active.branch.unwrap();
        let sealed_summary = pre.mini_allocator.reserved_aus();

        CachingDisk::State::access_visible_effect(
            pre.disk,
            post.disk,
            reads,
            writes,
        );
        pre.loaded_interpreted_wf();

        assert(pre.i().active_branch.mini_allocator == pre.mini_allocator);
        assert(dealloc_aus == pre.mini_allocator.removable_aus());
        assert(pre.i().active_branch.branch == Some(branch));
        assert(branch.root == root);
        assert(reads.contains_key(root));
        query_read_node_matches_visible(pre.disk, reads, root);
        assert(branch.disk_view.entries.contains_key(root));
        assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(root));
        assert(branch.disk_view.entries[root] == to_branch_nodes(pre.disk.visible())[root]);
        assert(read_nodes[root] == branch.root());
        assert(aux_ptr is Some <==> branch.root() is Index);

        if aux_ptr is Some {
            let ptr = aux_ptr.unwrap();
            assert(pre.mini_allocator.can_allocate(ptr));
            assert(pre.mini_allocator.reserved_aus().contains(ptr.au));
            assert(!dealloc_aus.contains(ptr.au)) by {
                if dealloc_aus.contains(ptr.au) {
                    assert(pre.mini_allocator.removable_aus().contains(ptr.au));
                    assert(pre.mini_allocator.can_remove(ptr.au));
                    assert(pre.mini_allocator.allocs[ptr.au].has_no_outstanding_refs());
                    assert(!pre.mini_allocator.reserved_aus().contains(ptr.au));
                    assert(false);
                }
            }
        }
        assert(pre.i().active_branch.can_seal(aux_ptr, dealloc_aus));

        let concrete_sealed_branch = LinkedBranch{
            root: branch.root,
            disk_view: DiskView{
                entries: branch.disk_view.entries.union_prefer_right(write_nodes),
            },
        };

        if aux_ptr is Some {
            let ptr = aux_ptr.unwrap();
            assert(write_nodes == loaded_seal_write_nodes(
                root,
                read_nodes,
                aux_ptr,
                sealed_summary,
            ));
            assert(write_nodes.contains_key(root));
            assert(write_nodes.contains_key(ptr));
            assert(write_nodes[root] == BranchNode::Index{
                pivots: branch.root()->pivots,
                children: branch.root()->children,
                aux_ptr,
            });
            assert(write_nodes[ptr] == BranchNode::Auxiliary(sealed_summary));
            assert(concrete_sealed_branch == branch.seal(ptr, sealed_summary)) by {
                assert_maps_equal!(
                    concrete_sealed_branch.disk_view.entries,
                    branch.seal(ptr, sealed_summary).disk_view.entries,
                    addr => {
                        if concrete_sealed_branch.disk_view.entries.contains_key(addr) {
                            if write_nodes.contains_key(addr) {
                                assert(addr == root || addr == ptr);
                            } else {
                                assert(branch.disk_view.entries.contains_key(addr));
                            }
                        }
                        if branch.seal(ptr, sealed_summary).disk_view.entries.contains_key(addr) {
                            if addr == root || addr == ptr {
                                assert(write_nodes.contains_key(addr));
                            } else {
                                assert(branch.disk_view.entries.contains_key(addr));
                                assert(!write_nodes.contains_key(addr));
                            }
                        }
                    }
                );
            };
        } else {
            assert(write_nodes == Map::<Address, BranchNode>::empty());
            assert(concrete_sealed_branch == branch) by {
                assert_maps_equal!(
                    concrete_sealed_branch.disk_view.entries,
                    branch.disk_view.entries,
                    addr => {
                        if concrete_sealed_branch.disk_view.entries.contains_key(addr) {
                            assert(!write_nodes.contains_key(addr));
                        }
                    }
                );
            };
        }
        assert(sealed_branch == concrete_sealed_branch);

        pre.i().active_branch.branch_seal_preserves_inv(aux_ptr, dealloc_aus);
        assert(sealed_active.inv());
        assert(sealed_branch.valid_sealed_branch());
        assert(sealed_branch.tight_disk_view_with_summary());

        mini_allocator_all_minus_removable_is_reserved(pre.mini_allocator);
        if aux_ptr is Some {
            mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, aux_ptr.unwrap());
            let allocated = pre.mini_allocator.allocate(aux_ptr.unwrap());
            allocated.prune_preserves_wf(dealloc_aus);
            assert(allocated.all_aus() == pre.mini_allocator.all_aus());
            assert(sealed_active.mini_allocator == allocated.prune(dealloc_aus));
        } else {
            pre.mini_allocator.prune_preserves_wf(dealloc_aus);
            assert(sealed_active.mini_allocator == pre.mini_allocator.prune(dealloc_aus));
        }
        assert(sealed_active.mini_allocator.all_aus() == sealed_summary);
        assert(sealed_branch.get_summary() == sealed_summary);
        let loose_active_summary =
            Map::<AU, Summary>::empty().insert(sealed_branch.root.au, sealed_branch.get_summary());
        let loose_active_disk = BufferDisk{
            entries: sealed_nodes_of(post.disk.visible(), loose_active_summary),
        };
        assert(loose_active_summary.dom().finite());
        lemma_values_finite(loose_active_summary);

        assert(summary_aus(pre.branch_summary).disjoint(sealed_branch.get_summary())) by {
            assert forall |au: AU| #[trigger] summary_aus(pre.branch_summary).contains(au)
                implies !sealed_branch.get_summary().contains(au)
            by {
                if sealed_branch.get_summary().contains(au) {
                    assert(pre.mini_allocator.all_aus().contains(au));
                    assert(false);
                }
            }
        };
        assert(!pre.branch_summary.contains_key(sealed_branch.root.au)) by {
            if pre.branch_summary.contains_key(sealed_branch.root.au) {
                assert(pre.branch_summary.values().contains(pre.branch_summary[sealed_branch.root.au]));
                lemma_union_set_of_sets_subset(pre.branch_summary.values(), pre.branch_summary[sealed_branch.root.au]);
                assert(summary_aus(pre.branch_summary).contains(sealed_branch.root.au));
                assert(sealed_branch.get_summary().contains(sealed_branch.root.au));
                assert(false);
            }
        };
        assert(!pre.i().branch_summary.contains_key(sealed_branch.root.au));
        assert(tight_branch_in_loose_disk(
            loose_active_disk,
            sealed_branch.root,
            sealed_branch.get_summary(),
            sealed_branch,
        )) by {
            assert(sealed_branch.root == root);
            assert(sealed_branch.valid_sealed_branch());
            assert(sealed_branch.tight_disk_view_with_summary());
            assert(sealed_branch.get_summary() == sealed_summary);
            assert(sealed_branch.disk_view.entries <= loose_active_disk.entries) by {
                assert forall |addr: Address| #[trigger] sealed_branch.disk_view.entries.contains_key(addr)
                    implies loose_active_disk.entries.contains_key(addr)
                        && loose_active_disk.entries[addr] == sealed_branch.disk_view.entries[addr]
                by {
                    assert(addrs_closed(sealed_branch.full_repr(), sealed_branch.get_summary()));
                    assert(sealed_branch.full_repr().contains(addr));
                    assert(sealed_branch.get_summary().contains(addr.au));
                    assert(loose_active_summary.contains_key(sealed_branch.root.au));
                    assert(loose_active_summary[sealed_branch.root.au] == sealed_branch.get_summary());
                    assert(summary_aus(loose_active_summary).contains(addr.au)) by {
                        assert(loose_active_summary.values().contains(sealed_branch.get_summary()));
                        lemma_union_set_of_sets_subset(loose_active_summary.values(), sealed_branch.get_summary());
                    }
                    assert(post.disk.visible().contains_key(addr)) by {
                        if writes.contains_key(addr) {
                            assert(write_nodes.contains_key(addr));
                            assert(post.disk.visible().contains_key(addr));
                        } else {
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                            assert(pre.i().active_branch.mini_allocator.page_is_reserved(addr));
                            assert(pre.mini_allocator.page_is_reserved(addr));
                            assert(mini_allocator_allocated_addrs(pre.mini_allocator).contains(addr));
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                            assert(pre.disk.visible().contains_key(addr));
                            assert(post.disk.visible().contains_key(addr));
                        }
                    };
                    assert(sealed_nodes_of(post.disk.visible(), loose_active_summary).contains_key(addr));
                    assert(to_branch_nodes(post.disk.visible())[addr] == sealed_branch.disk_view.entries[addr]);
                }
            };
        };
        assert(addrs_closed(loose_active_disk.entries.dom(), sealed_branch.get_summary())) by {
            assert forall |addr: Address| #[trigger] loose_active_disk.entries.dom().contains(addr)
                implies sealed_branch.get_summary().contains(addr.au)
            by {
                assert(loose_active_disk.entries.contains_key(addr));
                assert(summary_aus(loose_active_summary).contains(addr.au));
                let summary = lemma_union_set_of_sets_contains(loose_active_summary.values(), addr.au);
                assert(summary == sealed_branch.get_summary());
            }
        };
        pre.i().sealed_stack.push_branch_preserves_wf(pre.i().branch_summary, sealed_branch, loose_active_disk);
        let pushed_stack = pre.i().sealed_stack.push_branch(sealed_branch, loose_active_disk);
        let roots = pre.i().sealed_stack.sealed_roots.to_set();
        pre.i().sealed_stack.sealed_disk.build_branch_summary_finite(roots);
        assert(pre.branch_summary.dom().finite());
        assert(sealed_branch.get_summary().contains(sealed_branch.root.au)) by {
            assert(sealed_branch.full_repr().contains(sealed_branch.root));
            assert(crate::disk::GenericDisk_v::addrs_closed(
                sealed_branch.full_repr(),
                sealed_branch.get_summary(),
            ));
        }
        assert(!pre.branch_summary.contains_key(sealed_branch.root.au));
        branch_summary_insert_ensures(pre.branch_summary, sealed_branch);
        lemma_values_finite(post.branch_summary);
        assert(post.branch_summary.values().finite());
        assert(summary_aus(post.branch_summary)
            == summary_aus(pre.branch_summary) + sealed_branch.get_summary());
        assert(writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary)))) by {
            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                implies !addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr) by {
                assert(write_nodes.contains_key(addr));
                if aux_ptr is Some {
                    assert(addr == root || addr == aux_ptr.unwrap());
                    if addr == root {
                        assert(sealed_branch.get_summary().contains(addr.au)) by {
                            assert(sealed_branch.full_repr().contains(root));
                            assert(addrs_closed(sealed_branch.full_repr(), sealed_branch.get_summary()));
                        }
                    } else {
                        assert(addr == aux_ptr.unwrap());
                        assert(sealed_branch.get_summary().contains(addr.au)) by {
                            assert(sealed_branch.full_repr().contains(addr));
                            assert(addrs_closed(sealed_branch.full_repr(), sealed_branch.get_summary()));
                        }
                    }
                } else {
                    assert(false);
                }
                if addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr) {
                    assert(summary_aus(pre.branch_summary).contains(addr.au));
                    assert(false);
                }
            }
        };
        access_preserves_loaded_metadata(pre, post.disk, reads, writes);
        assert(branch_summary_reads_valid(post.sealed_roots, post.visible_branch_nodes())) by {
            assert forall |i: int| #![trigger post.sealed_roots[i]]
                0 <= i < post.sealed_roots.len()
                implies root_summary_read_valid(post.sealed_roots[i], post.visible_branch_nodes())
            by {
                if i < pre.sealed_roots.len() {
                    assert(post.sealed_roots[i] == pre.sealed_roots[i]);
                    assert(branch_summary_reads_valid(pre.sealed_roots, post.visible_branch_nodes()));
                } else {
                    assert(i == pre.sealed_roots.len());
                    assert(post.sealed_roots[i] == root);
                    assert(post.visible_branch_nodes().contains_key(root));
                    if post.visible_branch_nodes()[root] is Index {
                        assert(aux_ptr is Some);
                        let aux = aux_ptr.unwrap();
                        assert(post.visible_branch_nodes()[root]->aux_ptr == Some(aux));
                        assert(post.visible_branch_nodes().contains_key(aux));
                        assert(post.visible_branch_nodes()[aux] is Auxiliary);
                    } else {
                        assert(post.visible_branch_nodes()[root] is Leaf);
                    }
                }
            }
        };
        branch_summary_from_reads_up_to_self_ensures(
            post.sealed_roots,
            post.visible_branch_nodes(),
            post.sealed_roots.len() as nat,
        );
        assert(post.interpreted_branch_summary() == post.branch_summary) by {
            assert_maps_equal!(post.interpreted_branch_summary(), post.branch_summary, au => {
                if post.interpreted_branch_summary().contains_key(au) {
                    let idx = root_aus_up_to_member_has_index(post.sealed_roots, post.sealed_roots.len() as nat, au);
                    if idx < pre.sealed_roots.len() {
                        assert(post.sealed_roots[idx] == pre.sealed_roots[idx]);
                        assert(loaded_branch_summary_agrees(
                            pre.sealed_roots,
                            post.visible_branch_nodes(),
                            pre.branch_summary,
                        ));
                        root_aus_up_to_contains(pre.sealed_roots, pre.sealed_roots.len() as nat, idx);
                        assert(pre.branch_summary.dom().contains(pre.sealed_roots[idx].au));
                        assert(pre.branch_summary.contains_key(pre.sealed_roots[idx].au));
                        assert(pre.branch_summary[pre.sealed_roots[idx].au]
                            == root_summary_from_read(pre.sealed_roots[idx], post.visible_branch_nodes()));
                        assert(post.interpreted_branch_summary()[au]
                            == root_summary_from_read(post.sealed_roots[idx], post.visible_branch_nodes()));
                        assert(pre.branch_summary[au]
                            == root_summary_from_read(pre.sealed_roots[idx], post.visible_branch_nodes()));
                        assert(post.branch_summary[au] == pre.branch_summary[au]);
                    } else {
                        assert(idx == pre.sealed_roots.len());
                        assert(post.sealed_roots[idx] == root);
                        assert(au == root.au);
                        assert(post.branch_summary[au] == sealed_summary);
                        if post.visible_branch_nodes()[root] is Index {
                            let aux = aux_ptr.unwrap();
                            assert(post.visible_branch_nodes()[aux] == BranchNode::Auxiliary(sealed_summary));
                        } else {
                            assert(root_summary_from_read(root, post.visible_branch_nodes()) == set![root.au]);
                            assert(sealed_summary == set![root.au]) by {
                                assert(sealed_branch.get_summary() == sealed_summary);
                                assert(sealed_branch.root == root);
                                assert(sealed_branch.root() is Leaf);
                                assert(sealed_branch.get_summary() == set![root.au]);
                            }
                        }
                    }
                }
                if post.branch_summary.contains_key(au) {
                    if pre.branch_summary.contains_key(au) {
                        assert(root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat).contains(au));
                        let old_idx = root_aus_up_to_member_has_index(pre.sealed_roots, pre.sealed_roots.len() as nat, au);
                        root_aus_up_to_contains(post.sealed_roots, post.sealed_roots.len() as nat, old_idx);
                        assert(root_aus_up_to(post.sealed_roots, post.sealed_roots.len() as nat).contains(au));
                    } else {
                        assert(au == root.au);
                        root_aus_up_to_contains(post.sealed_roots, post.sealed_roots.len() as nat, pre.sealed_roots.len() as int);
                    }
                    assert(post.interpreted_branch_summary().contains_key(au));
                }
            });
        };

        assert(post.i().sealed_stack.sealed_disk.entries =~=
            pushed_stack.sealed_disk.entries) by {
            let post_entries = post.i().sealed_stack.sealed_disk.entries;
            let pushed_entries = pushed_stack.sealed_disk.entries;
            let pre_sealed_entries = pre.i().sealed_stack.sealed_disk.entries;
            let loose_entries = loose_active_disk.entries;
            let old_summary = summary_aus(pre.branch_summary);
            let new_summary = sealed_branch.get_summary();
            assert(summary_aus(loose_active_summary) == new_summary) by {
                assert_maps_equal!(
                    loose_active_summary,
                    Map::<AU, Summary>::empty().insert(sealed_branch.root.au, new_summary),
                    au => {}
                );
                assert(loose_active_summary.dom().finite());
                lemma_values_finite(loose_active_summary);
                assert(loose_active_summary.contains_key(sealed_branch.root.au));
                assert(loose_active_summary[sealed_branch.root.au] == new_summary);
                assert(loose_active_summary.contains_value(new_summary));
                assert(loose_active_summary.values().contains(new_summary));
                assert forall |au: AU| #[trigger] summary_aus(loose_active_summary).contains(au)
                    <==> new_summary.contains(au)
                by {
                    if summary_aus(loose_active_summary).contains(au) {
                        let summary = lemma_union_set_of_sets_contains(loose_active_summary.values(), au);
                        let root_au = choose |root_au: AU|
                            loose_active_summary.contains_key(root_au)
                            && loose_active_summary[root_au] == summary;
                        assert(root_au == sealed_branch.root.au);
                        assert(summary == new_summary);
                    } else if new_summary.contains(au) {
                        lemma_union_set_of_sets_subset(loose_active_summary.values(), new_summary);
                    }
                };
            };
            assert_maps_equal!(
                post_entries,
                pushed_entries,
                addr => {
                    if post_entries.contains_key(addr) {
                        assert(sealed_nodes_of(post.disk.visible(), post.branch_summary).contains_key(addr));
                        assert(summary_aus(post.branch_summary).contains(addr.au));
                        if old_summary.contains(addr.au) {
                            assert(!new_summary.contains(addr.au));
                            assert(!writes.contains_key(addr)) by {
                                if writes.contains_key(addr) {
                                    assert(write_nodes.contains_key(addr));
                                    if aux_ptr is Some {
                                        assert(addr == root || addr == aux_ptr.unwrap());
                                    } else {
                                        assert(false);
                                    }
                                    assert(new_summary.contains(addr.au));
                                    assert(false);
                                }
                            }
                            assert(pre.disk.visible().contains_key(addr));
                            assert(to_branch_nodes(post.disk.visible())[addr]
                                == to_branch_nodes(pre.disk.visible())[addr]);
                            assert(pre_sealed_entries.contains_key(addr));
                            assert(!loose_entries.contains_key(addr)) by {
                                if loose_entries.contains_key(addr) {
                                    assert(summary_aus(loose_active_summary).contains(addr.au));
                                    assert(new_summary.contains(addr.au));
                                    assert(false);
                                }
                            };
                        } else {
                            assert(new_summary.contains(addr.au));
                            assert(summary_aus(loose_active_summary).contains(addr.au));
                            assert(loose_entries.contains_key(addr));
                        }
                    }
                    if pushed_entries.contains_key(addr) {
                        if loose_entries.contains_key(addr) {
                            assert(summary_aus(loose_active_summary).contains(addr.au));
                            assert(new_summary.contains(addr.au));
                            assert(post.disk.visible().contains_key(addr));
                            assert(summary_aus(post.branch_summary).contains(addr.au));
                        } else {
                            assert(pre_sealed_entries.contains_key(addr));
                            assert(old_summary.contains(addr.au));
                            assert(!new_summary.contains(addr.au));
                            assert(pre.disk.visible().contains_key(addr));
                            assert(post.disk.visible().contains_key(addr));
                            assert(summary_aus(post.branch_summary).contains(addr.au));
                        }
                    }
                }
            );
        };
        assert(post.i().sealed_stack.sealed_disk == pushed_stack.sealed_disk);
        assert(post.i().sealed_stack.sealed_roots == pushed_stack.sealed_roots);
        assert(post.i().sealed_stack == pushed_stack);

        assert(post.i().active_branch == AllocationBranch{
            sealed: false,
            branch: None,
            mini_allocator: pre.i().active_branch.mini_allocator.prune(
                sealed_branch.get_summary()
            ),
        });

        AllocationBranch::build_next_preserves_inv(
            pre.i().active_branch,
            sealed_active,
            crate::allocation_layer::AllocationBranch_v::BuildEvent::Seal{aux_ptr},
            Set::empty(),
            dealloc_aus,
        );
        pre.i().sealed_stack.push_branch_preserves_wf(pre.i().branch_summary, sealed_branch, loose_active_disk);
        pre.i().active_branch.mini_allocator.prune_preserves_wf(sealed_branch.get_summary());
        assert(post.active_branch.wf());
        pre.mini_allocator.prune_preserves_wf(pre.mini_allocator.reserved_aus());
        assert(post.mini_allocator.wf());
        assert(post.persisted_root_count == pre.persisted_root_count);
        assert(post.persisted_root_count <= post.sealed_roots.len());
        assert(post.i().wf());
        assert forall |addr: Address|
            #[trigger] writes.contains_key(addr)
            implies !summary_aus(pre.branch_summary).contains(addr.au)
        by {
            assert(write_nodes.contains_key(addr));
            if aux_ptr is Some {
                assert(addr == root || addr == aux_ptr.unwrap());
                if addr == root {
                    assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                    assert(pre.i().active_branch.mini_allocator.page_is_reserved(root));
                    assert(pre.mini_allocator.page_is_reserved(root));
                    assert(pre.mini_allocator.all_aus().contains(root.au));
                } else {
                    assert(addr == aux_ptr.unwrap());
                    assert(pre.mini_allocator.reserved_aus().contains(addr.au));
                    assert(pre.mini_allocator.all_aus().contains(addr.au));
                }
            } else {
                assert(false);
            }
            assert(pre.i().wf());
        }
        assert(writes.dom().disjoint(addresses_in_aus(summary_aus(pre.branch_summary)))) by {
            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                implies !addresses_in_aus(summary_aus(pre.branch_summary)).contains(addr) by {
                assert(writes.contains_key(addr));
            }
        };
        access_preserves_persisted_prefix_clean(pre, post.disk, reads, writes);
        assert forall |i: int| 0 <= i < pre.persisted_root_count
            implies pre.branch_summary.contains_key(pre.sealed_roots[i].au)
        by {
            assert(pre.sealed_roots.to_set().contains(pre.sealed_roots[i]));
            pre.i().sealed_stack.root_au_in_summary(pre.i().branch_summary, pre.sealed_roots[i]);
            assert(pre.i().branch_summary.contains_key(pre.sealed_roots[i].au));
            assert(pre.i().branch_summary == pre.branch_summary);
        }
        sealed_summary_aus_up_to_push_insert_unchanged(
            pre.sealed_roots,
            pre.branch_summary,
            sealed_branch.root,
            sealed_branch.get_summary(),
            pre.persisted_root_count,
        );
        assert(sealed_summary_aus_up_to(
            post.sealed_roots,
            post.branch_summary,
            post.persisted_root_count,
        ) == sealed_summary_aus_up_to(
            pre.sealed_roots,
            pre.branch_summary,
            pre.persisted_root_count,
        ));
        assert(post.disk.aus_clean_or_evictable(sealed_summary_aus_up_to(
            post.sealed_roots,
            post.branch_summary,
            post.persisted_root_count,
        )));
        assert(active_loaded_nodes_of(post.disk, post.mini_allocator) == Map::<Address, BranchNode>::empty()) by {
            assert_maps_equal!(
                active_loaded_nodes_of(post.disk, post.mini_allocator),
                Map::<Address, BranchNode>::empty(),
                addr => {
                    if active_loaded_nodes_of(post.disk, post.mini_allocator).contains_key(addr) {
                        assert(to_branch_nodes(post.disk.visible()).contains_key(addr));
                        assert(post.mini_allocator.all_aus().contains(addr.au));
                        pre.mini_allocator.prune_preserves_wf(sealed_summary);
                        assert(post.mini_allocator.all_aus()
                            == pre.mini_allocator.all_aus().difference(sealed_summary));
                        assert(pre.mini_allocator.all_aus().contains(addr.au));
                        assert(!sealed_summary.contains(addr.au));
                        if writes.contains_key(addr) {
                            assert(write_nodes.contains_key(addr));
                            assert(write_nodes == loaded_seal_write_nodes(
                                root,
                                read_nodes,
                                aux_ptr,
                                sealed_summary,
                            ));
                            if aux_ptr is Some {
                                assert(addr == root || addr == aux_ptr.unwrap());
                                if addr == root {
                                    assert(sealed_summary.contains(root.au)) by {
                                        assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                                        assert(pre.i().active_branch.mini_allocator.page_is_reserved(root));
                                        assert(pre.mini_allocator.page_is_reserved(root));
                                        assert(pre.mini_allocator.reserved_aus().contains(root.au));
                                    }
                                } else {
                                    assert(addr == aux_ptr.unwrap());
                                    assert(sealed_summary.contains(addr.au));
                                }
                            } else {
                                assert(write_nodes == Map::<Address, BranchNode>::empty());
                                assert(false);
                            }
                            assert(false);
                        } else {
                            assert(pre.disk.visible().contains_key(addr));
                            assert(active_loaded_nodes_of(pre.disk, pre.mini_allocator).contains_key(addr));
                            assert(branch.disk_view.entries.contains_key(addr));
                            assert(pre.i().active_branch.addrs_closed_under_mini_allocator());
                            assert(pre.i().active_branch.mini_allocator.page_is_reserved(addr));
                            assert(pre.mini_allocator.page_is_reserved(addr));
                            assert(pre.mini_allocator.reserved_aus().contains(addr.au));
                            assert(sealed_summary.contains(addr.au));
                            assert(false);
                        }
                    }
                }
            );
        };
    }

    #[inductive(internal_fill_au)]
    fn internal_fill_au_inductive(pre: Self, post: Self, lbl: Label, aus: Set<AU>, new_disk: CachingDisk::State) {
        assert(post.mini_allocator.wf());
        mini_allocator_add_aus_preserves_all_aus(pre.mini_allocator, aus);
        mini_allocator_add_aus_preserves_allocated_addrs(pre.mini_allocator, aus);
        assert(post.sealed_roots == pre.sealed_roots);
        assert(post.branch_summary == pre.branch_summary);
        assert(post.persisted_root_count == pre.persisted_root_count);
        assert(post.active_branch == pre.active_branch);
        assert(post.disk == new_disk);
        assert(post.seq_end == pre.seq_end);
        disk_growth_preserves_loaded_metadata(pre, post.disk, aus);
        assert(post.interpreted_branch_summary() == pre.branch_summary);
        assert(post.branch_metadata_loaded());
        assert(post.loaded_branch_summary_agrees());
        assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
        assert(post.sealed_stack_i() == pre.sealed_stack_i());
        pre.i().sealed_stack.sealed_disk.build_branch_summary_finite(
            pre.i().sealed_stack.sealed_roots.to_set(),
        );
        assert(pre.branch_summary.values().finite());
        sealed_summary_aus_up_to_subset_summary_aus(
            pre.sealed_roots,
            pre.branch_summary,
            pre.persisted_root_count,
        );
        let persisted_aus = sealed_summary_aus_up_to(
            pre.sealed_roots,
            pre.branch_summary,
            pre.persisted_root_count,
        );
        assert(persisted_aus.disjoint(aus)) by {
            assert(persisted_aus <= summary_aus(pre.branch_summary));
            assert forall |au: AU| #[trigger] persisted_aus.contains(au)
                implies !aus.contains(au) by {
                assert(summary_aus(pre.branch_summary).contains(au));
            }
        };
        disk_growth_preserves_aus_clean_or_evictable(
            pre.disk,
            post.disk,
            aus,
            persisted_aus,
        );
        assert(sealed_summary_aus_up_to(
            post.sealed_roots,
            post.interpreted_branch_summary(),
            post.persisted_root_count,
        ) == persisted_aus);
        disk_growth_preserves_active_loaded_nodes(
            pre.disk,
            post.disk,
            pre.mini_allocator,
            post.mini_allocator,
            aus,
        );
        assert(post.active_branch_i() == pre.active_branch_i().mini_allocator_fill(aus));
        AllocationBranch::build_next_preserves_inv(
            pre.active_branch_i(),
            post.active_branch_i(),
            crate::allocation_layer::AllocationBranch_v::BuildEvent::AllocFill{},
            aus,
            Set::empty(),
        );
        assert(post.i().wf());
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CachingDiskBranch::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);

        let step = choose |step| CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                assert(CachingDiskBranch::State::disk_internal(pre, post, lbl, new_disk)) by {
                    reveal(CachingDiskBranch::State::disk_internal);
                }
                CachingDiskBranch::State::disk_internal_inductive(pre, post, lbl, new_disk);
            },
            CachingDiskBranch::Step::observe_persisted_roots(target_count) => {
                assert(CachingDiskBranch::State::observe_persisted_roots(pre, post, lbl, target_count)) by {
                    reveal(CachingDiskBranch::State::observe_persisted_roots);
                }
                CachingDiskBranch::State::observe_persisted_roots_inductive(pre, post, lbl, target_count);
            },
            CachingDiskBranch::Step::load_metadata(reads) => {
                assert(CachingDiskBranch::State::load_metadata(pre, post, lbl, reads)) by {
                    reveal(CachingDiskBranch::State::load_metadata);
                }
                CachingDiskBranch::State::load_metadata_inductive(pre, post, lbl, reads);
            },
            CachingDiskBranch::Step::query(receipts, reads) => {
                assert(CachingDiskBranch::State::query(pre, post, lbl, receipts, reads)) by {
                    reveal(CachingDiskBranch::State::query);
                }
                CachingDiskBranch::State::query_inductive(pre, post, lbl, receipts, reads);
            },
            CachingDiskBranch::Step::append(new_disk, new_active_branch, receipt, init_root, reads, writes) => {
                assert(CachingDiskBranch::State::append(pre, post, lbl, new_disk, new_active_branch, receipt, init_root, reads, writes)) by {
                    reveal(CachingDiskBranch::State::append);
                }
                CachingDiskBranch::State::append_inductive(pre, post, lbl, new_disk, new_active_branch, receipt, init_root, reads, writes);
            },
            CachingDiskBranch::Step::freeze_as() => {
                assert(CachingDiskBranch::State::freeze_as(pre, post, lbl)) by {
                    reveal(CachingDiskBranch::State::freeze_as);
                }
                CachingDiskBranch::State::freeze_as_inductive(pre, post, lbl);
            },
            CachingDiskBranch::Step::freeze_prepared() => {
                assert(CachingDiskBranch::State::freeze_prepared(pre, post, lbl)) by {
                    reveal(CachingDiskBranch::State::freeze_prepared);
                }
            },
            CachingDiskBranch::Step::internal_noop() => {
                assert(CachingDiskBranch::State::internal_noop(pre, post, lbl)) by {
                    reveal(CachingDiskBranch::State::internal_noop);
                }
                CachingDiskBranch::State::internal_noop_inductive(pre, post, lbl);
            },
            CachingDiskBranch::Step::internal_grow(new_disk, new_root_addr, reads, writes) => {
                assert(CachingDiskBranch::State::internal_grow(pre, post, lbl, new_disk, new_root_addr, reads, writes)) by {
                    reveal(CachingDiskBranch::State::internal_grow);
                }
                CachingDiskBranch::State::internal_grow_inductive(pre, post, lbl, new_disk, new_root_addr, reads, writes);
            },
            CachingDiskBranch::Step::internal_split(new_disk, new_child_addr, receipt, split_arg, reads, writes) => {
                assert(CachingDiskBranch::State::internal_split(pre, post, lbl, new_disk, new_child_addr, receipt, split_arg, reads, writes)) by {
                    reveal(CachingDiskBranch::State::internal_split);
                }
                CachingDiskBranch::State::internal_split_inductive(pre, post, lbl, new_disk, new_child_addr, receipt, split_arg, reads, writes);
            },
            CachingDiskBranch::Step::internal_seal(written_disk, aux_ptr, reads, writes) => {
                assert(CachingDiskBranch::State::internal_seal(pre, post, lbl, written_disk, aux_ptr, reads, writes)) by {
                    reveal(CachingDiskBranch::State::internal_seal);
                }
                CachingDiskBranch::State::internal_seal_inductive(pre, post, lbl, written_disk, aux_ptr, reads, writes);
            },
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                assert(CachingDiskBranch::State::internal_fill_au(pre, post, lbl, aus, new_disk)) by {
                    reveal(CachingDiskBranch::State::internal_fill_au);
                }
                CachingDiskBranch::State::internal_fill_au_inductive(pre, post, lbl, aus, new_disk);
            },
            _ => {
                assert(post.inv());
            },
        }
    }

    pub proof fn next_preserves_persisted_root_count_lower_bound(
        pre: Self,
        post: Self,
        lbl: Label,
        bound: nat,
    )
        requires
            CachingDiskBranch::State::next(pre, post, lbl),
            bound <= pre.persisted_root_count,
        ensures
            bound <= post.persisted_root_count,
    {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step| CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                assert(CachingDiskBranch::State::disk_internal(pre, post, lbl, new_disk));
            },
            CachingDiskBranch::Step::observe_persisted_roots(target_count) => {
                assert(CachingDiskBranch::State::observe_persisted_roots(pre, post, lbl, target_count));
            },
            CachingDiskBranch::Step::load_metadata(reads) => {
                assert(CachingDiskBranch::State::load_metadata(pre, post, lbl, reads));
            },
            CachingDiskBranch::Step::query(receipts, reads) => {
                assert(CachingDiskBranch::State::query(pre, post, lbl, receipts, reads));
            },
            CachingDiskBranch::Step::append(new_disk, new_active_branch, receipt, init_root, reads, writes) => {
                assert(CachingDiskBranch::State::append(pre, post, lbl, new_disk, new_active_branch, receipt, init_root, reads, writes));
            },
            CachingDiskBranch::Step::freeze_as() => {
                assert(CachingDiskBranch::State::freeze_as(pre, post, lbl));
            },
            CachingDiskBranch::Step::freeze_prepared() => {
                assert(CachingDiskBranch::State::freeze_prepared(pre, post, lbl));
            },
            CachingDiskBranch::Step::internal_noop() => {
                assert(CachingDiskBranch::State::internal_noop(pre, post, lbl));
            },
            CachingDiskBranch::Step::internal_grow(new_disk, new_root_addr, reads, writes) => {
                assert(CachingDiskBranch::State::internal_grow(pre, post, lbl, new_disk, new_root_addr, reads, writes));
            },
            CachingDiskBranch::Step::internal_split(new_disk, new_child_addr, receipt, split_arg, reads, writes) => {
                assert(CachingDiskBranch::State::internal_split(pre, post, lbl, new_disk, new_child_addr, receipt, split_arg, reads, writes));
            },
            CachingDiskBranch::Step::internal_seal(written_disk, aux_ptr, reads, writes) => {
                assert(CachingDiskBranch::State::internal_seal(pre, post, lbl, written_disk, aux_ptr, reads, writes));
            },
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                assert(CachingDiskBranch::State::internal_fill_au(pre, post, lbl, aus, new_disk));
            },
            _ => {
                assert(false);
            },
        }
    }
}}

impl CachingDiskBranch::State {
    pub proof fn loaded_interpreted_wf(self)
        requires
            self.inv(),
            self.metadata_loaded,
        ensures
	            self.i().wf(),
	            self.i().sealed_stack == self.sealed_stack_i(),
	            self.i().branch_summary == self.branch_summary,
	    {
	        assert(self.branch_metadata_loaded());
	        assert(self.i().sealed_stack == self.sealed_stack_i());
        assert(self.i().branch_summary == self.branch_summary);
        assert(summary_aus(self.i().branch_summary).disjoint(self.i().active_branch.mini_allocator.all_aus()));
        assert(self.i().wf());
    }

    pub proof fn loaded_summary_aus_disjoint_mini_allocator(self)
        requires
            self.inv(),
            self.metadata_loaded,
        ensures
            summary_aus(self.branch_summary).disjoint(self.mini_allocator.all_aus()),
    {
        assert(self.branch_metadata_loaded());
        assert(self.branch_summary == self.interpreted_branch_summary());
    }

    pub proof fn loaded_index_root_aux_in_summary(self, root: Address, aux: Address)
        requires
            self.inv(),
            self.metadata_loaded,
            self.sealed_roots.to_set().contains(root),
            self.visible_branch_nodes().contains_key(root),
            self.visible_branch_nodes()[root] is Index,
            self.visible_branch_nodes()[root]->aux_ptr == Some(aux),
        ensures
            self.branch_summary.contains_key(root.au),
            self.branch_summary[root.au].contains(aux.au),
            summary_aus(self.branch_summary).contains(aux.au),
    {
        assert(self.branch_metadata_loaded());
        assert(self.branch_summary == self.interpreted_branch_summary());
        assert(self.sealed_stack_i().wf(self.branch_summary));
        self.sealed_stack_i().root_au_in_summary(self.branch_summary, root);
        self.sealed_stack_i().tight_branch_facts(self.branch_summary, root);
        let branch = self.sealed_stack_i().tight_branch(root, self.branch_summary[root.au]);
        assert(tight_branch_in_loose_disk(
            self.sealed_stack_i().sealed_disk,
            root,
            self.branch_summary[root.au],
            branch,
        ));
        assert(branch.disk_view.entries.contains_key(root));
        assert(branch.disk_view.entries[root] == branch.root());
        assert(branch.disk_view.entries <= self.sealed_stack_i().sealed_disk.entries);
        assert(self.sealed_stack_i().sealed_disk.entries.contains_key(root));
        assert(self.sealed_stack_i().sealed_disk.entries[root] == branch.disk_view.entries[root]);
        assert(self.sealed_stack_i().sealed_disk.entries[root] == self.visible_branch_nodes()[root]) by {
            assert(summary_aus(self.branch_summary).contains(root.au));
            assert(sealed_nodes_of(self.disk.visible(), self.branch_summary).contains_key(root));
        };
        assert(branch.root() == self.visible_branch_nodes()[root]);
        assert(branch.root() is Index);
        assert(branch.root()->aux_ptr == Some(aux));
        assert(branch.sealed_root());
        assert(branch.disk_view.valid_address(aux));
        assert(branch.disk_view.entries.contains_key(aux));
        assert(branch.full_repr().contains(aux));
        assert(addrs_closed(branch.full_repr(), branch.get_summary()));
        assert(branch.get_summary() == self.branch_summary[root.au]);
        assert(self.branch_summary[root.au].contains(aux.au));
        assert(self.branch_summary.values().contains(self.branch_summary[root.au]));
        lemma_union_set_of_sets_subset(self.branch_summary.values(), self.branch_summary[root.au]);
    }

    pub open spec fn sealed_stack_i(self) -> SealedAllocationBranchStack {
        SealedAllocationBranchStack{
            sealed_roots: self.sealed_roots,
            sealed_disk: BufferDisk{entries: sealed_nodes_of(
                self.disk.visible(),
                self.interpreted_branch_summary(),
            )},
        }
    }

    pub open spec fn interpreted_sealed_stack_i(self) -> SealedAllocationBranchStack {
        self.sealed_stack_i()
    }

    pub open spec fn active_branch_i(self) -> AllocationBranch {
        active_branch_i_of(self.active_branch, self.mini_allocator, self.disk)
    }

    pub open spec fn accessible_aus(self) -> Set<AU> {
        summary_aus(self.branch_summary)
            + self.mini_allocator.all_aus()
            + to_aus(self.disk.visible().dom())
    }

    pub open spec fn full_accessible_aus(self) -> Set<AU> {
        summary_aus(self.interpreted_branch_summary())
            + self.mini_allocator.all_aus()
            + to_aus(self.disk.visible().dom())
    }

	    pub proof fn metadata_loaded_full_accessible_eq(self)
	        requires
	            self.inv(),
	            self.metadata_loaded,
	        ensures
	            self.full_accessible_aus() == self.accessible_aus(),
	    {
	        assert(self.branch_metadata_loaded());
	        assert(self.interpreted_branch_summary() == self.branch_summary);
	    }

    pub open spec fn i(self) -> AllocationBranchStack::State {
        let sealed_stack = self.sealed_stack_i();
        AllocationBranchStack::State{
            sealed_stack,
            branch_summary: self.interpreted_branch_summary(),
            active_branch: self.active_branch_i(),
            seq_end: self.seq_end,
        }
    }

    pub proof fn access_disk_aus_subset(
        pre: Self,
        post_disk: CachingDisk::State,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            CachingDisk::State::next(
                pre.disk,
                post_disk,
                CachingDisk::Label::Access{reads, writes},
            ),
            to_aus(writes.dom()) <= pre.accessible_aus(),
        ensures
            to_aus(post_disk.visible().dom()) <= pre.accessible_aus(),
    {
        CachingDisk::State::access_visible_effect(pre.disk, post_disk, reads, writes);
        assert forall |au: AU| #[trigger] to_aus(post_disk.visible().dom()).contains(au)
            implies pre.accessible_aus().contains(au) by {
            let addr = choose |addr: Address|
                post_disk.visible().dom().contains(addr) && addr.au == au;
            if pre.disk.visible().dom().contains(addr) {
                crate::disk::GenericDisk_v::to_aus_domain(pre.disk.visible().dom());
                assert(to_aus(pre.disk.visible().dom()).contains(au));
            } else {
                assert(writes.dom().contains(addr));
                crate::disk::GenericDisk_v::to_aus_domain(writes.dom());
                assert(to_aus(writes.dom()).contains(au));
            }
        }
    }

    pub proof fn append_preserves_accessible_aus(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranch::Label,
    )
        requires
            pre.inv(),
            CachingDiskBranch::State::next(pre, post, lbl),
            lbl is AppendLabel,
        ensures
            pre.metadata_loaded,
            post.metadata_loaded,
            post.accessible_aus() <= pre.accessible_aus(),
    {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::append(new_disk, new_active_branch, receipt, init_root, reads, writes) => {
                assert(CachingDiskBranch::State::append(
                    pre, post, lbl, new_disk, new_active_branch, receipt, init_root, reads, writes,
                )) by {
                    reveal(CachingDiskBranch::State::append);
                }
                reveal(CachingDiskBranch::State::append);
                match lbl {
                    CachingDiskBranch::Label::AppendLabel{keys, msgs} => {
                        if pre.active_branch.root is Some {
                            assert(init_root is None);
                            let read_nodes = to_branch_nodes(reads);
                            let write_nodes = to_branch_nodes(writes);
                            let branch_lbl = CachedBranch::Label::Append{
                                mini_allocator: pre.mini_allocator,
                                receipt,
                                keys,
                                msgs,
                                read_nodes,
                                write_nodes,
                            };
                            assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                            reveal(CachedBranch::State::next);
                            reveal(CachedBranch::State::next_by);
                            let cb_step = choose |step: CachedBranch::Step|
                                CachedBranch::State::next_by(pre.active_branch, new_active_branch, branch_lbl, step);
                            match cb_step {
                                CachedBranch::Step::append_step() => {
                                    assert(CachedBranch::State::append_step(pre.active_branch, new_active_branch, branch_lbl)) by {
                                        reveal(CachedBranch::State::append_step);
                                    }
                                },
                                _ => { assert(false); },
                            }
                            assert(new_active_branch == pre.active_branch);
                        } else {
                            assert(init_root is Some);
                            let init_addr = init_root.unwrap();
                            let write_nodes = to_branch_nodes(writes);
                            let branch_lbl = CachedBranch::Label::Initialize{
                                mini_allocator: pre.mini_allocator,
                                init_root: init_addr,
                                keys,
                                msgs,
                                write_nodes,
                            };
                            assert(CachedBranch::State::next(pre.active_branch, new_active_branch, branch_lbl));
                            reveal(CachedBranch::State::next);
                            reveal(CachedBranch::State::next_by);
                            let cb_step = choose |step: CachedBranch::Step|
                                CachedBranch::State::next_by(pre.active_branch, new_active_branch, branch_lbl, step);
                            match cb_step {
                                CachedBranch::Step::initialize_branch() => {
                                    assert(CachedBranch::State::initialize_branch(pre.active_branch, new_active_branch, branch_lbl)) by {
                                        reveal(CachedBranch::State::initialize_branch);
                                    }
                                },
                                _ => { assert(false); },
                            }
                            assert(new_active_branch == CachedBranch::State{root: Some(init_addr)});
	                        }
                    },
                    _ => { assert(false); },
                }
                assert(post.branch_summary == pre.branch_summary);
                assert(to_aus(writes.dom()) <= pre.accessible_aus()) by {
                    assert forall |au: AU| #[trigger] to_aus(writes.dom()).contains(au)
                        implies pre.accessible_aus().contains(au) by {
                        let addr = choose |addr: Address| writes.dom().contains(addr) && addr.au == au;
                        if pre.active_branch.root is Some {
                            let read_nodes = to_branch_nodes(reads);
                            let write_nodes = to_branch_nodes(writes);
                            match lbl {
                                CachingDiskBranch::Label::AppendLabel{keys, msgs} => {
                                    let branch_lbl = CachedBranch::Label::Append{
                                        mini_allocator: pre.mini_allocator,
                                        receipt,
                                        keys,
                                        msgs,
                                        read_nodes,
                                        write_nodes,
                                    };
                                    assert(CachedBranch::State::next(pre.active_branch, pre.active_branch, branch_lbl));
                                    reveal(CachedBranch::State::next);
                                    reveal(CachedBranch::State::next_by);
                                    let cb_step = choose |step: CachedBranch::Step|
                                        CachedBranch::State::next_by(pre.active_branch, pre.active_branch, branch_lbl, step);
                                    match cb_step {
                                        CachedBranch::Step::append_step() => {
                                            assert(CachedBranch::State::append_step(pre.active_branch, pre.active_branch, branch_lbl)) by {
                                                reveal(CachedBranch::State::append_step);
                                            }
                                            assert(write_nodes == loaded_append_write_nodes(receipt, keys, msgs));
                                            assert(write_nodes.contains_key(addr));
                                            assert(addr == receipt.target().addr);
                                            assert(receipt.needed_addrs().contains(addr)) by {
                                                let i = receipt.lines.len() - 1;
                                                assert(0 <= i < receipt.lines.len());
                                                assert(receipt.lines[i].addr == addr);
                                            }
                                            assert(reads.dom().contains(addr));
                                            assert(reads.contains_key(addr));
                                            reveal(CachingDisk::State::next);
                                            reveal(CachingDisk::State::next_by);
                                            assert(CachingDisk::State::access(
                                                pre.disk,
                                                post.disk,
                                                CachingDisk::Label::Access{reads, writes},
                                            )) by {
                                                reveal(CachingDisk::State::access);
                                            }
                                            assert(pre.disk.cache.contains_key(addr));
                                            assert(pre.disk.visible().dom().contains(addr));
                                            crate::disk::GenericDisk_v::to_aus_domain(pre.disk.visible().dom());
                                            assert(to_aus(pre.disk.visible().dom()).contains(au));
                                        },
                                        _ => { assert(false); },
                                    }
                                },
                                _ => { assert(false); },
                            }
                        } else {
                            assert(init_root is Some);
                            let init_addr = init_root.unwrap();
	                            match lbl {
                                CachingDiskBranch::Label::AppendLabel{keys, msgs} => {
                                    let write_nodes = to_branch_nodes(writes);
                                    assert(write_nodes == loaded_initialize_write_nodes(init_addr, keys, msgs));
                                    assert(write_nodes.contains_key(addr));
                                    assert(addr == init_addr);
                                    let branch_lbl = CachedBranch::Label::Initialize{
                                        mini_allocator: pre.mini_allocator,
                                        init_root: init_addr,
                                        keys,
                                        msgs,
                                        write_nodes,
                                    };
                                    assert(CachedBranch::State::next(
                                        pre.active_branch,
                                        CachedBranch::State{root: Some(init_addr)},
                                        branch_lbl,
                                    ));
                                    reveal(CachedBranch::State::next);
                                    reveal(CachedBranch::State::next_by);
                                    let cb_step = choose |step: CachedBranch::Step|
                                        CachedBranch::State::next_by(
                                            pre.active_branch,
                                            CachedBranch::State{root: Some(init_addr)},
                                            branch_lbl,
                                            step,
                                        );
                                    match cb_step {
                                        CachedBranch::Step::initialize_branch() => {
                                            assert(CachedBranch::State::initialize_branch(
                                                pre.active_branch,
                                                CachedBranch::State{root: Some(init_addr)},
                                                branch_lbl,
                                            )) by {
                                                reveal(CachedBranch::State::initialize_branch);
                                            }
                                        },
                                        _ => { assert(false); },
                                    }
                                    assert(pre.mini_allocator.can_allocate(init_addr));
                                    assert(pre.mini_allocator.all_aus().contains(au));
                                },
                                _ => { assert(false); },
                            }
                        }
                    }
                }
                CachingDiskBranch::State::access_disk_aus_subset(pre, post.disk, reads, writes);
                assert(post.mini_allocator.all_aus() <= pre.mini_allocator.all_aus()) by {
                    if pre.active_branch.root is Some {
                        assert(post.mini_allocator == pre.mini_allocator);
                    } else {
                        assert(init_root is Some);
                        mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, init_root.unwrap());
                    }
                }
                assert forall |au: AU| #[trigger] post.accessible_aus().contains(au)
                    implies pre.accessible_aus().contains(au) by {
                    if summary_aus(post.branch_summary).contains(au) {
                    } else if post.mini_allocator.all_aus().contains(au) {
                    } else {
                        assert(to_aus(post.disk.visible().dom()).contains(au));
                    }
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_preserves_accessible_aus(pre: Self, post: Self)
        requires
            pre.inv(),
            CachingDiskBranch::State::next(pre, post, CachingDiskBranch::Label::Internal),
        ensures
            post.accessible_aus() <= pre.accessible_aus(),
    {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let lbl = CachingDiskBranch::Label::Internal;
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                assert(CachingDiskBranch::State::disk_internal(pre, post, lbl, new_disk)) by {
                    reveal(CachingDiskBranch::State::disk_internal);
                }
                CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
                assert(post.branch_summary == pre.branch_summary);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(to_aus(post.disk.visible().dom()) == to_aus(pre.disk.visible().dom()));
            },
            CachingDiskBranch::Step::observe_persisted_roots(target_count) => {
                assert(CachingDiskBranch::State::observe_persisted_roots(pre, post, lbl, target_count)) by {
                    reveal(CachingDiskBranch::State::observe_persisted_roots);
                }
                assert(post.branch_summary == pre.branch_summary);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(post.disk == pre.disk);
            },
            CachingDiskBranch::Step::freeze_as() => {
                assert(CachingDiskBranch::State::freeze_as(pre, post, lbl)) by {
                    reveal(CachingDiskBranch::State::freeze_as);
                }
                assert(post == pre);
            },
            CachingDiskBranch::Step::internal_noop() => {
                assert(CachingDiskBranch::State::internal_noop(pre, post, lbl)) by {
                    reveal(CachingDiskBranch::State::internal_noop);
                }
                assert(post == pre);
            },
            CachingDiskBranch::Step::internal_grow(new_disk, new_root_addr, reads, writes) => {
                assert(CachingDiskBranch::State::internal_grow(pre, post, lbl, new_disk, new_root_addr, reads, writes)) by {
                    reveal(CachingDiskBranch::State::internal_grow);
                }
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let branch_lbl = CachedBranch::Label::Grow{
                    mini_allocator: pre.mini_allocator,
                    new_root_addr,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(
                    pre.active_branch,
                    CachedBranch::State{root: Some(new_root_addr)},
                    branch_lbl,
                ));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                let cb_step = choose |step: CachedBranch::Step|
                    CachedBranch::State::next_by(
                        pre.active_branch,
                        CachedBranch::State{root: Some(new_root_addr)},
                        branch_lbl,
                        step,
                    );
                match cb_step {
                    CachedBranch::Step::grow_step() => {
                        assert(CachedBranch::State::grow_step(
                            pre.active_branch,
                            CachedBranch::State{root: Some(new_root_addr)},
                            branch_lbl,
                        )) by {
                            reveal(CachedBranch::State::grow_step);
                        }
                    },
                    _ => { assert(false); },
                }
                assert(pre.mini_allocator.can_allocate(new_root_addr));
                mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, new_root_addr);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(to_aus(writes.dom()) <= pre.accessible_aus()) by {
                    assert forall |au: AU| #[trigger] to_aus(writes.dom()).contains(au)
                        implies pre.accessible_aus().contains(au) by {
                        let addr = choose |addr: Address| writes.dom().contains(addr) && addr.au == au;
                        assert(write_nodes == loaded_grow_write_nodes(pre.active_branch.root.unwrap(), new_root_addr));
                        assert(write_nodes.contains_key(addr));
                        assert(addr == new_root_addr);
                        assert(pre.mini_allocator.all_aus().contains(au));
                    }
                }
                CachingDiskBranch::State::access_disk_aus_subset(pre, post.disk, reads, writes);
                assert(post.branch_summary == pre.branch_summary);
            },
            CachingDiskBranch::Step::internal_split(new_disk, new_child_addr, receipt, split_arg, reads, writes) => {
                assert(CachingDiskBranch::State::internal_split(pre, post, lbl, new_disk, new_child_addr, receipt, split_arg, reads, writes)) by {
                    reveal(CachingDiskBranch::State::internal_split);
                }
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let branch_lbl = CachedBranch::Label::Split{
                    mini_allocator: pre.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, pre.active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                let cb_step = choose |step: CachedBranch::Step|
                    CachedBranch::State::next_by(pre.active_branch, pre.active_branch, branch_lbl, step);
                match cb_step {
                    CachedBranch::Step::split_step() => {
                        assert(CachedBranch::State::split_step(pre.active_branch, pre.active_branch, branch_lbl)) by {
                            reveal(CachedBranch::State::split_step);
                        }
                    },
                    _ => { assert(false); },
                }
                assert(pre.mini_allocator.can_allocate(new_child_addr));
                mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, new_child_addr);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                CachingDisk::State::access_visible_effect(pre.disk, post.disk, reads, writes);
                assert(to_aus(writes.dom()) <= pre.accessible_aus()) by {
                    assert forall |au: AU| #[trigger] to_aus(writes.dom()).contains(au)
                        implies pre.accessible_aus().contains(au) by {
                        let addr = choose |addr: Address| writes.dom().contains(addr) && addr.au == au;
                        assert(write_nodes == loaded_split_write_nodes(receipt, read_nodes, split_arg, new_child_addr));
                        assert(write_nodes.contains_key(addr));
                        if addr == new_child_addr {
                            assert(pre.mini_allocator.all_aus().contains(au));
                        } else {
                            assert(reads.dom().contains(addr)) by {
                                if addr == receipt.target().addr {
                                    assert(receipt.needed_addrs().contains(addr));
                                    assert(split_read_addrs(receipt).contains(addr));
                                } else {
                                    assert(addr == receipt.child_addr());
                                    assert(split_read_addrs(receipt).contains(addr));
                                }
                            }
                            assert(pre.disk.cache.contains_key(addr));
                            assert(pre.disk.visible().dom().contains(addr));
                            crate::disk::GenericDisk_v::to_aus_domain(pre.disk.visible().dom());
                            assert(to_aus(pre.disk.visible().dom()).contains(au));
                        }
                    }
                }
                CachingDiskBranch::State::access_disk_aus_subset(pre, post.disk, reads, writes);
                assert(post.branch_summary == pre.branch_summary);
            },
            CachingDiskBranch::Step::internal_seal(written_disk, aux_ptr, reads, writes) => {
                assert(CachingDiskBranch::State::internal_seal(pre, post, lbl, written_disk, aux_ptr, reads, writes)) by {
                    reveal(CachingDiskBranch::State::internal_seal);
                }
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let branch_lbl = CachedBranch::Label::Seal{
                    mini_allocator: pre.mini_allocator,
                    aux_ptr,
                    read_nodes,
                    write_nodes,
                };
                assert(CachedBranch::State::next(pre.active_branch, pre.active_branch, branch_lbl));
                reveal(CachedBranch::State::next);
                reveal(CachedBranch::State::next_by);
                let cb_step = choose |step: CachedBranch::Step|
                    CachedBranch::State::next_by(pre.active_branch, pre.active_branch, branch_lbl, step);
                match cb_step {
                    CachedBranch::Step::seal_step() => {
                        assert(CachedBranch::State::seal_step(pre.active_branch, pre.active_branch, branch_lbl)) by {
                            reveal(CachedBranch::State::seal_step);
                        }
                    },
                    _ => { assert(false); },
                }
                let sealed_summary = pre.mini_allocator.reserved_aus();
                pre.mini_allocator.prune_preserves_wf(sealed_summary);
                assert(post.mini_allocator.all_aus()
                    == pre.mini_allocator.all_aus().difference(sealed_summary));
                assert(summary_aus(post.branch_summary) <= summary_aus(pre.branch_summary) + pre.mini_allocator.all_aus()) by {
                    pre.i().sealed_stack.sealed_disk.build_branch_summary_finite(
                        pre.i().sealed_stack.sealed_roots.to_set(),
                    );
                    assert(pre.branch_summary.values().finite());
                    assert(post.branch_summary.values().finite()) by {
                        assert(post.branch_summary == pre.branch_summary.insert(
                            pre.active_branch.root.unwrap().au,
                            sealed_summary,
                        ));
                        lemma_values_finite(post.branch_summary);
                    }
                    assert forall |au: AU| #[trigger] summary_aus(post.branch_summary).contains(au)
                        implies (summary_aus(pre.branch_summary) + pre.mini_allocator.all_aus()).contains(au) by {
                        if !summary_aus(pre.branch_summary).contains(au) {
                            assert(post.branch_summary == pre.branch_summary.insert(
                                pre.active_branch.root.unwrap().au,
                                sealed_summary,
                            ));
                            let summary = lemma_union_set_of_sets_contains(post.branch_summary.values(), au);
                            if summary != sealed_summary {
                                assert(pre.branch_summary.values().contains(summary));
                                lemma_union_set_of_sets_subset(pre.branch_summary.values(), summary);
                                assert(summary_aus(pre.branch_summary).contains(au));
                                assert(false);
                            }
                            assert(summary.contains(au));
                            assert(pre.mini_allocator.all_aus().contains(au));
                        }
                    }
                }
                CachingDisk::State::access_visible_effect(pre.disk, post.disk, reads, writes);
                assert(to_aus(writes.dom()) <= pre.accessible_aus()) by {
                    assert forall |au: AU| #[trigger] to_aus(writes.dom()).contains(au)
                        implies pre.accessible_aus().contains(au) by {
                        let addr = choose |addr: Address| writes.dom().contains(addr) && addr.au == au;
                        assert(write_nodes == loaded_seal_write_nodes(
                            pre.active_branch.root.unwrap(),
                            read_nodes,
                            aux_ptr,
                            pre.mini_allocator.reserved_aus(),
                        ));
                        assert(write_nodes.contains_key(addr));
                        if aux_ptr is Some && addr == aux_ptr.unwrap() {
                            assert(pre.mini_allocator.reserved_aus().contains(au));
                            assert(pre.mini_allocator.all_aus().contains(au));
                        } else {
                            assert(addr == pre.active_branch.root.unwrap());
                            assert(reads.contains_key(addr));
                            assert(pre.disk.cache.contains_key(addr));
                            assert(pre.disk.visible().dom().contains(addr));
                            crate::disk::GenericDisk_v::to_aus_domain(pre.disk.visible().dom());
                            assert(to_aus(pre.disk.visible().dom()).contains(au));
                        }
                    }
                }
                CachingDiskBranch::State::access_disk_aus_subset(pre, post.disk, reads, writes);
                assert forall |au: AU| #[trigger] post.accessible_aus().contains(au)
                    implies pre.accessible_aus().contains(au) by {
                    if summary_aus(post.branch_summary).contains(au) {
                        if summary_aus(pre.branch_summary).contains(au) {
                        } else {
                            assert(pre.mini_allocator.all_aus().contains(au));
                        }
                    } else if post.mini_allocator.all_aus().contains(au) {
                        assert(pre.mini_allocator.all_aus().contains(au));
                    } else {
                        assert(to_aus(post.disk.visible().dom()).contains(au));
                    }
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_preserves_full_accessible_aus(pre: Self, post: Self)
        requires
            pre.inv(),
            CachingDiskBranch::State::next(pre, post, CachingDiskBranch::Label::Internal),
        ensures
            post.full_accessible_aus() <= pre.full_accessible_aus(),
    {
        CachingDiskBranch::State::internal_preserves_accessible_aus(pre, post);
        CachingDiskBranch::State::inv_next(pre, post, CachingDiskBranch::Label::Internal);
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let lbl = CachingDiskBranch::Label::Internal;
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                assert(CachingDiskBranch::State::disk_internal(pre, post, lbl, new_disk)) by {
                    reveal(CachingDiskBranch::State::disk_internal);
                }
                CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.disk.visible() == pre.disk.visible());
                assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
                assert(post.mini_allocator == pre.mini_allocator);
            },
            CachingDiskBranch::Step::observe_persisted_roots(target_count) => {
                assert(CachingDiskBranch::State::observe_persisted_roots(pre, post, lbl, target_count)) by {
                    reveal(CachingDiskBranch::State::observe_persisted_roots);
                }
                assert(post.disk == pre.disk);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
                assert(post.mini_allocator == pre.mini_allocator);
            },
            CachingDiskBranch::Step::freeze_as() => {
                assert(CachingDiskBranch::State::freeze_as(pre, post, lbl)) by {
                    reveal(CachingDiskBranch::State::freeze_as);
                }
                assert(post == pre);
            },
            CachingDiskBranch::Step::internal_noop() => {
                assert(CachingDiskBranch::State::internal_noop(pre, post, lbl)) by {
                    reveal(CachingDiskBranch::State::internal_noop);
                }
                assert(post == pre);
            },
            _ => {
                assert(pre.metadata_loaded);
                assert(post.metadata_loaded);
                pre.metadata_loaded_full_accessible_eq();
                post.metadata_loaded_full_accessible_eq();
                assert(post.accessible_aus() <= pre.accessible_aus());
            },
        }
    }

    pub proof fn load_metadata_preserves_full_accessible_aus(
        pre: Self,
        post: Self,
        root: Address,
        discovered_aus: Set<AU>,
    )
        requires
            pre.inv(),
            CachingDiskBranch::State::next(
                pre,
                post,
                CachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
            ),
        ensures
            post.full_accessible_aus() == pre.full_accessible_aus(),
    {
        let lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::load_metadata(reads) => {
                assert(CachingDiskBranch::State::load_metadata(pre, post, lbl, reads)) by {
                    reveal(CachingDiskBranch::State::load_metadata);
                }
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.disk == pre.disk);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary()) by {
                    assert_maps_equal!(
                        post.interpreted_branch_summary(),
                        pre.interpreted_branch_summary(),
                        au => {}
                    );
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn load_metadata_discovered_aus_subset_full_accessible(
        pre: Self,
        post: Self,
        root: Address,
        discovered_aus: Set<AU>,
    )
        requires
            pre.inv(),
            CachingDiskBranch::State::next(
                pre,
                post,
                CachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
            ),
        ensures
            discovered_aus <= pre.full_accessible_aus(),
    {
        let lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::load_metadata(reads) => {
                assert(CachingDiskBranch::State::load_metadata(pre, post, lbl, reads)) by {
                    reveal(CachingDiskBranch::State::load_metadata);
                }
                CachingDiskBranch::State::inv_next(pre, post, lbl);
                assert(post.inv());
                assert(post.disk == pre.disk);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.visible_branch_nodes() == pre.visible_branch_nodes()) by {
                    assert_maps_equal!(
                        post.visible_branch_nodes(),
                        pre.visible_branch_nodes(),
                        addr => {}
                    );
                }
                assert(post.interpreted_branch_summary()
                    == pre.interpreted_branch_summary()) by {
                    assert_maps_equal!(
                        post.interpreted_branch_summary(),
                        pre.interpreted_branch_summary(),
                        au => {}
                    );
                }
                let idx = choose |i: int| 0 <= i < pre.sealed_roots.len()
                    && pre.sealed_roots[i] == root;
                assert(0 <= idx < pre.sealed_roots.len());
                assert(post.sealed_roots[idx] == root);
                assert(post.branch_summary == pre.branch_summary.insert(root.au, discovered_aus));
                assert(post.branch_summary.contains_key(root.au));
                assert(post.branch_summary[root.au] == discovered_aus);
                assert(post.loaded_branch_summary_agrees());
                assert(discovered_aus == root_summary_from_read(
                    root,
                    post.visible_branch_nodes(),
                ));
                assert(discovered_aus == root_summary_from_read(
                    root,
                    pre.visible_branch_nodes(),
                ));
                assert(crate::disk::GenericDisk_v::set_addrs_disjoint_aus(
                    pre.sealed_roots.to_set(),
                )) by {
                    assert(pre.sealed_stack_i().wf(pre.interpreted_branch_summary()));
                }
                branch_summary_from_reads_up_to_self_ensures(
                    pre.sealed_roots,
                    pre.visible_branch_nodes(),
                    pre.sealed_roots.len() as nat,
                );
                root_aus_up_to_full(pre.sealed_roots);
                to_aus_finite(pre.sealed_roots.to_set());
                assert(pre.interpreted_branch_summary().dom().finite());
                lemma_values_finite(pre.interpreted_branch_summary());
                assert(pre.interpreted_branch_summary()[root.au] == discovered_aus);
                assert(pre.interpreted_branch_summary().values().contains(discovered_aus));
                assert forall |au: AU| #[trigger] discovered_aus.contains(au)
                    implies pre.full_accessible_aus().contains(au) by {
                    assert(summary_aus(pre.interpreted_branch_summary()).contains(au)) by {
                        lemma_union_set_of_sets_subset(
                            pre.interpreted_branch_summary().values(),
                            discovered_aus,
                        );
                    }
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn load_metadata_accessible_aus_growth(
        pre: Self,
        post: Self,
        root: Address,
        discovered_aus: Set<AU>,
    )
        requires
            pre.inv(),
            CachingDiskBranch::State::next(
                pre,
                post,
                CachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
            ),
        ensures
            post.accessible_aus() <= pre.accessible_aus() + discovered_aus,
    {
        let lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::load_metadata(reads) => {
                assert(CachingDiskBranch::State::load_metadata(pre, post, lbl, reads)) by {
                    reveal(CachingDiskBranch::State::load_metadata);
                }
                assert(post.disk == pre.disk);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(summary_aus(post.branch_summary) <= summary_aus(pre.branch_summary) + discovered_aus) by {
                    lemma_values_finite(post.branch_summary);
                    assert forall |au: AU| #[trigger] summary_aus(post.branch_summary).contains(au)
                        implies (summary_aus(pre.branch_summary) + discovered_aus).contains(au) by {
                        let summary = lemma_union_set_of_sets_contains(post.branch_summary.values(), au);
                        if summary == discovered_aus {
                        } else {
                            assert(pre.branch_summary.values().contains(summary));
                            lemma_union_set_of_sets_subset(pre.branch_summary.values(), summary);
                        }
                    }
                };
                assert forall |au: AU| #[trigger] post.accessible_aus().contains(au)
                    implies (pre.accessible_aus() + discovered_aus).contains(au) by {
                    if summary_aus(post.branch_summary).contains(au) {
                    } else if post.mini_allocator.all_aus().contains(au) {
                    } else {
                        assert(to_aus(post.disk.visible().dom()).contains(au));
                    }
                }
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_alloc_accessible_aus(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    )
        requires
            pre.inv(),
            CachingDiskBranch::State::next(
                pre,
                post,
                CachingDiskBranch::Label::InternalAlloc{allocs, deallocs},
            ),
        ensures
            deallocs == Set::<AU>::empty(),
            post.accessible_aus() <= pre.accessible_aus() + allocs,
    {
        let lbl = CachingDiskBranch::Label::InternalAlloc{allocs, deallocs};
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                assert(CachingDiskBranch::State::internal_fill_au(pre, post, lbl, aus, new_disk)) by {
                    reveal(CachingDiskBranch::State::internal_fill_au);
                }
                mini_allocator_add_aus_preserves_all_aus(pre.mini_allocator, allocs);
                assert(post.branch_summary == pre.branch_summary);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus() + allocs);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn internal_alloc_full_accessible_aus(
        pre: Self,
        post: Self,
        allocs: Set<AU>,
        deallocs: Set<AU>,
    )
        requires
            pre.inv(),
            CachingDiskBranch::State::next(
                pre,
                post,
                CachingDiskBranch::Label::InternalAlloc{allocs, deallocs},
            ),
        ensures
            deallocs == Set::<AU>::empty(),
            post.full_accessible_aus() <= pre.full_accessible_aus() + allocs,
    {
        let lbl = CachingDiskBranch::Label::InternalAlloc{allocs, deallocs};
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                assert(CachingDiskBranch::State::internal_fill_au(pre, post, lbl, aus, new_disk)) by {
                    reveal(CachingDiskBranch::State::internal_fill_au);
                }
                disk_growth_preserves_loaded_metadata(pre, post.disk, aus);
                mini_allocator_add_aus_preserves_all_aus(pre.mini_allocator, allocs);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.interpreted_branch_summary() == pre.branch_summary);
                assert(pre.branch_metadata_loaded());
                assert(post.interpreted_branch_summary() == pre.interpreted_branch_summary());
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus() + allocs);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub open spec fn disk_from_persistent(persistent: Map<Address, RawPage>) -> CachingDisk::State {
        CachingDisk::State{
            cache: Map::empty(),
            persistent,
            status: Map::empty(),
        }
    }

    pub open spec fn can_load_from_persistent(
        image: CachingDiskBranchImage,
    ) -> bool {
        let disk = Self::disk_from_persistent(image.persistent);
        &&& image.loadable()
        &&& image.stack_wf()
        &&& disk.inv()
    }

    pub open spec fn load_from_persistent(
        image: CachingDiskBranchImage,
    ) -> Self
        recommends
            Self::can_load_from_persistent(image),
    {
	        Self{
	            sealed_roots: image.sealed_roots,
	            branch_summary: Map::<AU, Summary>::empty(),
	            metadata_loaded: image.sealed_roots.len() == 0,
	            persisted_root_count: image.sealed_roots.len() as nat,
	            active_branch: CachedBranch::State::empty_active(),
	            mini_allocator: MiniAllocator::empty(),
	            disk: Self::disk_from_persistent(image.persistent),
            seq_end: image.seq_end,
        }
    }

    pub proof fn load_from_persistent_accessible_aus(
        image: CachingDiskBranchImage,
    )
        requires
            Self::can_load_from_persistent(image),
        ensures
            Self::load_from_persistent(image).accessible_aus()
                <= to_aus(image.persistent.dom()) + summary_aus(image.branch_summary()),
            Self::load_from_persistent(image).full_accessible_aus()
                <= to_aus(image.persistent.dom()) + summary_aus(image.branch_summary()),
    {
        let loaded = Self::load_from_persistent(image);
        assert(loaded.mini_allocator.all_aus() =~= Set::<AU>::empty());
        assert(loaded.disk.visible().dom() == image.persistent.dom());
        assert(loaded.branch_summary == Map::<AU, Summary>::empty());
        lemma_values_finite(loaded.branch_summary);
        assert(summary_aus(loaded.branch_summary) =~= Set::<AU>::empty()) by {
            assert_maps_equal!(loaded.branch_summary, Map::<AU, Summary>::empty());
            assert forall |au: AU| #[trigger] summary_aus(loaded.branch_summary).contains(au)
                implies false by {
                let summary = lemma_union_set_of_sets_contains(loaded.branch_summary.values(), au);
                assert(loaded.branch_summary.values().contains(summary));
                assert(false);
            }
        };
        assert forall |au: AU| #[trigger] loaded.accessible_aus().contains(au)
            implies (to_aus(image.persistent.dom()) + summary_aus(image.branch_summary())).contains(au)
        by {
            if summary_aus(loaded.branch_summary).contains(au) {
                assert(false);
            } else if loaded.mini_allocator.all_aus().contains(au) {
                assert(false);
            } else {
                assert(to_aus(loaded.disk.visible().dom()).contains(au));
                let addr = choose |addr: Address|
                    loaded.disk.visible().dom().contains(addr) && addr.au == au;
                assert(image.persistent.dom().contains(addr));
                crate::disk::GenericDisk_v::to_aus_domain(image.persistent.dom());
                assert(to_aus(image.persistent.dom()).contains(au));
            }
        }
        assert(loaded.accessible_aus()
            <= to_aus(image.persistent.dom()) + summary_aus(image.branch_summary()));
        assert(loaded.interpreted_branch_summary() == image.branch_summary()) by {
            assert(loaded.sealed_roots == image.sealed_roots);
            assert(loaded.visible_branch_nodes() == image.persistent_branch_nodes()) by {
                assert_maps_equal!(loaded.visible_branch_nodes(), image.persistent_branch_nodes(), addr => {
                    if loaded.visible_branch_nodes().contains_key(addr) {
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(image.persistent.contains_key(addr));
                    }
                    if image.persistent_branch_nodes().contains_key(addr) {
                        assert(image.persistent.contains_key(addr));
                        assert(loaded.disk.visible().contains_key(addr));
                    }
                });
            }
        };
        assert(loaded.full_accessible_aus()
            <= to_aus(image.persistent.dom()) + summary_aus(image.branch_summary())) by {
            assert forall |au: AU| #[trigger] loaded.full_accessible_aus().contains(au)
                implies (to_aus(image.persistent.dom()) + summary_aus(image.branch_summary())).contains(au) by {
                if summary_aus(loaded.interpreted_branch_summary()).contains(au) {
                    assert(summary_aus(image.branch_summary()).contains(au));
                } else if loaded.mini_allocator.all_aus().contains(au) {
                    assert(false);
                } else {
                    assert(to_aus(loaded.disk.visible().dom()).contains(au));
                    let addr = choose |addr: Address|
                        loaded.disk.visible().dom().contains(addr) && addr.au == au;
                    assert(image.persistent.dom().contains(addr));
                    crate::disk::GenericDisk_v::to_aus_domain(image.persistent.dom());
                    assert(to_aus(image.persistent.dom()).contains(au));
                }
            }
        };
    }

    pub open spec fn freeze_image(self) -> CachingDiskBranchImage {
        CachingDiskBranchImage{
            persistent: self.disk.persistent,
            sealed_roots: self.sealed_roots,
            seq_end: self.seq_end,
        }
    }

    pub open spec fn freeze_metadata(self) -> CachingDiskBranchMetadata {
        CachingDiskBranchMetadata{
            sealed_roots: self.sealed_roots,
            seq_end: self.seq_end,
        }
    }

    pub open spec fn visible_image_for_metadata(
        self,
        frozen: CachingDiskBranchMetadata,
    ) -> CachingDiskBranchImage {
        CachingDiskBranchImage{
            persistent: self.disk.visible(),
            sealed_roots: frozen.sealed_roots,
            seq_end: frozen.seq_end,
        }
    }

    pub proof fn visible_prefix_image_matches_stack(
        self,
        frozen: CachingDiskBranchMetadata,
    )
        requires
            self.inv(),
            frozen.sealed_roots.len() <= self.sealed_roots.len(),
            self.sealed_roots.subrange(0, frozen.sealed_roots.len() as int)
                == frozen.sealed_roots,
        ensures
            self.visible_image_for_metadata(frozen).stack_wf(),
            self.visible_image_for_metadata(frozen).sealed_stack_i().wf(
                self.visible_image_for_metadata(frozen).branch_summary()
            ),
            self.visible_image_for_metadata(frozen).branch_summary()
                == self.interpreted_branch_summary().remove_keys(
                    to_aus(self.sealed_roots.to_set() - frozen.sealed_roots.to_set()),
                ),
            summary_aus(self.visible_image_for_metadata(frozen).branch_summary())
                <= summary_aus(self.interpreted_branch_summary()),
            self.visible_image_for_metadata(frozen).sealed_stack_i().sealed_disk.entries
                == self.sealed_stack_i().sealed_disk.entries.restrict(
                    restrict_domain_au(
                        self.sealed_stack_i().sealed_disk.entries,
                        summary_aus(self.visible_image_for_metadata(frozen).branch_summary()),
                    ),
                ),
            frozen.sealed_roots == self.sealed_roots ==>
                self.visible_image_for_metadata(frozen).sealed_stack_i() == self.sealed_stack_i(),
    {
        let image = self.visible_image_for_metadata(frozen);
        let full_stack = self.sealed_stack_i();
        let full_summary = self.interpreted_branch_summary();
        let full_roots = self.sealed_roots.to_set();
        let frozen_roots = frozen.sealed_roots.to_set();

        assert(frozen_roots <= full_roots) by {
            assert forall |root: Address| #[trigger] frozen_roots.contains(root)
                implies full_roots.contains(root) by {
                let idx = choose |i: int| 0 <= i < frozen.sealed_roots.len()
                    && frozen.sealed_roots[i] == root;
                assert(self.sealed_roots[idx] == root);
            }
        };
        assert(crate::disk::GenericDisk_v::set_addrs_disjoint_aus(frozen_roots));
        branch_summary_from_reads_up_to_self_ensures(
            self.sealed_roots,
            self.visible_branch_nodes(),
            self.sealed_roots.len() as nat,
        );
        assert(full_stack.wf(full_summary));
        to_aus_finite(full_roots);
        assert(full_summary.dom() == to_aus(full_roots));
        assert(full_summary.dom().finite());
        lemma_values_finite(full_summary);
        assert(full_summary.values().finite());
        assert(map_with_disjoint_values(full_summary));
        assert(addrs_closed(full_stack.sealed_disk.entries.dom(), summary_aus(full_summary)));

        let image_nodes = image.persistent_branch_nodes();
        assert(image_nodes == self.visible_branch_nodes());
        assert(branch_summary_reads_valid(frozen.sealed_roots, image_nodes)) by {
            assert forall |i: int| #![trigger frozen.sealed_roots[i]]
                0 <= i < frozen.sealed_roots.len()
                implies root_summary_read_valid(frozen.sealed_roots[i], image_nodes)
            by {
                let root = frozen.sealed_roots[i];
                assert(self.sealed_roots[i] == root);
                assert(branch_summary_reads_valid(self.sealed_roots, self.visible_branch_nodes()));
            }
        };
        assert forall |i: int| 0 <= i < frozen.sealed_roots.len() implies {
            &&& full_summary.contains_key(frozen.sealed_roots[i].au)
            &&& root_summary_from_read(frozen.sealed_roots[i], image_nodes)
                == full_summary[frozen.sealed_roots[i].au]
        } by {
            let root = frozen.sealed_roots[i];
            assert(self.sealed_roots[i] == root);
            root_aus_up_to_contains(
                self.sealed_roots,
                self.sealed_roots.len() as nat,
                i,
            );
            assert(full_summary.dom().contains(root.au));
            assert(full_summary[root.au] == root_summary_from_read(root, self.visible_branch_nodes()));
        };
        branch_summary_from_reads_up_to_ensures(
            frozen.sealed_roots,
            image_nodes,
            full_summary,
            frozen.sealed_roots.len() as nat,
        );

        let prefix_summary = full_summary.remove_keys(to_aus(full_roots - frozen_roots));
        assert(image.branch_summary() == prefix_summary) by {
            assert_maps_equal!(image.branch_summary(), prefix_summary, au => {
                if image.branch_summary().contains_key(au) {
                    assert(image.branch_summary().dom().contains(au));
                    let idx = root_aus_up_to_member_has_index(
                        frozen.sealed_roots,
                        frozen.sealed_roots.len() as nat,
                        au,
                    );
                    assert(image.branch_summary()[au] == full_summary[au]);
                    assert(full_summary.contains_key(au));
                    let root = frozen.sealed_roots[idx];
                    assert(frozen_roots.contains(root));
                    assert(full_roots.contains(root));
                    assert(!(full_roots - frozen_roots).contains(root));
                    crate::disk::GenericDisk_v::to_aus_domain(full_roots - frozen_roots);
                    assert(!to_aus(full_roots - frozen_roots).contains(au)) by {
                        if to_aus(full_roots - frozen_roots).contains(au) {
                            let removed_to_au = Map::new(
                                |addr| (full_roots - frozen_roots).contains(addr),
                                |addr: Address| addr.au,
                            );
                            let removed_root = choose |removed_root| #[trigger] removed_to_au.contains_key(removed_root)
                                && removed_to_au[removed_root] == au;
                            assert((full_roots - frozen_roots).contains(removed_root));
                            assert(full_roots.contains(removed_root));
                            if removed_root != root {
                                assert(addrs_with_different_au(removed_root, root));
                                assert(removed_root.au != root.au);
                            }
                            assert(removed_root == root);
                            assert(!frozen_roots.contains(root));
                            assert(false);
                        }
                    }
                    assert(prefix_summary.contains_key(au));
                }
                if prefix_summary.contains_key(au) {
                    assert(full_summary.contains_key(au));
                    assert(!to_aus(full_roots - frozen_roots).contains(au));
                    assert(to_aus(full_roots).contains(au)) by {
                        assert(full_summary.dom() == to_aus(full_roots));
                    };
                    crate::disk::GenericDisk_v::to_aus_domain(full_roots);
                    let root = choose |root: Address| full_roots.contains(root) && root.au == au;
                    assert(full_roots.contains(root));
                    assert(root.au == au);
                    assert(!(full_roots - frozen_roots).contains(root)) by {
                        if (full_roots - frozen_roots).contains(root) {
                            crate::disk::GenericDisk_v::to_aus_domain(full_roots - frozen_roots);
                            assert(to_aus(full_roots - frozen_roots).contains(au));
                            assert(false);
                        }
                    };
                    assert(frozen_roots.contains(root));
                    let idx = choose |i: int| 0 <= i < frozen.sealed_roots.len()
                        && frozen.sealed_roots[i] == root;
                    root_aus_up_to_contains(
                        frozen.sealed_roots,
                        frozen.sealed_roots.len() as nat,
                        idx,
                    );
                    assert(image.branch_summary().contains_key(au));
                    assert(image.branch_summary()[au] == full_summary[au]);
                }
            });
        };
        assert(summary_aus(image.branch_summary()) <= summary_aus(full_summary)) by {
            assert(full_summary.dom().finite());
            assert(full_summary.values().finite());
            root_aus_up_to_full(frozen.sealed_roots);
            to_aus_finite(frozen_roots);
            assert(image.branch_summary().dom().finite()) by {
                assert(image.branch_summary().dom()
                    =~= root_aus_up_to(frozen.sealed_roots, frozen.sealed_roots.len() as nat));
                assert(root_aus_up_to(
                    frozen.sealed_roots,
                    frozen.sealed_roots.len() as nat,
                ) =~= to_aus(frozen_roots));
            }
            lemma_values_finite(image.branch_summary());
            assert forall |au: AU| #[trigger] summary_aus(image.branch_summary()).contains(au)
                implies summary_aus(full_summary).contains(au)
            by {
                let summary = lemma_union_set_of_sets_contains(
                    image.branch_summary().values(),
                    au,
                );
                assert(image.branch_summary().values().contains(summary));
                let root_au = choose |root_au: AU|
                    image.branch_summary().contains_key(root_au)
                        && image.branch_summary()[root_au] == summary;
                assert(prefix_summary.contains_key(root_au));
                assert(full_summary.contains_key(root_au));
                assert(prefix_summary[root_au] == full_summary[root_au]);
                assert(full_summary[root_au] == summary);
                assert(full_summary.values().contains(summary));
                lemma_union_set_of_sets_subset(full_summary.values(), summary);
            }
        };

        assert(image.live_persistent_aus() == summary_aus(prefix_summary));
        let image_entries = image.sealed_stack_i().sealed_disk.entries;
        let prefix_domain = restrict_domain_au(
            full_stack.sealed_disk.entries,
            summary_aus(prefix_summary),
        );
        let prefix_entries = full_stack.sealed_disk.entries.restrict(
            prefix_domain,
        );
        assert(image.sealed_stack_i().sealed_roots == frozen.sealed_roots);
        let prefix_disk = BufferDisk{entries: prefix_entries};
        assert(image_entries == prefix_entries) by {
            assert_maps_equal!(image_entries, prefix_entries, addr => {
                if image_entries.contains_key(addr) {
                    assert(image.live_persistent().contains_key(addr));
                    assert(addresses_in_aus(summary_aus(prefix_summary)).contains(addr));
                    assert(prefix_domain.contains(addr));
                    assert(self.disk.visible().contains_key(addr));
                    assert(full_stack.sealed_disk.entries.contains_key(addr));
                    assert(prefix_entries.contains_key(addr));
                }
                if prefix_entries.contains_key(addr) {
                    assert(full_stack.sealed_disk.entries.contains_key(addr));
                    assert(prefix_domain.contains(addr));
                    assert(addresses_in_aus(summary_aus(prefix_summary)).contains(addr));
                    assert(self.disk.visible().contains_key(addr));
                    assert(image.live_persistent().contains_key(addr));
                }
            });
        };
        assert(image.sealed_stack_i().sealed_disk == prefix_disk);
        assert(map_with_disjoint_values(prefix_summary));
        assert(addrs_closed(prefix_disk.entries.dom(), summary_aus(prefix_summary)));
        assert(map_with_disjoint_values(image.branch_summary()));
        assert(addrs_closed(image.sealed_stack_i().sealed_disk.entries.dom(), summary_aus(image.branch_summary())));
        assert(image.sealed_stack_i().wf(image.branch_summary())) by {
            root_aus_up_to_full(frozen.sealed_roots);
            assert(image.branch_summary().dom()
                =~= root_aus_up_to(frozen.sealed_roots, frozen.sealed_roots.len() as nat));
            assert(image.branch_summary().dom() == to_aus(frozen_roots));
            assert forall |root: Address| #[trigger] image.sealed_stack_i().sealed_roots.to_set().contains(root)
                implies {
                    &&& image.branch_summary().contains_key(root.au)
                    &&& image.branch_summary()[root.au].contains(root.au)
                    &&& image.sealed_stack_i().root_has_tight_branch(root, image.branch_summary()[root.au])
                }
            by {
                assert(frozen_roots.contains(root));
                assert(full_roots.contains(root));
                let idx = choose |i: int| 0 <= i < frozen.sealed_roots.len()
                    && frozen.sealed_roots[i] == root;
                assert(self.sealed_roots[idx] == root);
                root_aus_up_to_contains(
                    frozen.sealed_roots,
                    frozen.sealed_roots.len() as nat,
                    idx,
                );
                assert(image.branch_summary().contains_key(root.au));
                assert(image.branch_summary()[root.au] == full_summary[root.au]);
                full_stack.tight_branch_facts(full_summary, root);
                let branch = full_stack.tight_branch(root, full_summary[root.au]);
                assert(tight_branch_in_loose_disk(
                    full_stack.sealed_disk,
                    root,
                    full_summary[root.au],
                    branch,
                ));
                assert(branch.disk_view.entries <= full_stack.sealed_disk.entries);
                assert(branch.get_summary() == full_summary[root.au]);
                assert(tight_branch_in_loose_disk(
                    image.sealed_stack_i().sealed_disk,
                    root,
                    image.branch_summary()[root.au],
                    branch,
                )) by {
                    assert(branch.disk_view.entries <= image.sealed_stack_i().sealed_disk.entries) by {
                        assert forall |addr: Address| #[trigger] branch.disk_view.entries.contains_key(addr)
                            implies image.sealed_stack_i().sealed_disk.entries.contains_key(addr)
                        by {
                            assert(full_stack.sealed_disk.entries.contains_key(addr));
                            assert(branch.valid_sealed_branch());
                            assert(branch.tight_disk_view_with_summary());
                            assert(branch.disk_view.representation() == branch.full_repr());
                            assert(branch.disk_view.entries.dom() =~= branch.full_repr());
                            assert(branch.full_repr().contains(addr));
                            assert(addrs_closed(branch.full_repr(), branch.get_summary()));
                            assert(branch.get_summary().contains(addr.au));
                            assert(summary_aus(image.branch_summary()).contains(addr.au)) by {
                                root_aus_up_to_full(frozen.sealed_roots);
                                to_aus_finite(frozen_roots);
                                assert(image.branch_summary().dom()
                                    =~= root_aus_up_to(frozen.sealed_roots, frozen.sealed_roots.len() as nat));
                                assert(image.branch_summary().dom() == to_aus(frozen_roots));
                                assert(image.branch_summary().dom().finite());
                                lemma_values_finite(image.branch_summary());
                                assert(image.branch_summary().values().contains(image.branch_summary()[root.au]));
                                lemma_union_set_of_sets_subset(
                                    image.branch_summary().values(),
                                    image.branch_summary()[root.au],
                                );
                            };
                            assert(addresses_in_aus(summary_aus(image.branch_summary())).contains(addr));
                            assert(prefix_domain.contains(addr));
                            assert(prefix_entries.contains_key(addr));
                            assert(image.sealed_stack_i().sealed_disk.entries.contains_key(addr));
                        }
                    };
                };
                assert(image.sealed_stack_i().root_has_tight_branch(root, image.branch_summary()[root.au]));
            }
        };
        assert(image.stack_wf());
        if frozen.sealed_roots == self.sealed_roots {
            assert(frozen_roots =~= full_roots);
            assert(full_roots - frozen_roots =~= Set::<Address>::empty()) by {
                assert forall |root: Address| #[trigger] (full_roots - frozen_roots).contains(root)
                    implies false by {
                    assert(full_roots.contains(root));
                    assert(frozen_roots.contains(root));
                }
            };
            assert(to_aus(full_roots - frozen_roots) =~= Set::<AU>::empty()) by {
                assert forall |au: AU| #[trigger] to_aus(full_roots - frozen_roots).contains(au)
                    implies false by {
                    crate::disk::GenericDisk_v::to_aus_domain(full_roots - frozen_roots);
                    let root = choose |root: Address|
                        (full_roots - frozen_roots).contains(root) && root.au == au;
                    assert(false);
                }
            };
            assert(prefix_summary == full_summary);
            assert(prefix_domain == full_stack.sealed_disk.entries.dom()) by {
                assert_sets_equal!(
                    prefix_domain,
                    full_stack.sealed_disk.entries.dom(),
                    addr => {
                        if prefix_domain.contains(addr) {
                            assert(full_stack.sealed_disk.entries.contains_key(addr));
                        }
                        if full_stack.sealed_disk.entries.dom().contains(addr) {
                            assert(full_stack.sealed_disk.entries.contains_key(addr));
                            assert(addrs_closed(full_stack.sealed_disk.entries.dom(), summary_aus(full_summary)));
                            assert(summary_aus(prefix_summary).contains(addr.au));
                            assert(addresses_in_aus(summary_aus(prefix_summary)).contains(addr));
                            assert(prefix_domain.contains(addr));
                        }
                    }
                );
            };
            assert(prefix_entries == full_stack.sealed_disk.entries) by {
                assert_maps_equal!(prefix_entries, full_stack.sealed_disk.entries, addr => {
                    if prefix_entries.contains_key(addr) {
                        assert(full_stack.sealed_disk.entries.contains_key(addr));
                    }
                    if full_stack.sealed_disk.entries.contains_key(addr) {
                        assert(prefix_domain.contains(addr));
                        assert(prefix_entries.contains_key(addr));
                    }
                });
            };
            assert(image.sealed_stack_i().sealed_disk == full_stack.sealed_disk);
            assert(image.sealed_stack_i() == full_stack);
        }
    }

    pub proof fn prepared_image_matches_visible_prefix(
        self,
        image: CachingDiskBranchImage,
    )
        requires
            self.inv(),
            image.persistent == self.disk.persistent,
            CachingDiskBranch::State::next(
                self,
                self,
                CachingDiskBranch::Label::FreezePrepared{
                    image: CachingDiskBranchMetadata{
                        sealed_roots: image.sealed_roots,
                        seq_end: image.seq_end,
                    },
                },
            ),
        ensures
            image.loadable(),
            image.stack_wf(),
            image.sealed_stack_i().wf(image.branch_summary()),
            image.branch_summary() == image.branch_summary(),
            image.branch_summary()
                == self.visible_image_for_metadata(CachingDiskBranchMetadata{
                    sealed_roots: image.sealed_roots,
                    seq_end: image.seq_end,
                }).branch_summary(),
            summary_aus(image.branch_summary()) <= summary_aus(self.interpreted_branch_summary()),
            image.sealed_stack_i()
                == self.visible_image_for_metadata(CachingDiskBranchMetadata{
                    sealed_roots: image.sealed_roots,
                    seq_end: image.seq_end,
                }).sealed_stack_i(),
    {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let frozen = CachingDiskBranchMetadata{
            sealed_roots: image.sealed_roots,
            seq_end: image.seq_end,
        };
        let lbl = CachingDiskBranch::Label::FreezePrepared{image: frozen};
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(self, self, lbl, step);
        match step {
            CachingDiskBranch::Step::freeze_prepared() => {
                reveal(CachingDiskBranch::State::freeze_prepared);
            },
            _ => { assert(false); },
        }

        let visible_image = self.visible_image_for_metadata(frozen);
        self.visible_prefix_image_matches_stack(frozen);
        branch_summary_from_reads_up_to_self_ensures(
            image.sealed_roots,
            visible_image.persistent_branch_nodes(),
            image.sealed_roots.len() as nat,
        );

        let full_summary = self.interpreted_branch_summary();
        let prefix_summary = visible_image.branch_summary();
        let prefix_aus = summary_aus(prefix_summary);
        let persisted_aus = sealed_summary_aus_up_to(
            self.sealed_roots,
            self.interpreted_branch_summary(),
            self.persisted_root_count,
        );

        assert(self.interpreted_branch_summary() == full_summary);
        assert(visible_image.branch_summary() == prefix_summary);
        visible_image.branch_summary_finite();
        assert(prefix_summary.values().finite());
        assert(prefix_aus <= persisted_aus) by {
            to_aus_finite(self.sealed_roots.to_set());
            assert(full_summary.dom() == to_aus(self.sealed_roots.to_set()));
            assert(full_summary.dom().finite());
            lemma_values_finite(full_summary);
            assert(full_summary.values().finite());
            assert(prefix_summary == full_summary.remove_keys(
                to_aus(self.sealed_roots.to_set() - image.sealed_roots.to_set()),
            ));
            assert forall |au: AU| #[trigger] prefix_aus.contains(au)
                implies persisted_aus.contains(au)
            by {
                let summary = lemma_union_set_of_sets_contains(prefix_summary.values(), au);
                let root_au = choose |root_au: AU|
                    prefix_summary.contains_key(root_au)
                    && prefix_summary[root_au] == summary;
                assert(prefix_summary.contains_key(root_au));
                assert(prefix_summary.dom().contains(root_au));
                assert(root_aus_up_to(
                    image.sealed_roots,
                    image.sealed_roots.len() as nat,
                ).contains(root_au));
                let idx = root_aus_up_to_member_has_index(
                    image.sealed_roots,
                    image.sealed_roots.len() as nat,
                    root_au,
                );
                assert(0 <= idx < image.sealed_roots.len());
                assert(self.sealed_roots[idx] == image.sealed_roots[idx]);
                assert(full_summary.contains_key(root_au));
                assert(full_summary[root_au] == summary);
                assert(summary.contains(au));
                sealed_summary_aus_up_to_contains_root_summary(
                    self.sealed_roots,
                    full_summary,
                    self.persisted_root_count,
                    idx,
                    au,
                );
            }
        };
        to_aus_finite(self.sealed_roots.to_set());
        assert(full_summary.dom() == to_aus(self.sealed_roots.to_set()));
        assert(full_summary.dom().finite());
        lemma_values_finite(full_summary);
        assert(full_summary.values().finite());
        sealed_summary_aus_up_to_subset_summary_aus(
            self.sealed_roots,
            full_summary,
            self.persisted_root_count,
        );
        assert(persisted_aus <= summary_aus(full_summary));
        assert(prefix_aus <= summary_aus(full_summary));
        assert(self.disk.aus_clean_or_evictable(prefix_aus)) by {
            assert forall |addr: Address| #[trigger] self.disk.cache.contains_key(addr)
                && prefix_aus.contains(addr.au)
                implies {
                    &&& self.disk.status.contains_key(addr)
                    &&& self.disk.status[addr] == PageStatus::Clean
                }
            by {
                assert(persisted_aus.contains(addr.au));
                assert(self.disk.aus_clean_or_evictable(persisted_aus));
            }
        };
        clean_aus_persistent_visible_eq(self.disk, prefix_aus);
        assert(image.persistent == self.disk.persistent);
        assert(visible_image.persistent == self.disk.visible());
        assert(self.disk.persistent.restrict(addresses_in_aus(prefix_aus))
            == self.disk.visible().restrict(addresses_in_aus(prefix_aus)));
        assert(branch_summary_reads_valid(image.sealed_roots, image.persistent_branch_nodes())) by {
            assert forall |i: int| #![trigger image.sealed_roots[i]]
                0 <= i < image.sealed_roots.len()
                implies root_summary_read_valid(image.sealed_roots[i], image.persistent_branch_nodes())
            by {
                let root = image.sealed_roots[i];
                assert(root_summary_read_valid(root, visible_image.persistent_branch_nodes()));
                assert(prefix_aus.contains(root.au)) by {
                    visible_image.sealed_stack_i().root_au_in_summary(prefix_summary, root);
                }
                assert(self.disk.persistent.restrict(addresses_in_aus(prefix_aus))[root]
                    == self.disk.visible().restrict(addresses_in_aus(prefix_aus))[root]);
                assert(image.persistent_branch_nodes().contains_key(root));
                assert(image.persistent_branch_nodes()[root]
                    == visible_image.persistent_branch_nodes()[root]);
                if visible_image.persistent_branch_nodes()[root] is Index {
                    let aux = visible_image.persistent_branch_nodes()[root]->aux_ptr.unwrap();
                    assert(prefix_aus.contains(aux.au)) by {
                        visible_image.index_root_aux_in_summary(root, aux);
                        assert(prefix_summary[root.au].contains(aux.au));
                        assert(prefix_summary.values().contains(prefix_summary[root.au]));
                        lemma_union_set_of_sets_subset(prefix_summary.values(), prefix_summary[root.au]);
                    }
                    assert(self.disk.persistent.restrict(addresses_in_aus(prefix_aus))[aux]
                        == self.disk.visible().restrict(addresses_in_aus(prefix_aus))[aux]);
                    assert(image.persistent_branch_nodes().contains_key(aux));
                    assert(image.persistent_branch_nodes()[aux]
                        == visible_image.persistent_branch_nodes()[aux]);
                    assert(image.persistent_branch_nodes()[aux] is Auxiliary);
                } else {
                    assert(image.persistent_branch_nodes()[root] is Leaf);
                }
            }
        };
        branch_summary_from_reads_up_to_self_ensures(
            image.sealed_roots,
            image.persistent_branch_nodes(),
            image.sealed_roots.len() as nat,
        );

        assert(image.branch_summary() == prefix_summary) by {
            assert_maps_equal!(image.branch_summary(), prefix_summary, au => {
                if image.branch_summary().contains_key(au) {
                    assert(image.branch_summary().dom().contains(au));
                    assert(root_aus_up_to(
                        image.sealed_roots,
                        image.sealed_roots.len() as nat,
                    ).contains(au));
                    let idx = root_aus_up_to_member_has_index(
                        image.sealed_roots,
                        image.sealed_roots.len() as nat,
                        au,
                    );
                    let root = image.sealed_roots[idx];
                    assert(self.sealed_roots[idx] == root);
                    assert(prefix_summary.contains_key(au));
                    assert(prefix_summary[au]
                        == root_summary_from_read(root, visible_image.persistent_branch_nodes()));
                    assert(root_summary_read_valid(root, visible_image.persistent_branch_nodes()));
                    assert(root_summary_read_valid(root, image.persistent_branch_nodes()));
                    assert(prefix_aus.contains(root.au)) by {
                        visible_image.sealed_stack_i().root_au_in_summary(prefix_summary, root);
                    }
                    assert(self.disk.persistent.restrict(addresses_in_aus(prefix_aus))[root]
                        == self.disk.visible().restrict(addresses_in_aus(prefix_aus))[root]);
                    assert(image.persistent_branch_nodes()[root]
                        == visible_image.persistent_branch_nodes()[root]);
                    if visible_image.persistent_branch_nodes()[root] is Index {
                        let aux = visible_image.persistent_branch_nodes()[root]->aux_ptr.unwrap();
                        assert(image.persistent_branch_nodes()[root] is Index);
                        assert(image.persistent_branch_nodes()[root]->aux_ptr == Some(aux));
                        assert(prefix_aus.contains(aux.au)) by {
                            visible_image.index_root_aux_in_summary(root, aux);
                            assert(prefix_summary[root.au].contains(aux.au));
                            assert(prefix_summary.values().contains(prefix_summary[root.au]));
                            lemma_union_set_of_sets_subset(prefix_summary.values(), prefix_summary[root.au]);
                        }
                        assert(self.disk.persistent.restrict(addresses_in_aus(prefix_aus))[aux]
                            == self.disk.visible().restrict(addresses_in_aus(prefix_aus))[aux]);
                        assert(image.persistent_branch_nodes()[aux]
                            == visible_image.persistent_branch_nodes()[aux]);
                    }
                    assert(image.branch_summary()[au] == prefix_summary[au]);
                }
                if prefix_summary.contains_key(au) {
                    assert(prefix_summary.dom().contains(au));
                    assert(root_aus_up_to(
                        image.sealed_roots,
                        image.sealed_roots.len() as nat,
                    ).contains(au));
                    let idx = root_aus_up_to_member_has_index(
                        image.sealed_roots,
                        image.sealed_roots.len() as nat,
                        au,
                    );
                    let root = image.sealed_roots[idx];
                    assert(image.branch_summary().contains_key(au));
                }
            });
        };

        assert(image.live_persistent() == visible_image.live_persistent()) by {
            assert_maps_equal!(image.live_persistent(), visible_image.live_persistent(), addr => {
                if image.live_persistent().contains_key(addr) {
                    assert(addresses_in_aus(prefix_aus).contains(addr));
                    assert(self.disk.persistent.restrict(addresses_in_aus(prefix_aus)).contains_key(addr));
                    assert(self.disk.visible().restrict(addresses_in_aus(prefix_aus)).contains_key(addr));
                    assert(visible_image.live_persistent().contains_key(addr));
                }
                if visible_image.live_persistent().contains_key(addr) {
                    assert(addresses_in_aus(prefix_aus).contains(addr));
                    assert(self.disk.visible().restrict(addresses_in_aus(prefix_aus)).contains_key(addr));
                    assert(self.disk.persistent.restrict(addresses_in_aus(prefix_aus)).contains_key(addr));
                    assert(image.live_persistent().contains_key(addr));
                }
            });
        };
        assert(image.sealed_stack_i().sealed_disk.entries
            == visible_image.sealed_stack_i().sealed_disk.entries) by {
            assert_maps_equal!(
                image.sealed_stack_i().sealed_disk.entries,
                visible_image.sealed_stack_i().sealed_disk.entries,
                addr => {
                    if image.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                        assert(image.live_persistent().contains_key(addr));
                    }
                    if visible_image.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                        assert(visible_image.live_persistent().contains_key(addr));
                    }
                }
            );
        };
        assert(image.sealed_stack_i() == visible_image.sealed_stack_i());
        assert(image.sealed_stack_i().wf(image.branch_summary()));
        assert(image.branch_summary() == image.branch_summary());
    }

	    pub proof fn freeze_image_matches_stack(self)
	        requires
	            self.inv(),
	            self.metadata_loaded,
	            self.active_branch.root is None,
	            self.persisted_root_count == self.sealed_roots.len(),
        ensures
            self.freeze_image().stack_wf(),
            self.freeze_image().sealed_stack_i() == self.sealed_stack_i(),
            self.freeze_image().sealed_stack_i().wf(self.freeze_image().branch_summary()),
            self.freeze_image().branch_summary() == self.interpreted_branch_summary(),
	    {
	        assert(self.branch_metadata_loaded());
	        let image = self.freeze_image();
        let roots = self.sealed_roots.to_set();
        let branch_summary = self.interpreted_branch_summary();
        let aus = summary_aus(branch_summary);

        self.sealed_stack_i().sealed_disk.build_branch_domain(roots);
        assert(branch_summary.dom() =~= to_aus(roots));
        assert(branch_summary.values().finite()) by {
            self.sealed_stack_i().sealed_disk.build_branch_summary_finite(roots);
        };
        assert(aus <= sealed_summary_aus_up_to(self.sealed_roots, branch_summary, self.sealed_roots.len() as nat)) by {
            assert forall |au: AU| #[trigger] aus.contains(au)
                implies sealed_summary_aus_up_to(self.sealed_roots, branch_summary, self.sealed_roots.len() as nat).contains(au)
            by {
                let summary = lemma_union_set_of_sets_contains(branch_summary.values(), au);
                let root_au = choose |root_au: AU|
                    branch_summary.contains_key(root_au)
                    && branch_summary[root_au] == summary;
                assert(branch_summary.contains_key(root_au));
                assert(branch_summary.dom() == to_aus(roots));
                root_aus_up_to_full(self.sealed_roots);
                assert(root_aus_up_to(self.sealed_roots, self.sealed_roots.len() as nat).contains(root_au));
                let idx = root_aus_up_to_member_has_index(
                    self.sealed_roots,
                    self.sealed_roots.len() as nat,
                    root_au,
                );
                let root = self.sealed_roots[idx];
                assert(root.au == root_au);
                assert(branch_summary[root_au].contains(au));
                sealed_summary_aus_up_to_contains_root_summary(
                    self.sealed_roots,
                    branch_summary,
                    self.sealed_roots.len() as nat,
                    idx,
                    au,
                );
            }
        };
        assert(sealed_summary_aus_up_to(self.sealed_roots, branch_summary, self.sealed_roots.len() as nat) <= aus) by {
            sealed_summary_aus_up_to_subset_summary_aus(
                self.sealed_roots,
                branch_summary,
                self.sealed_roots.len() as nat,
            );
        };
        assert(aus == sealed_summary_aus_up_to(self.sealed_roots, branch_summary, self.sealed_roots.len() as nat));
        assert(self.disk.aus_clean_or_evictable(aus));
        clean_aus_persistent_visible_eq(self.disk, aus);
        assert(image.live_persistent_aus() == aus
            && branch_summary_reads_valid(self.sealed_roots, image.persistent_branch_nodes())
            && image.branch_summary() == branch_summary) by {
            assert(image.persistent_branch_nodes() == to_branch_nodes(self.disk.persistent));
            assert(branch_summary_reads_valid(self.sealed_roots, image.persistent_branch_nodes())) by {
                assert forall |i: int| #![trigger self.sealed_roots[i]]
                    0 <= i < self.sealed_roots.len()
                    implies root_summary_read_valid(self.sealed_roots[i], image.persistent_branch_nodes())
                by {
                    let root = self.sealed_roots[i];
                    assert(self.sealed_roots.to_set().contains(root));
                    self.sealed_stack_i().root_au_in_summary(branch_summary, root);
                    assert(aus.contains(root.au));
                    assert(self.sealed_stack_i().sealed_disk.entries.contains_key(root));
                    assert(self.disk.visible().restrict(addresses_in_aus(aus)).contains_key(root));
                    assert(self.disk.persistent.restrict(addresses_in_aus(aus)).contains_key(root));
                    assert(image.persistent_branch_nodes().contains_key(root));
                    assert(to_branch_nodes(self.disk.visible())[root]
                        == image.persistent_branch_nodes()[root]);
                    if image.persistent_branch_nodes()[root] is Index {
                        let aux_ptr = image.persistent_branch_nodes()[root]->aux_ptr;
                        assert(aux_ptr is Some) by {
                            assert(to_branch_nodes(self.disk.visible())[root] is Index);
                            assert(root_summary_read_valid(root, self.visible_branch_nodes()));
                        }
                        let aux = aux_ptr.unwrap();
                        assert(to_branch_nodes(self.disk.visible())[root]
                            == image.persistent_branch_nodes()[root]);
                        assert(to_branch_nodes(self.disk.visible())[root]->aux_ptr == Some(aux));
                        assert(root_summary_read_valid(root, self.visible_branch_nodes()));
                        assert(self.visible_branch_nodes().contains_key(aux));
                        assert(self.visible_branch_nodes()[aux] is Auxiliary);
                        assert(aus.contains(aux.au)) by {
                            self.loaded_index_root_aux_in_summary(root, aux);
                            assert(branch_summary.values().contains(branch_summary[root.au]));
                            lemma_union_set_of_sets_subset(branch_summary.values(), branch_summary[root.au]);
                        }
                        assert(self.disk.visible().restrict(addresses_in_aus(aus)).contains_key(aux));
                        assert(self.disk.persistent.restrict(addresses_in_aus(aus)).contains_key(aux));
                        assert(image.persistent_branch_nodes().contains_key(aux));
                        assert(image.persistent_branch_nodes()[aux] is Auxiliary);
                    } else {
                        assert(to_branch_nodes(self.disk.visible())[root]
                            == image.persistent_branch_nodes()[root]);
                        assert(image.persistent_branch_nodes()[root] is Leaf);
                    }
                }
            };
            assert forall |i: int| 0 <= i < self.sealed_roots.len() implies {
                &&& branch_summary.contains_key(self.sealed_roots[i].au)
                &&& root_summary_from_read(self.sealed_roots[i], image.persistent_branch_nodes())
                    == branch_summary[self.sealed_roots[i].au]
            } by {
                let root = self.sealed_roots[i];
                assert(self.sealed_roots.to_set().contains(root));
                self.sealed_stack_i().root_au_in_summary(branch_summary, root);
                assert(to_branch_nodes(self.disk.visible())[root] == image.persistent_branch_nodes()[root]);
                assert(root_summary_read_valid(root, self.visible_branch_nodes()));
                assert(root_summary_from_read(root, self.visible_branch_nodes()) == branch_summary[root.au]);
                if image.persistent_branch_nodes()[root] is Index {
                    let aux = image.persistent_branch_nodes()[root]->aux_ptr.unwrap();
                    assert(image.persistent_branch_nodes()[root] is Index);
                    assert(image.persistent_branch_nodes()[root]->aux_ptr == Some(aux));
                    assert(to_branch_nodes(self.disk.visible())[root] is Index);
                    assert(to_branch_nodes(self.disk.visible())[root]->aux_ptr == Some(aux));
                    self.loaded_index_root_aux_in_summary(root, aux);
                    assert(aus.contains(aux.au)) by {
                        assert(branch_summary.values().contains(branch_summary[root.au]));
                        lemma_union_set_of_sets_subset(branch_summary.values(), branch_summary[root.au]);
                    }
                    assert(image.persistent_branch_nodes()[aux] == to_branch_nodes(self.disk.visible())[aux]);
                    assert(root_summary_from_read(root, image.persistent_branch_nodes())
                        == root_summary_from_read(root, self.visible_branch_nodes()));
                } else {
                    assert(to_branch_nodes(self.disk.visible())[root] is Leaf);
                    assert(root_summary_from_read(root, image.persistent_branch_nodes())
                        == set![root.au]);
                    assert(root_summary_from_read(root, self.visible_branch_nodes()) == set![root.au]);
                }
                assert(root_summary_from_read(root, image.persistent_branch_nodes())
                    == branch_summary[root.au]);
            }
            branch_summary_from_reads_up_to_ensures(
                self.sealed_roots,
                image.persistent_branch_nodes(),
                branch_summary,
                self.sealed_roots.len() as nat,
            );
            root_aus_up_to_full(self.sealed_roots);
            assert_maps_equal!(
                image.branch_summary(),
                branch_summary,
                au_key => {
                    if image.branch_summary().contains_key(au_key) {
                        assert(image.branch_summary().dom().contains(au_key));
                        assert(root_aus_up_to(self.sealed_roots, self.sealed_roots.len() as nat).contains(au_key));
                        assert(to_aus(self.sealed_roots.to_set()).contains(au_key));
                        assert(branch_summary.dom().contains(au_key));
                        let idx = root_aus_up_to_member_has_index(self.sealed_roots, self.sealed_roots.len() as nat, au_key);
                        assert(image.branch_summary()[au_key] == branch_summary[au_key]);
                    }
                    if branch_summary.contains_key(au_key) {
                        assert(branch_summary.dom().contains(au_key));
                        assert(to_aus(self.sealed_roots.to_set()).contains(au_key));
                        assert(root_aus_up_to(self.sealed_roots, self.sealed_roots.len() as nat).contains(au_key));
                        assert(image.branch_summary().dom().contains(au_key));
                        let idx = root_aus_up_to_member_has_index(self.sealed_roots, self.sealed_roots.len() as nat, au_key);
                        assert(image.branch_summary()[au_key] == branch_summary[au_key]);
                    }
                }
            );
        };
        assert(image.live_persistent() == self.disk.visible().restrict(addresses_in_aus(aus))) by {
            assert_maps_equal!(
                image.live_persistent(),
                self.disk.visible().restrict(addresses_in_aus(aus)),
                addr => {
                    if image.live_persistent().contains_key(addr) {
                        assert(addresses_in_aus(aus).contains(addr));
                        assert(self.disk.persistent.restrict(addresses_in_aus(aus)).contains_key(addr));
                    }
                    if self.disk.visible().restrict(addresses_in_aus(aus)).contains_key(addr) {
                        assert(addresses_in_aus(aus).contains(addr));
                        assert(self.disk.persistent.restrict(addresses_in_aus(aus)).contains_key(addr));
                    }
                }
            );
        };
        assert(image.sealed_stack_i().sealed_disk.entries == self.sealed_stack_i().sealed_disk.entries) by {
            assert_maps_equal!(
                image.sealed_stack_i().sealed_disk.entries,
                self.sealed_stack_i().sealed_disk.entries,
                addr => {
                    if image.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                        assert(addresses_in_aus(aus).contains(addr));
                    }
                    if self.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                        assert(addresses_in_aus(aus).contains(addr));
                    }
                }
            );
        };
        assert(image.sealed_stack_i() == self.sealed_stack_i());
        assert(image.sealed_stack_i().wf(image.branch_summary()));
        assert(image.branch_summary() == image.branch_summary());
        assert(image.stack_wf());
    }
}

impl CachingDiskBranch::State {
    pub proof fn next_preserves_seq_end_lower_bound(pre: Self, post: Self, lbl: CachingDiskBranch::Label, lower: nat)
        requires
            pre.inv(),
            lower <= pre.seq_end,
            CachingDiskBranch::State::next(pre, post, lbl),
        ensures
            lower <= post.seq_end,
    {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step| CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                reveal(CachingDiskBranch::State::disk_internal);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::observe_persisted_roots(target_count) => {
                reveal(CachingDiskBranch::State::observe_persisted_roots);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::load_metadata(reads) => {
                reveal(CachingDiskBranch::State::load_metadata);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::query(receipts, reads) => {
                reveal(CachingDiskBranch::State::query);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::append(new_disk, new_active_branch, receipt, init_root, reads, writes) => {
                reveal(CachingDiskBranch::State::append);
                assert(post.seq_end == pre.seq_end + lbl.arrow_AppendLabel_keys().len());
            },
            CachingDiskBranch::Step::freeze_as() => {
                reveal(CachingDiskBranch::State::freeze_as);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::freeze_prepared() => {
                reveal(CachingDiskBranch::State::freeze_prepared);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::internal_noop() => {
                reveal(CachingDiskBranch::State::internal_noop);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::internal_grow(new_disk, new_root_addr, reads, writes) => {
                reveal(CachingDiskBranch::State::internal_grow);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::internal_split(new_disk, new_child_addr, receipt, split_arg, reads, writes) => {
                reveal(CachingDiskBranch::State::internal_split);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::internal_seal(written_disk, aux_ptr, reads, writes) => {
                reveal(CachingDiskBranch::State::internal_seal);
                assert(post.seq_end == pre.seq_end);
            },
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                reveal(CachingDiskBranch::State::internal_fill_au);
                assert(post.seq_end == pre.seq_end);
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn next_preserves_loaded_root_prefix(
        pre: Self,
        post: Self,
        lbl: CachingDiskBranch::Label,
        roots: Seq<Address>,
    )
        requires
            pre.inv(),
            pre.metadata_loaded,
            roots.len() <= pre.sealed_roots.len(),
            pre.sealed_roots.subrange(0, roots.len() as int) == roots,
            CachingDiskBranch::State::next(pre, post, lbl),
        ensures
            post.metadata_loaded,
            roots.len() <= post.sealed_roots.len(),
            post.sealed_roots.subrange(0, roots.len() as int) == roots,
    {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step| CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::load_metadata(reads) => {
                reveal(CachingDiskBranch::State::load_metadata);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(pre.branch_summary.dom() <= post.branch_summary.dom()) by {
                    assert forall |au: AU| #[trigger] pre.branch_summary.dom().contains(au)
                        implies post.branch_summary.dom().contains(au) by {
                        assert(post.branch_summary.contains_key(au));
                    }
                };
                assert(pre.branch_metadata_loaded());
                branch_summary_from_reads_up_to_self_ensures(
                    pre.sealed_roots,
                    pre.visible_branch_nodes(),
                    pre.sealed_roots.len() as nat,
                );
                assert(pre.branch_summary == pre.interpreted_branch_summary());
                assert(pre.branch_summary.dom()
                    =~= root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat));
                assert(root_aus_up_to(post.sealed_roots, post.sealed_roots.len() as nat)
                    <= post.branch_summary.dom()) by {
                    assert(root_aus_up_to(pre.sealed_roots, pre.sealed_roots.len() as nat)
                        <= pre.branch_summary.dom());
                }
            },
            CachingDiskBranch::Step::internal_seal(written_disk, aux_ptr, reads, writes) => {
                reveal(CachingDiskBranch::State::internal_seal);
                assert(post.metadata_loaded == pre.metadata_loaded);
                assert(post.sealed_roots.len() == pre.sealed_roots.len() + 1);
                assert(post.sealed_roots.subrange(0, roots.len() as int) == roots) by {
                    assert_seqs_equal!(
                        post.sealed_roots.subrange(0, roots.len() as int),
                        roots,
                        i => {
                            assert(post.sealed_roots[i] == pre.sealed_roots[i]);
                            assert(pre.sealed_roots.subrange(0, roots.len() as int)[i]
                                == pre.sealed_roots[i]);
                        }
                    );
                }
            },
            CachingDiskBranch::Step::append(new_disk, new_active_branch, receipt, init_root, reads, writes) => {
                reveal(CachingDiskBranch::State::append);
                assert(post.metadata_loaded == pre.metadata_loaded);
                assert(post.sealed_roots == pre.sealed_roots);
            },
            CachingDiskBranch::Step::internal_noop() => {
                reveal(CachingDiskBranch::State::internal_noop);
                assert(post == pre);
            },
            CachingDiskBranch::Step::internal_grow(new_disk, new_root_addr, reads, writes) => {
                reveal(CachingDiskBranch::State::internal_grow);
                assert(post.metadata_loaded == pre.metadata_loaded);
                assert(post.sealed_roots == pre.sealed_roots);
            },
            CachingDiskBranch::Step::internal_split(new_disk, new_child_addr, receipt, split_arg, reads, writes) => {
                reveal(CachingDiskBranch::State::internal_split);
                assert(post.metadata_loaded == pre.metadata_loaded);
                assert(post.sealed_roots == pre.sealed_roots);
            },
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                reveal(CachingDiskBranch::State::internal_fill_au);
                assert(post.metadata_loaded == pre.metadata_loaded);
                assert(post.sealed_roots == pre.sealed_roots);
            },
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                reveal(CachingDiskBranch::State::disk_internal);
                assert(post.metadata_loaded == pre.metadata_loaded);
                assert(post.sealed_roots == pre.sealed_roots);
            },
            CachingDiskBranch::Step::observe_persisted_roots(target_count) => {
                reveal(CachingDiskBranch::State::observe_persisted_roots);
                assert(post.metadata_loaded == pre.metadata_loaded);
                assert(post.sealed_roots == pre.sealed_roots);
            },
            CachingDiskBranch::Step::query(receipts, reads) => {
                reveal(CachingDiskBranch::State::query);
                assert(post == pre);
            },
            CachingDiskBranch::Step::freeze_as() => {
                reveal(CachingDiskBranch::State::freeze_as);
                assert(post == pre);
            },
            CachingDiskBranch::Step::freeze_prepared() => {
                reveal(CachingDiskBranch::State::freeze_prepared);
                assert(post == pre);
            },
            _ => {
                assert(false);
            },
        }
    }
}

}
