// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map_lib::lemma_values_finite;
use vstd::{assert_sets_equal, map::*, set::*};

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranchBetree_v::{
    branch_summary_insert_ensures, map_with_disjoint_values, summary_aus,
};
use crate::allocation_layer::AllocationBranch_v::{BranchNode as AllocationBranchNode, Summary};
use crate::allocation_layer::Likes_v::restrict_domain_au;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::{LinkedBranch, SplitArg};
use crate::betree::Utils_v::lemma_union_set_of_sets_subset;
use crate::disk::GenericDisk_v::{addrs_closed, set_addrs_disjoint_aus, AU, Address, Pointer};
use crate::implementation::AllocationBranchStack_v::SealedAllocationBranchStack;
use crate::implementation::Cache_v::{Cache, Entry, Slot};
use crate::implementation::CachedBranch_v::{init_mini_allocator, CachedBranch, LoadedPathReceipt};
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::spec::Messages_t::{nop_delta, Message};

verus! {

proof fn mini_allocator_add_aus_preserves_all_aus(mini_allocator: MiniAllocator, aus: Set<AU>)
    requires
        mini_allocator.wf(),
    ensures
        mini_allocator.add_aus(aus).all_aus() == mini_allocator.all_aus() + aus,
{
    assert forall |au: AU| #[trigger] mini_allocator.add_aus(aus).all_aus().contains(au)
        <==> (mini_allocator.all_aus() + aus).contains(au) by { };
}

pub proof fn mini_allocator_add_aus_page_is_reserved(
    mini_allocator: MiniAllocator,
    aus: Set<AU>,
    addr: Address,
)
    requires
        mini_allocator.wf(),
        aus.disjoint(mini_allocator.all_aus()),
    ensures
        mini_allocator.add_aus(aus).page_is_reserved(addr)
            <==> mini_allocator.page_is_reserved(addr),
{
    let post = mini_allocator.add_aus(aus);
    if mini_allocator.allocs.contains_key(addr.au) {
        assert(!aus.contains(addr.au));
        assert(post.allocs[addr.au] == mini_allocator.allocs[addr.au]);
    } else if aus.contains(addr.au) {
        assert(post.allocs[addr.au] == crate::allocation_layer::MiniAllocator_v::PageAllocator::new(addr.au));
        assert(!post.allocs[addr.au].reserved.contains(addr));
    } else {
        assert(!post.allocs.contains_key(addr.au));
    }
}

pub proof fn mini_allocator_allocate_preserves_all_aus(mini_allocator: MiniAllocator, addr: Address)
    requires
        mini_allocator.wf(),
        mini_allocator.can_allocate(addr),
    ensures
        mini_allocator.allocate(addr).all_aus() == mini_allocator.all_aus(),
{
    assert forall |au: AU| #[trigger] mini_allocator.allocate(addr).all_aus().contains(au)
        <==> mini_allocator.all_aus().contains(au) by {
        if au == addr.au {
            assert(mini_allocator.all_aus().contains(au));
        }
    };
}

pub proof fn mini_allocator_no_reserved_pages(mini_allocator: MiniAllocator, addr: Address)
    requires
        mini_allocator.reserved_aus() == Set::<AU>::empty(),
    ensures
        !mini_allocator.page_is_reserved(addr),
{
    if mini_allocator.page_is_reserved(addr) {
        assert(mini_allocator.allocs[addr.au].reserved.contains(addr));
        assert(!mini_allocator.allocs[addr.au].has_no_outstanding_refs());
        assert(mini_allocator.reserved_aus().contains(addr.au));
        assert(false);
    }
}

pub proof fn mini_allocator_prune_all_aus_subset(mini_allocator: MiniAllocator, aus: Set<AU>)
    requires
        mini_allocator.wf(),
    ensures
        mini_allocator.prune(aus).all_aus() <= mini_allocator.all_aus(),
{
    let post = mini_allocator.prune(aus);
    assert forall |au: AU| #[trigger] post.all_aus().contains(au)
        implies mini_allocator.all_aus().contains(au) by {
        assert(post.allocs.contains_key(au));
        assert(mini_allocator.allocs.contains_key(au));
    }
}

proof fn mini_allocator_prune_disjoint_from_pruned_aus(mini_allocator: MiniAllocator, aus: Set<AU>)
    requires
        mini_allocator.wf(),
    ensures
        aus.disjoint(mini_allocator.prune(aus).all_aus()),
{
    let post = mini_allocator.prune(aus);
    assert forall |au: AU| #[trigger] aus.contains(au)
        implies !post.all_aus().contains(au) by {
        if post.all_aus().contains(au) {
            assert(post.allocs.contains_key(au));
            assert(!post.allocs.contains_key(au));
        }
    }
}

proof fn mini_allocator_allocate_in_reserved_au_preserves_reserved_aus(
    mini_allocator: MiniAllocator,
    addr: Address,
)
    requires
        mini_allocator.wf(),
        mini_allocator.can_allocate(addr),
        mini_allocator.reserved_aus().contains(addr.au),
    ensures
        mini_allocator.allocate(addr).reserved_aus() == mini_allocator.reserved_aus(),
{
    let post = mini_allocator.allocate(addr);
    assert forall |au: AU| #[trigger] post.reserved_aus().contains(au)
        <==> mini_allocator.reserved_aus().contains(au) by {
        assert(post.allocs.contains_key(au) <==> mini_allocator.allocs.contains_key(au));
        if au == addr.au {
            assert(post.allocs[au].reserved.contains(addr));
            assert(!post.allocs[au].has_no_outstanding_refs());
            assert(!mini_allocator.allocs[au].has_no_outstanding_refs());
        } else if post.allocs.contains_key(au) {
            assert(post.allocs[au] == mini_allocator.allocs[au]);
        }
    }
    assert_sets_equal!(post.reserved_aus(), mini_allocator.reserved_aus());
}

pub proof fn branch_summary_insert_fresh_ensures(
    branch_summary: Map<AU, Set<AU>>,
    root_au: AU,
    summary: Set<AU>,
)
    requires
        branch_summary.dom().finite(),
        map_with_disjoint_values(branch_summary),
        !branch_summary.contains_key(root_au),
        summary.contains(root_au),
        summary_aus(branch_summary).disjoint(summary),
    ensures ({
        let post_summary = branch_summary.insert(root_au, summary);
        &&& map_with_disjoint_values(post_summary)
        &&& summary_aus(post_summary) == summary_aus(branch_summary) + summary
    })
{
    broadcast use lemma_union_set_of_sets_subset;

    let pre_summary_aus = summary_aus(branch_summary);
    let post_summary = branch_summary.insert(root_au, summary);
    lemma_values_finite(branch_summary);

    assert forall |k1, k2| #[trigger] post_summary.contains_key(k1)
        && #[trigger] post_summary.contains_key(k2) && k1 != k2
        implies post_summary[k1].disjoint(post_summary[k2])
    by {
        if k1 == root_au || k2 == root_au {
            let other = if k1 == root_au { k2 } else { k1 };
            assert(branch_summary.values().contains(post_summary[other]));
            assert(post_summary[other] <= pre_summary_aus);
        } else {
            assert(branch_summary.contains_key(k1));
            assert(branch_summary.contains_key(k2));
        }
    }

    lemma_values_finite(post_summary);
    assert(post_summary.contains_key(root_au));
    assert(post_summary.contains_value(summary));
    lemma_union_set_of_sets_subset(post_summary.values(), summary);

    assert(!branch_summary.values().contains(summary)) by {
        if branch_summary.values().contains(summary) {
            assert(summary <= pre_summary_aus);
            assert(pre_summary_aus.contains(root_au));
            assert(false);
        }
    }
    assert(post_summary.remove(root_au) =~= branch_summary);
    assert(post_summary.values().remove(summary) =~= branch_summary.values());
}

pub proof fn mini_allocator_allocate_page_is_reserved(
    mini_allocator: MiniAllocator,
    new_addr: Address,
    addr: Address,
)
    requires
        mini_allocator.wf(),
        mini_allocator.can_allocate(new_addr),
    ensures
        mini_allocator.allocate(new_addr).page_is_reserved(addr)
            <==> (addr == new_addr || mini_allocator.page_is_reserved(addr)),
{
    let post = mini_allocator.allocate(new_addr);
    if addr == new_addr {
        assert(post.page_is_reserved(addr));
    } else if addr.au == new_addr.au {
        assert(post.allocs[addr.au] == mini_allocator.allocs[addr.au].reserve(set![new_addr]));
        assert(post.page_is_reserved(addr) <==> mini_allocator.page_is_reserved(addr));
    } else {
        assert(post.allocs.contains_key(addr.au) <==> mini_allocator.allocs.contains_key(addr.au));
        if post.allocs.contains_key(addr.au) {
            assert(post.allocs[addr.au] == mini_allocator.allocs[addr.au]);
        }
        assert(post.page_is_reserved(addr) <==> mini_allocator.page_is_reserved(addr));
    }
}

proof fn async_disk_internal_pending_dom_preserved(pre: AsyncDisk::State, post: AsyncDisk::State)
    requires
        pre.inv(),
        AsyncDisk::State::next(pre, post, AsyncDisk::Label::Internal{}),
    ensures
        post.requests.dom() + post.responses.dom() == pre.requests.dom() + pre.responses.dom(),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let lbl = AsyncDisk::Label::Internal{};
    let step = choose |step| AsyncDisk::State::next_by(pre, post, lbl, step);
    match step {
        AsyncDisk::Step::process_read(id) => {
            let resp = DiskResponse::ReadResp{data: pre.content[pre.requests[id]->from]};
            assert(post.requests == pre.requests.remove(id));
            assert(post.responses == pre.responses.insert(id, resp));
            assert_sets_equal!(post.requests.dom() + post.responses.dom(), pre.requests.dom() + pre.responses.dom());
        }
        AsyncDisk::Step::process_write(id) => {
            let resp = DiskResponse::WriteResp{};
            assert(post.requests == pre.requests.remove(id));
            assert(post.responses == pre.responses.insert(id, resp));
            assert_sets_equal!(post.requests.dom() + post.responses.dom(), pre.requests.dom() + pre.responses.dom());
        }
        _ => {
            assert(false);
        }
    }
}

proof fn cache_lookup_gets_addr(cache: Cache::State, addr: Address)
    requires
        cache.inv(),
        cache.lookup_map.contains_key(addr),
    ensures
        cache.entries.contains_key(cache.lookup_map[addr]),
        cache.entries[cache.lookup_map[addr]].get_addr() == addr,
{
    cache.build_lookup_map_ensures();
}

proof fn cache_filled_entry_in_lookup(cache: Cache::State, slot: Slot)
    requires
        cache.inv(),
        cache.entries.contains_key(slot),
        cache.entries[slot] is Filled,
    ensures
        cache.lookup_map.contains_key(cache.entries[slot].get_addr()),
        cache.lookup_map[cache.entries[slot].get_addr()] == slot,
{
    cache.build_lookup_map_ensures();
}

proof fn cache_internal_preserves_pending_slot(pre: Cache::State, post: Cache::State, addr: Address)
    requires
        pre.inv(),
        Cache::State::next(pre, post, Cache::Label::Internal{}),
        pre.lookup_map.contains_key(addr),
        ({
            let slot = pre.lookup_map[addr];
            ||| pre.entries[slot] is Loading
            ||| pre.status_map[slot] is Writeback
        }),
    ensures
        post.lookup_map.contains_key(addr),
        post.lookup_map[addr] == pre.lookup_map[addr],
        post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]],
        post.status_map[post.lookup_map[addr]] == pre.status_map[pre.lookup_map[addr]],
{
    Cache::State::inv_next(pre, post, Cache::Label::Internal{});
    let slot = pre.lookup_map[addr];
    cache_lookup_gets_addr(pre, addr);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let lbl = Cache::Label::Internal{};
    let step = choose |step| Cache::State::next_by(pre, post, lbl, step);
    match step {
        Cache::Step::reserve(new_slots_mapping) => {
            assert(!new_slots_mapping.contains_key(slot)) by {
                if new_slots_mapping.contains_key(slot) {
                    assert(pre.entries[slot] is Empty);
                }
            }
            assert(!new_slots_mapping.invert().contains_key(addr)) by {
                if new_slots_mapping.invert().contains_key(addr) {
                    reveal(Map::invert);
                    let mapped_slot = new_slots_mapping.invert()[addr];
                    assert(new_slots_mapping.contains_pair(mapped_slot, addr));
                    assert(new_slots_mapping.contains_value(addr));
                    assert(new_slots_mapping.values().contains(addr));
                    assert(pre.lookup_map.dom().contains(addr));
                    assert(false);
                }
            }
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::evict(evicted_slots) => {
            assert(!evicted_slots.contains(slot)) by {
                if evicted_slots.contains(slot) {
                    assert(pre.entries[slot] is Filled);
                    assert(pre.status_map[slot] is Clean);
                }
            }
            let evicted_addrs = Map::new(
                |slot: Slot| evicted_slots.contains(slot),
                |slot: Slot| pre.entries[slot].get_addr(),
            ).values();
            assert(!evicted_addrs.contains(addr)) by {
                if evicted_addrs.contains(addr) {
                    let evicted_slot = choose |s: Slot|
                        evicted_slots.contains(s)
                        && #[trigger] pre.entries[s].get_addr() == addr;
                    assert(pre.entries[evicted_slot] is Filled);
                    cache_filled_entry_in_lookup(pre, evicted_slot);
                    assert(pre.lookup_map[addr] == evicted_slot);
                    assert(slot == evicted_slot);
                    assert(false);
                }
            }
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::noop() => {
            assert(post == pre);
        }
        _ => {
            assert(false);
        }
    }
}

proof fn cache_disk_ops_preserves_pending_slot(
    pre: Cache::State,
    post: Cache::State,
    cache_requests: Set<DiskRequest>,
    cache_responses: Map<Address, DiskResponse>,
    addr: Address,
)
    requires
        pre.inv(),
        Cache::State::next(
            pre,
            post,
            Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses},
        ),
        pre.lookup_map.contains_key(addr),
        !cache_responses.contains_key(addr),
        ({
            let slot = pre.lookup_map[addr];
            ||| pre.entries[slot] is Loading
            ||| pre.status_map[slot] is Writeback
        }),
    ensures
        post.lookup_map.contains_key(addr),
        post.lookup_map[addr] == pre.lookup_map[addr],
        post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]],
        post.status_map[post.lookup_map[addr]] == pre.status_map[pre.lookup_map[addr]],
{
    Cache::State::inv_next(
        pre,
        post,
        Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses},
    );
    let slot = pre.lookup_map[addr];
    cache_lookup_gets_addr(pre, addr);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
    let step = choose |step| Cache::State::next_by(pre, post, lbl, step);
    match step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert(cache_responses.is_empty());
            assert(!new_slots_mapping.contains_key(slot)) by {
                if new_slots_mapping.contains_key(slot) {
                    assert(pre.entries[slot] is Empty);
                }
            }
            assert(!new_slots_mapping.invert().contains_key(addr)) by {
                if new_slots_mapping.invert().contains_key(addr) {
                    reveal(Map::invert);
                    let mapped_slot = new_slots_mapping.invert()[addr];
                    assert(new_slots_mapping.contains_pair(mapped_slot, addr));
                    assert(new_slots_mapping.contains_value(addr));
                    assert(new_slots_mapping.values().contains(addr));
                    assert(pre.lookup_map.dom().contains(addr));
                    assert(false);
                }
            }
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::load_complete() => {
            assert(cache_requests.is_empty());
            let restricted_lookup = pre.lookup_map.restrict(cache_responses.dom());
            let slot_addr_map = restricted_lookup.invert();
            assert(!slot_addr_map.contains_key(slot)) by {
                if slot_addr_map.contains_key(slot) {
                    Cache::State::invert_contains_pair(restricted_lookup, slot);
                    let resp_addr = slot_addr_map[slot];
                    assert(restricted_lookup.contains_pair(resp_addr, slot));
                    assert(cache_responses.contains_key(resp_addr));
                    assert(pre.lookup_map.contains_key(resp_addr));
                    assert(pre.lookup_map[resp_addr] == slot);
                    pre.build_lookup_map_ensures();
                    assert(pre.lookup_map.is_injective());
                    assert(resp_addr == addr);
                    assert(false);
                }
            }
            assert(post.lookup_map == pre.lookup_map);
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::writeback_initiate() => {
            assert(cache_responses.is_empty());
            let request_slot_map = Map::new(
                |req: DiskRequest| cache_requests.contains(req),
                |req: DiskRequest| pre.lookup_map[req->to],
            );
            let writeback_slots = request_slot_map.values();
            assert(!writeback_slots.contains(slot)) by {
                if writeback_slots.contains(slot) {
                    let req = choose |req: DiskRequest|
                        request_slot_map.contains_key(req)
                        && #[trigger] request_slot_map[req] == slot;
                    assert(cache_requests.contains(req));
                    assert(req is WriteReq);
                    assert(pre.lookup_map.contains_key(req->to));
                    assert(pre.entries[pre.lookup_map[req->to]]
                        == Entry::Filled{addr: req->to, data: req->data});
                    assert(pre.status_map[pre.lookup_map[req->to]] is Dirty);
                    assert(pre.lookup_map[req->to] == slot);
                    if pre.entries[slot] is Loading {
                        assert(false);
                    } else {
                        assert(pre.status_map[slot] is Writeback);
                        assert(false);
                    }
                }
            }
            assert(post.lookup_map == pre.lookup_map);
            assert(post.entries == pre.entries);
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::writeback_complete() => {
            assert(cache_requests.is_empty());
            let resps_slots = pre.lookup_map.restrict(cache_responses.dom()).values();
            assert(!resps_slots.contains(slot)) by {
                if resps_slots.contains(slot) {
                    let resp_addr = choose |a: Address|
                        pre.lookup_map.restrict(cache_responses.dom()).contains_key(a)
                        && #[trigger] pre.lookup_map.restrict(cache_responses.dom())[a] == slot;
                    assert(cache_responses.contains_key(resp_addr));
                    assert(pre.lookup_map.contains_key(resp_addr));
                    assert(pre.lookup_map[resp_addr] == slot);
                    pre.build_lookup_map_ensures();
                    assert(pre.lookup_map.is_injective());
                    assert(resp_addr == addr);
                    assert(false);
                }
            }
            assert(post.lookup_map == pre.lookup_map);
            assert(post.entries == pre.entries);
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        _ => {
            assert(false);
        }
    }
}

proof fn cache_response_absent_for_unresponded_outstanding(
    pre: ConcreteBranch::State,
    cache_responses: Map<Address, DiskResponse>,
    disk_responses: Map<ID, DiskResponse>,
    id: ID,
)
    requires
        pre.outstanding_cache_reqs.is_injective(),
        pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
        pre.outstanding_cache_reqs.contains_key(id),
        !disk_responses.contains_key(id),
    ensures
        !cache_responses.contains_key(pre.outstanding_cache_reqs[id]),
{
    let addr = pre.outstanding_cache_reqs[id];
    if cache_responses.contains_key(addr) {
        let restricted = pre.outstanding_cache_reqs.restrict(disk_responses.dom());
        assert(restricted.values().contains(addr));
        let id2 = choose |id2: ID|
            restricted.contains_key(id2) && #[trigger] restricted[id2] == addr;
        assert(disk_responses.contains_key(id2));
        assert(pre.outstanding_cache_reqs.contains_key(id2));
        assert(pre.outstanding_cache_reqs[id2] == addr);
        if id2 != id {
            assert(pre.outstanding_cache_reqs[id2] != pre.outstanding_cache_reqs[id]);
        } else {
            assert(disk_responses.contains_key(id));
        }
        assert(false);
    }
}

pub open spec fn to_branch_nodes(raw_pages: Map<Address, RawPage>) -> Map<Address, AllocationBranchNode>
{
    Map::new(
        |addr: Address| raw_pages.contains_key(addr),
        |addr: Address| raw_page_to_branch_node(raw_pages[addr]),
    )
}

pub open spec fn init_projected_branch(cached_branch: CachedBranch, disk: AsyncDisk::State) -> LinkedBranch<Summary>
    recommends
        cached_branch.sealed,
        cached_branch.root is Some,
{
    LinkedBranch {
        root: cached_branch.root.unwrap(),
        disk_view: crate::betree::LinkedBranch_v::DiskView {
            entries: to_branch_nodes(Map::new(
                |addr: Address| disk.content.contains_key(addr),
                |addr: Address| disk.content[addr],
            )),
        },
    }
}

pub open spec fn init_projection_valid_at(
    cached_branches: Seq<CachedBranch>,
    disk: AsyncDisk::State,
    idx: int,
) -> bool
    recommends 0 <= idx < cached_branches.len()
{
    let cached_branch = cached_branches[idx];
    &&& cached_branch.wf()
    &&& cached_branch.sealed
    &&& cached_branch.root is Some
    &&& init_projected_branch(cached_branch, disk).valid_sealed_branch()
}

pub open spec fn init_projection_valid(cached_branches: Seq<CachedBranch>, disk: AsyncDisk::State) -> bool
{
    forall |idx: int|
        0 <= idx < cached_branches.len()
        ==> #[trigger] init_projection_valid_at(cached_branches, disk, idx)
}

pub open spec fn init_branch_summary_up_to(
    cached_branches: Seq<CachedBranch>,
    disk: AsyncDisk::State,
    end: nat,
) -> Map<AU, Summary>
    recommends end <= cached_branches.len()
    decreases end
{
    if end == 0 {
        Map::<AU, Summary>::empty()
    } else {
        let idx = (end - 1) as int;
        let cached_branch = cached_branches[idx];
        init_branch_summary_up_to(cached_branches, disk, (end - 1) as nat).insert(
            cached_branch.root.unwrap().au,
            init_projected_branch(cached_branch, disk).get_summary(),
        )
    }
}

pub open spec fn init_branch_summary(cached_branches: Seq<CachedBranch>, disk: AsyncDisk::State) -> Map<AU, Summary>
{
    init_branch_summary_up_to(cached_branches, disk, cached_branches.len() as nat)
}

state_machine!{ ConcreteBranch {
    fields {
        pub cached_branches: Seq<CachedBranch>,
        pub branch_summary: Map<AU, Summary>,
        pub seq_end: nat,
        pub mini_allocator: MiniAllocator,
        pub cache: Cache::State,
        pub disk: AsyncDisk::State,
        pub outstanding_cache_reqs: Map<ID, Address>,
    }

    pub enum Label {
        Query{branch_idx: nat, key: Key, msg: Message},
        Append{
            keys: Seq<Key>,
            msgs: Seq<Message>,
        },
        Grow{new_root_addr: Address},
        Split{
            new_child_addr: Address,
            pivot: Key,
            split_arg: SplitArg,
        },
        Seal{aux_ptr: Pointer},
        FillAU{aus: Set<AU>},
        Internal{},
    }

    init!{ initialize(cached_branches: Seq<CachedBranch>, seq_end: nat, init_aus: Set<AU>, cache: Cache::State, cache_slots: nat, disk: AsyncDisk::State) {
        require Cache::State::initialize(cache, cache_slots);
        require disk.inv();
        require disk.requests.is_empty();
        require disk.responses.is_empty();
        require init_projection_valid(cached_branches, disk);
        require init_mini_allocator(init_aus).all_aus() == init_aus;
        require Self::aus_have_no_available_branch_nodes_from(cache, disk, init_aus);
        require summary_aus(init_branch_summary(cached_branches, disk)).disjoint(init_aus);
        require concrete_branch_init_wf(cached_branches, seq_end, init_aus, cache, disk);

        init cached_branches = cached_branches.push(CachedBranch::empty_active());
        init branch_summary = init_branch_summary(cached_branches, disk);
        init seq_end = seq_end;
        init mini_allocator = init_mini_allocator(init_aus);
        init cache = cache;
        init disk = disk;
        init outstanding_cache_reqs = Map::empty();
    }}

    transition!{ query(
        lbl: Label,
        reads: Map<Address, RawPage>,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
    ) {
        require let Label::Query{branch_idx, key, msg} = lbl;
        require pre.wf();
        require query_receipts.len() == pre.cached_branches.len();
        require branch_idx < pre.cached_branches.len();
        let read_nodes = to_branch_nodes(reads);
        require pre.query_matches_stack(branch_idx, key, msg, query_receipts, read_nodes);

        let cache_lbl = Self::cache_access_label(reads, Map::<Address, RawPage>::empty());
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);
    }}

    transition!{ append(
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: Cache::State,
    ) {
        require let Label::Append{keys, msgs} = lbl;
        require pre.wf();
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pre.active_cached_branch().can_append(pre.mini_allocator, receipt, keys, msgs, read_nodes, write_nodes);
        require pre.active_managed_reads_agree(receipt.needed_addrs(), read_nodes);
        let new_active = pre.active_cached_branch().append(receipt, keys, msgs, read_nodes, write_nodes);

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branches = pre.cached_branches.update(pre.active_idx(), new_active);
        update seq_end = pre.seq_end + keys.len();
        update cache = new_cache;
    }}

    transition!{ append_to_empty(
        lbl: Label,
        writes: Map<Address, RawPage>,
        init_root: Address,
        new_cache: Cache::State,
    ) {
        require let Label::Append{keys, msgs} = lbl;
        require pre.wf();
        let write_nodes = to_branch_nodes(writes);
        require pre.active_cached_branch().can_initialize(pre.mini_allocator, init_root, keys, msgs, write_nodes);
        let new_active = pre.active_cached_branch().initialize(init_root, keys, msgs, write_nodes);
        let new_mini_allocator = pre.mini_allocator.allocate(init_root);

        let cache_lbl = Self::cache_access_label(Map::<Address, RawPage>::empty(), writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branches = pre.cached_branches.update(pre.active_idx(), new_active);
        update seq_end = pre.seq_end + keys.len();
        update mini_allocator = new_mini_allocator;
        update cache = new_cache;
    }}

    transition!{ grow(
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
    ) {
        require let Label::Grow{new_root_addr} = lbl;
        require pre.wf();
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pre.active_cached_branch().can_grow(pre.mini_allocator, new_root_addr, read_nodes, write_nodes);
        require pre.active_managed_reads_agree(
            Set::<Address>::empty().insert(pre.active_cached_branch().root.unwrap()),
            read_nodes,
        );
        let new_active = pre.active_cached_branch().grow(pre.mini_allocator, new_root_addr, read_nodes, write_nodes);
        let new_mini_allocator = pre.mini_allocator.allocate(new_root_addr);

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branches = pre.cached_branches.update(pre.active_idx(), new_active);
        update mini_allocator = new_mini_allocator;
        update cache = new_cache;
    }}

    transition!{ split(
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: Cache::State,
    ) {
        require let Label::Split{new_child_addr, pivot, split_arg} = lbl;
        require pre.wf();
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pivot == split_arg.get_pivot();
        require pre.active_cached_branch().can_split(pre.mini_allocator, new_child_addr, receipt, split_arg, read_nodes, write_nodes);
        require pre.active_managed_reads_agree(receipt.needed_addrs().insert(receipt.child_addr()), read_nodes);
        let new_active = pre.active_cached_branch().split(pre.mini_allocator, new_child_addr, receipt, split_arg, read_nodes, write_nodes);
        let new_mini_allocator = pre.mini_allocator.allocate(new_child_addr);

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branches = pre.cached_branches.update(pre.active_idx(), new_active);
        update mini_allocator = new_mini_allocator;
        update cache = new_cache;
    }}

    transition!{ seal(
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
    ) {
        require let Label::Seal{aux_ptr} = lbl;
        require pre.wf();
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pre.active_cached_branch().can_seal(pre.mini_allocator, aux_ptr, read_nodes, write_nodes);
        require pre.active_managed_reads_agree(
            Set::<Address>::empty().insert(pre.active_cached_branch().root.unwrap()),
            read_nodes,
        );
        let sealed_active = pre.active_cached_branch().seal(pre.mini_allocator, aux_ptr, read_nodes, write_nodes);
        let sealed_allocator =
            if aux_ptr is Some {
                pre.mini_allocator.allocate(aux_ptr.unwrap())
            } else {
                pre.mini_allocator
            };
        let new_mini_allocator = MiniAllocator::empty();
        let sealed_linked_branch = LinkedBranch{
            root: pre.overlay_branch().unwrap().root,
            disk_view: crate::betree::LinkedBranch_v::DiskView {
                entries: pre.overlay_branch_entries().union_prefer_right(write_nodes),
            },
        };

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branches = pre.cached_branches.update(pre.active_idx(), sealed_active).push(CachedBranch::empty_active());
        update branch_summary = pre.branch_summary.insert(
            sealed_linked_branch.root.au,
            sealed_linked_branch.get_summary(),
        );
        update mini_allocator = new_mini_allocator;
        update cache = new_cache;
    }}

    transition!{ fill_au(lbl: Label) {
        require let Label::FillAU{aus} = lbl;
        require pre.wf();
        require pre.fresh_aus_for_active(aus);
        require summary_aus(pre.branch_summary).disjoint(aus);

        update mini_allocator = pre.mini_allocator.add_aus(aus);
    }}

    transition!{ internal_cache(lbl: Label, new_cache: Cache::State) {
        require lbl is Internal;
        require pre.wf();
        require Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{});
        require Self::available_raw_pages_from(new_cache, pre.disk) == pre.available_raw_pages();

        update cache = new_cache;
    }}

    transition!{ internal_disk(lbl: Label, new_disk: AsyncDisk::State) {
        require lbl is Internal;
        require pre.wf();
        require AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{});
        require Self::available_raw_pages_from(pre.cache, new_disk) == pre.available_raw_pages();

        update disk = new_disk;
    }}

    transition!{ cache_disk_ops(
        lbl: Label,
        new_cache: Cache::State,
        new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    ) {
        require lbl is Internal;
        require pre.wf();
        require pre.disk_requests_match_cache_requests(cache_requests, disk_requests);
        require pre.disk_responses_match_cache_responses(cache_responses, disk_responses);

        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        let disk_lbl = AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        require AsyncDisk::State::next(pre.disk, new_disk, disk_lbl);
        require Self::available_raw_pages_from(new_cache, new_disk) == pre.available_raw_pages();

        update cache = new_cache;
        update disk = new_disk;
        update outstanding_cache_reqs = pre.next_outstanding_cache_reqs(disk_requests, disk_responses);
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        self.wf()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, cached_branches: Seq<CachedBranch>, seq_end: nat, init_aus: Set<AU>, cache: Cache::State, cache_slots: nat, disk: AsyncDisk::State) {
        let init_state = ConcreteBranch::State{
            cached_branches: cached_branches.push(CachedBranch::empty_active()),
            branch_summary: init_branch_summary(cached_branches, disk),
            seq_end,
            mini_allocator: init_mini_allocator(init_aus),
            cache,
            disk,
            outstanding_cache_reqs: Map::empty(),
        };
        assert(post == init_state);
        assert(post.wf());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>, query_receipts: Seq<Option<LoadedPathReceipt>>) {
        assert(post == pre);
        assert(post.wf());
    }

    #[inductive(append)]
    fn append_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: Cache::State,
    ) {
        match lbl {
            Label::Append{keys, msgs} => {
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let new_active = pre.active_cached_branch().append(receipt, keys, msgs, read_nodes, write_nodes);
                let cache_lbl = Self::cache_access_label(reads, writes);
                let target = receipt.target().addr;

                crate::implementation::Cache_v::State::inv_next(pre.cache, new_cache, cache_lbl);
                assert(post.mini_allocator == pre.mini_allocator);
                assert(write_nodes == crate::implementation::CachedBranch_v::loaded_append_write_nodes(receipt, keys, msgs));
                assert(write_nodes.contains_key(target));
                assert(writes.contains_key(target));
                assert(receipt.needed_addrs().contains(target)) by {
                    let i = receipt.lines.len() - 1;
                    assert(0 <= i < receipt.lines.len());
                    assert(receipt.lines[i].addr == target);
                }
                assert(read_nodes[target] == pre.available_branch_nodes()[target]);
                assert(read_nodes[target] == receipt.target().node);
                assert(pre.available_branch_nodes()[target] == receipt.target().node);
                assert(pre.available_branch_nodes()[target] is Leaf);
                Self::cache_access_write_visible_as_branch_node(pre, post, reads, writes, target);
                assert(post.available_branch_nodes()[target] == write_nodes[target]);
                assert(post.available_branch_nodes()[target] is Leaf);

                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies addr == target by {
                    assert(write_nodes.contains_key(addr));
                }
                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies !summary_aus(pre.branch_summary).contains(addr.au) by {
                    assert(addr == target);
                    assert(pre.active_branch_pages_in_allocator());
                    assert(pre.mini_allocator.all_aus().contains(target.au));
                }
                Self::sealed_disk_i_unchanged_by_cache_access(pre, post, reads, writes);

                assert(pre.available_branch_nodes().dom() == post.available_branch_nodes().dom()) by {
                    assert forall |addr: Address|
                        #[trigger] pre.available_branch_nodes().contains_key(addr)
                        <==> post.available_branch_nodes().contains_key(addr)
                    by {
                        if addr == target {
                            assert(pre.available_branch_nodes().contains_key(target));
                            assert(post.available_branch_nodes().contains_key(target));
                        } else {
                            assert(!writes.contains_key(addr));
                            Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
                        }
                    }
                }
                assert forall |addr: Address|
                    addr != target && #[trigger] pre.available_branch_nodes().contains_key(addr)
                    implies post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr] by {
                    assert(!writes.contains_key(addr));
                    Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
                    if pre.has_cached_page(addr) {
                        assert(post.has_cached_page(addr));
                        assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                    } else {
                        assert(!post.has_cached_page(addr));
                    }
                }
                assert(new_active == pre.active_cached_branch());
                assert(post.cached_branches =~= pre.cached_branches) by {
                    assert forall |i: int|
                        0 <= i < pre.cached_branches.len()
                        implies post.cached_branches[i] == pre.cached_branches[i] by {
                        if i == pre.active_idx() {
                            assert(post.cached_branches[i] == new_active);
                        }
                    }
                }
                assert(post.cached_branches == pre.cached_branches);
                Self::overlay_addrs_same_after_leaf_update(pre, post, pre.active_idx() as nat, target);

                assert(post.cached_branches.len() == pre.cached_branches.len());
                assert(post.active_idx() == pre.active_idx());
                assert(post.active_cached_branch() == new_active);
                assert(post.active_cached_branch() == pre.active_cached_branch());
                assert(post.sealed_roots_i() =~= pre.sealed_roots_i());
                assert(post.branch_summary == pre.branch_summary);
                assert(post.seq_end == pre.seq_end + keys.len());
                assert(post.cached_branches.len() > 0);
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies {
                        &&& #[trigger] post.cached_branches[i].wf()
                        &&& post.cached_branches[i].sealed
                        &&& post.cached_branches[i].root is Some
                    } by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                    assert(pre.cached_branches[i].root is Some);
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].sealed by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].root is Some by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                    assert(pre.cached_branches[i].root is Some);
                }
                assert(post.active_cached_branch().wf());
                assert(!post.active_cached_branch().sealed);
                assert(post.active_cached_branch().valid_allocator(post.mini_allocator));
                assert(post.active_branch_pages_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.all_aus().contains(addr.au) by {
                        assert(post.has_overlay_page(addr));
                        assert(pre.has_overlay_page(addr));
                        assert(pre.overlay_branch_entries().contains_key(addr));
                        assert(pre.mini_allocator.all_aus().contains(addr.au));
                    }
                }
                assert(post.active_branch_pages_reserved_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr) by {
                        assert(post.has_overlay_page(addr));
                        assert(pre.has_overlay_page(addr));
                        assert(pre.overlay_branch_entries().contains_key(addr));
                        assert(post.mini_allocator == pre.mini_allocator);
                        assert(pre.mini_allocator.page_is_reserved(addr));
                    }
                }
                assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus()));
                assert(post.cache_agrees_with_disk());
                assert(map_with_disjoint_values(post.branch_summary));
                assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary)));
                Self::cache_access_preserves_outstanding_reqs_consistent(pre, post, reads, writes);
                assert(post.mini_allocator.wf());
                assert(post.cache.inv());
                assert(post.disk.inv());
                assert(post.outstanding_reqs_consistent());
                assert(post.available_branch_nodes()[target].wf());
                assert(post.active_allocator_aus_have_only_reserved_branch_nodes()) by {
                    assert forall |addr: Address|
                        post.mini_allocator.all_aus().contains(addr.au)
                        && #[trigger] post.available_branch_nodes().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr)
                    by {
                        assert(post.mini_allocator == pre.mini_allocator);
                        if addr == target {
                            assert(pre.overlay_branch_entries().contains_key(target));
                            assert(pre.mini_allocator.page_is_reserved(target));
                        } else {
                            assert(pre.available_branch_nodes().contains_key(addr));
                            assert(pre.mini_allocator.page_is_reserved(addr));
                        }
                    }
                }
                post.wf_from_parts();
            }
            _ => { assert(false); }
        }
    }

    #[inductive(append_to_empty)]
    fn append_to_empty_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        writes: Map<Address, RawPage>,
        init_root: Address,
        new_cache: Cache::State,
    ) {
        match lbl {
            Label::Append{keys, msgs} => {
                let write_nodes = to_branch_nodes(writes);
                let new_active = pre.active_cached_branch().initialize(init_root, keys, msgs, write_nodes);
                let new_mini_allocator = pre.mini_allocator.allocate(init_root);
                let cache_lbl = Self::cache_access_label(Map::<Address, RawPage>::empty(), writes);

                crate::implementation::Cache_v::State::inv_next(pre.cache, new_cache, cache_lbl);
                mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, init_root);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(write_nodes == crate::implementation::CachedBranch_v::loaded_initialize_write_nodes(init_root, keys, msgs));
                assert(write_nodes.contains_key(init_root));
                assert(writes.contains_key(init_root));
                Self::cache_access_write_visible_as_branch_node(
                    pre,
                    post,
                    Map::<Address, RawPage>::empty(),
                    writes,
                    init_root,
                );
                assert(post.available_branch_nodes()[init_root] == AllocationBranchNode::Leaf{keys, msgs});
                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies !summary_aus(pre.branch_summary).contains(addr.au) by {
                    assert(write_nodes.contains_key(addr));
                    assert(addr == init_root);
                    assert(pre.mini_allocator.all_aus().contains(init_root.au));
                }
                Self::sealed_disk_i_unchanged_by_cache_access(
                    pre,
                    post,
                    Map::<Address, RawPage>::empty(),
                    writes,
                );

                assert(post.cached_branches.len() == pre.cached_branches.len());
                assert(post.active_idx() == pre.active_idx());
                assert(post.active_cached_branch() == new_active);
                assert(post.sealed_roots_i() =~= pre.sealed_roots_i());
                assert(post.branch_summary == pre.branch_summary);
                assert(post.seq_end == pre.seq_end + keys.len());
                assert(post.cached_branches.len() > 0);
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies {
                        &&& #[trigger] post.cached_branches[i].wf()
                        &&& post.cached_branches[i].sealed
                        &&& post.cached_branches[i].root is Some
                    } by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                    assert(pre.cached_branches[i].root is Some);
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].root is Some by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                    assert(pre.cached_branches[i].root is Some);
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].sealed by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                }
                assert(post.active_cached_branch().wf());
                assert(!post.active_cached_branch().sealed);
                assert(post.active_cached_branch().valid_allocator(post.mini_allocator)) by {
                    assert(post.active_cached_branch().root == Some(init_root));
                    assert(post.mini_allocator.all_aus().contains(init_root.au));
                }
                assert(post.active_branch_pages_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.all_aus().contains(addr.au) by {
                        assert(post.mini_allocator.page_is_reserved(addr));
                        assert(post.mini_allocator.allocs.contains_key(addr.au));
                    }
                }
                assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus()));
                assert(post.cache_agrees_with_disk());
                assert(map_with_disjoint_values(post.branch_summary));
                assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary)));
                Self::cache_access_preserves_outstanding_reqs_consistent(
                    pre,
                    post,
                    Map::<Address, RawPage>::empty(),
                    writes,
                );
                assert(post.mini_allocator.wf());
                assert(post.cache.inv());
                assert(post.disk.inv());
                assert(post.outstanding_reqs_consistent());
                assert(post.active_allocator_aus_have_only_reserved_branch_nodes()) by {
                    assert forall |addr: Address|
                        post.mini_allocator.all_aus().contains(addr.au)
                        && #[trigger] post.available_branch_nodes().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr)
                    by {
                        mini_allocator_allocate_page_is_reserved(pre.mini_allocator, init_root, addr);
                        if addr == init_root {
                            assert(post.mini_allocator.page_is_reserved(addr));
                        } else {
                            assert(!writes.contains_key(addr)) by {
                                if writes.contains_key(addr) {
                                    assert(write_nodes.contains_key(addr));
                                    assert(addr == init_root);
                                }
                            }
                            Cache::State::access_unwritten_addr_unchanged(
                                pre.cache,
                                post.cache,
                                Map::<Address, RawPage>::empty(),
                                writes,
                                addr,
                            );
                            if pre.has_cached_page(addr) {
                                assert(post.has_cached_page(addr));
                                assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                                assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
                            } else {
                                assert(!post.has_cached_page(addr));
                                assert(post.disk.content.contains_key(addr));
                                assert(pre.disk.content.contains_key(addr));
                                assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
                            }
                            assert(pre.available_branch_nodes().contains_key(addr));
                            assert(pre.mini_allocator.page_is_reserved(addr));
                            assert(post.mini_allocator.page_is_reserved(addr));
                        }
                    }
                }
                post.wf_from_parts();
            }
            _ => { assert(false); }
        }
    }

    #[inductive(grow)]
    fn grow_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
    ) {
        match lbl {
            Label::Grow{new_root_addr} => {
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let new_active = pre.active_cached_branch().grow(
                    pre.mini_allocator,
                    new_root_addr,
                    read_nodes,
                    write_nodes,
                );
                let new_mini_allocator = pre.mini_allocator.allocate(new_root_addr);
                let old_root = pre.active_cached_branch().root.unwrap();
                let cache_lbl = Self::cache_access_label(reads, writes);

                crate::implementation::Cache_v::State::inv_next(pre.cache, new_cache, cache_lbl);
                mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, new_root_addr);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(pre.mini_allocator.all_aus().contains(new_root_addr.au));
                assert(write_nodes == crate::implementation::CachedBranch_v::loaded_grow_write_nodes(
                    old_root,
                    new_root_addr,
                ));
                assert(write_nodes.contains_key(new_root_addr));
                assert(writes.contains_key(new_root_addr));
                Self::cache_access_write_visible_as_branch_node(pre, post, reads, writes, new_root_addr);
                assert(post.available_branch_nodes()[new_root_addr] == AllocationBranchNode::Index{
                    pivots: seq![],
                    children: seq![old_root],
                    aux_ptr: None,
                });
                assert(!pre.mini_allocator.page_is_reserved(new_root_addr));
                assert(!pre.overlay_branch_entries().contains_key(new_root_addr)) by {
                    if pre.overlay_branch_entries().contains_key(new_root_addr) {
                        assert(pre.mini_allocator.page_is_reserved(new_root_addr));
                        assert(false);
                    }
                }

                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies addr == new_root_addr by {
                    assert(write_nodes.contains_key(addr));
                }
                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies !summary_aus(pre.branch_summary).contains(addr.au) by {
                    assert(addr == new_root_addr);
                    assert(pre.mini_allocator.all_aus().contains(new_root_addr.au));
                }
                Self::sealed_disk_i_unchanged_by_cache_access(pre, post, reads, writes);

                assert(post.cached_branches.len() == pre.cached_branches.len());
                assert(post.active_idx() == pre.active_idx());
                assert(post.active_cached_branch() == new_active);
                assert(post.active_cached_branch().root == Some(new_root_addr));
                assert(post.sealed_roots_i() =~= pre.sealed_roots_i());
                assert(post.branch_summary == pre.branch_summary);
                assert(post.seq_end == pre.seq_end);
                assert(post.cached_branches.len() > 0);
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies {
                        &&& #[trigger] post.cached_branches[i].wf()
                        &&& post.cached_branches[i].sealed
                        &&& post.cached_branches[i].root is Some
                    } by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                    assert(pre.cached_branches[i].root is Some);
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].sealed by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].root is Some by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                    assert(pre.cached_branches[i].root is Some);
                }
                assert(post.active_cached_branch().wf());
                assert(!post.active_cached_branch().sealed);
                assert(post.active_cached_branch().valid_allocator(post.mini_allocator));
                assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus()));
                assert(post.cache_agrees_with_disk());
                assert(map_with_disjoint_values(post.branch_summary));
                assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary)));
                Self::cache_access_preserves_outstanding_reqs_consistent(pre, post, reads, writes);
                assert(post.mini_allocator.wf());
                assert(post.cache.inv());
                assert(post.disk.inv());
                assert(post.outstanding_reqs_consistent());
                assert(post.active_branch_pages_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.all_aus().contains(addr.au) by {
                        assert(post.mini_allocator.page_is_reserved(addr));
                        assert(post.mini_allocator.allocs.contains_key(addr.au));
                    }
                }
                assert(post.active_branch_pages_reserved_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr) by {
                        assert(post.active_branch_addrs().contains(addr));
                    }
                }
                assert forall |addr: Address|
                    addr != new_root_addr
                    implies (#[trigger] post.available_branch_nodes().contains_key(addr)
                        <==> pre.available_branch_nodes().contains_key(addr))
                by {
                    assert(!writes.contains_key(addr));
                    Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
                    if pre.has_cached_page(addr) {
                        assert(post.has_cached_page(addr));
                    } else {
                        assert(!post.has_cached_page(addr));
                        assert(post.disk.content.contains_key(addr)
                            == pre.disk.content.contains_key(addr));
                    }
                }
                assert forall |addr: Address|
                    addr != new_root_addr
                    && #[trigger] post.available_branch_nodes().contains_key(addr)
                    implies post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]
                by {
                    assert(!writes.contains_key(addr));
                    Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
                    if pre.has_cached_page(addr) {
                        assert(post.has_cached_page(addr));
                        assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                        assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
                    } else {
                        assert(!post.has_cached_page(addr));
                        assert(post.disk.content.contains_key(addr));
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
                    }
                    assert(post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]);
                }
                assert(post.active_allocator_aus_have_only_reserved_branch_nodes()) by {
                    assert forall |addr: Address|
                        post.mini_allocator.all_aus().contains(addr.au)
                        && #[trigger] post.available_branch_nodes().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr)
                    by {
                        mini_allocator_allocate_page_is_reserved(pre.mini_allocator, new_root_addr, addr);
                        if addr == new_root_addr {
                            assert(post.mini_allocator.page_is_reserved(addr));
                        } else {
                            assert(pre.available_branch_nodes().contains_key(addr));
                            assert(pre.mini_allocator.all_aus().contains(addr.au)) by {
                                mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, new_root_addr);
                            }
                            assert(pre.mini_allocator.page_is_reserved(addr));
                            assert(post.mini_allocator.page_is_reserved(addr));
                        }
                    }
                }
                post.wf_from_parts();
            }
            _ => { assert(false); }
        }
    }

    #[inductive(split)]
    fn split_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: Cache::State,
    ) {
        match lbl {
            Label::Split{new_child_addr, pivot, split_arg} => {
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let new_active = pre.active_cached_branch().split(
                    pre.mini_allocator,
                    new_child_addr,
                    receipt,
                    split_arg,
                    read_nodes,
                    write_nodes,
                );
                let new_mini_allocator = pre.mini_allocator.allocate(new_child_addr);
                let cache_lbl = Self::cache_access_label(reads, writes);
                let parent_addr = receipt.target().addr;
                let child_addr = receipt.child_addr();

                crate::implementation::Cache_v::State::inv_next(pre.cache, new_cache, cache_lbl);
                mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, new_child_addr);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus());
                assert(pre.mini_allocator.all_aus().contains(new_child_addr.au));
                assert(write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
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
                Self::cache_access_write_visible_as_branch_node(pre, post, reads, writes, parent_addr);
                Self::cache_access_write_visible_as_branch_node(pre, post, reads, writes, child_addr);
                Self::cache_access_write_visible_as_branch_node(pre, post, reads, writes, new_child_addr);

                assert(!pre.mini_allocator.page_is_reserved(new_child_addr));
                assert(!pre.overlay_branch_entries().contains_key(new_child_addr)) by {
                    if pre.overlay_branch_entries().contains_key(new_child_addr) {
                        assert(pre.mini_allocator.page_is_reserved(new_child_addr));
                        assert(false);
                    }
                }

                assert(receipt.needed_addrs().contains(parent_addr)) by {
                    let i = receipt.lines.len() - 1;
                    assert(0 <= i < receipt.lines.len());
                    assert(receipt.lines[i].addr == parent_addr);
                }
                assert(receipt.needed_addrs().insert(child_addr).contains(parent_addr));
                assert(receipt.needed_addrs().insert(child_addr).contains(child_addr));
                assert(pre.overlay_branch_entries().contains_key(parent_addr));
                assert(pre.overlay_branch_entries().contains_key(child_addr));
                assert(pre.mini_allocator.all_aus().contains(parent_addr.au));
                assert(pre.mini_allocator.all_aus().contains(child_addr.au));

                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies addr == parent_addr || addr == child_addr || addr == new_child_addr by {
                    assert(write_nodes.contains_key(addr));
                }
                assert forall |addr: Address|
                    #[trigger] writes.contains_key(addr)
                    implies !summary_aus(pre.branch_summary).contains(addr.au) by {
                    if addr == parent_addr {
                        assert(pre.mini_allocator.all_aus().contains(addr.au));
                    } else if addr == child_addr {
                        assert(pre.mini_allocator.all_aus().contains(addr.au));
                    } else {
                        assert(addr == new_child_addr);
                        assert(pre.mini_allocator.all_aus().contains(addr.au));
                    }
                }
                Self::sealed_disk_i_unchanged_by_cache_access(pre, post, reads, writes);

                assert(post.cached_branches.len() == pre.cached_branches.len());
                assert(post.active_idx() == pre.active_idx());
                assert(post.active_cached_branch() == new_active);
                assert(post.active_cached_branch() == pre.active_cached_branch());
                assert(post.sealed_roots_i() =~= pre.sealed_roots_i());
                assert(post.branch_summary == pre.branch_summary);
                assert(post.seq_end == pre.seq_end);
                assert(post.cached_branches.len() > 0);
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies {
                        &&& #[trigger] post.cached_branches[i].wf()
                        &&& post.cached_branches[i].sealed
                        &&& post.cached_branches[i].root is Some
                    } by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                    assert(pre.cached_branches[i].root is Some);
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].sealed by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].root is Some by {
                    assert(post.cached_branches[i] == pre.cached_branches[i]);
                    assert(pre.cached_branches[i].wf());
                    assert(pre.cached_branches[i].sealed);
                    assert(pre.cached_branches[i].root is Some);
                }
                assert(post.active_cached_branch().wf());
                assert(!post.active_cached_branch().sealed);
                assert(post.active_cached_branch().valid_allocator(post.mini_allocator));
                assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus()));
                assert(post.cache_agrees_with_disk());
                assert(map_with_disjoint_values(post.branch_summary));
                assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary)));
                Self::cache_access_preserves_outstanding_reqs_consistent(pre, post, reads, writes);
                assert(post.mini_allocator.wf());
                assert(post.cache.inv());
                assert(post.disk.inv());
                assert(post.outstanding_reqs_consistent());
                assert(post.active_branch_pages_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.all_aus().contains(addr.au) by {
                        assert(post.mini_allocator.page_is_reserved(addr));
                        assert(post.mini_allocator.allocs.contains_key(addr.au));
                    }
                }
                assert(post.active_branch_pages_reserved_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr) by {
                        assert(post.active_branch_addrs().contains(addr));
                    }
                }
                assert forall |addr: Address|
                    addr != parent_addr
                    && addr != child_addr
                    && addr != new_child_addr
                    implies (#[trigger] post.available_branch_nodes().contains_key(addr)
                        <==> pre.available_branch_nodes().contains_key(addr))
                by {
                    assert(!writes.contains_key(addr));
                    Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
                    if pre.has_cached_page(addr) {
                        assert(post.has_cached_page(addr));
                    } else {
                        assert(!post.has_cached_page(addr));
                        assert(post.disk.content.contains_key(addr)
                            == pre.disk.content.contains_key(addr));
                    }
                }
                assert forall |addr: Address|
                    addr != parent_addr
                    && addr != child_addr
                    && addr != new_child_addr
                    && #[trigger] post.available_branch_nodes().contains_key(addr)
                    implies post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]
                by {
                    assert(!writes.contains_key(addr));
                    Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
                    if pre.has_cached_page(addr) {
                        assert(post.has_cached_page(addr));
                        assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                        assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
                    } else {
                        assert(!post.has_cached_page(addr));
                        assert(post.disk.content.contains_key(addr));
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
                    }
                    assert(post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]);
                }
                assert(post.active_allocator_aus_have_only_reserved_branch_nodes()) by {
                    assert forall |addr: Address|
                        post.mini_allocator.all_aus().contains(addr.au)
                        && #[trigger] post.available_branch_nodes().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr)
                    by {
                        mini_allocator_allocate_page_is_reserved(pre.mini_allocator, new_child_addr, addr);
                        if addr == new_child_addr {
                            assert(post.mini_allocator.page_is_reserved(addr));
                        } else if addr == parent_addr {
                            assert(pre.overlay_branch_entries().contains_key(parent_addr));
                            assert(pre.mini_allocator.page_is_reserved(parent_addr));
                            assert(post.mini_allocator.page_is_reserved(addr));
                        } else if addr == child_addr {
                            assert(pre.overlay_branch_entries().contains_key(child_addr));
                            assert(pre.mini_allocator.page_is_reserved(child_addr));
                            assert(post.mini_allocator.page_is_reserved(addr));
                        } else {
                            assert(pre.available_branch_nodes().contains_key(addr));
                            assert(pre.mini_allocator.all_aus().contains(addr.au)) by {
                                mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, new_child_addr);
                            }
                            assert(pre.mini_allocator.page_is_reserved(addr));
                            assert(post.mini_allocator.page_is_reserved(addr));
                        }
                    }
                }
                post.wf_from_parts();
            }
            _ => { assert(false); }
        }
    }

    #[inductive(seal)]
    fn seal_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
    ) {
        match lbl {
            Label::Seal{aux_ptr} => {
                let read_nodes = to_branch_nodes(reads);
                let write_nodes = to_branch_nodes(writes);
                let sealed_active = pre.active_cached_branch().seal(
                    pre.mini_allocator,
                    aux_ptr,
                    read_nodes,
                    write_nodes,
                );
                let sealed_allocator =
                    if aux_ptr is Some {
                        pre.mini_allocator.allocate(aux_ptr.unwrap())
                    } else {
                        pre.mini_allocator
                    };
                let new_mini_allocator = MiniAllocator::empty();
                let sealed_linked_branch = LinkedBranch{
                    root: pre.overlay_branch().unwrap().root,
                    disk_view: crate::betree::LinkedBranch_v::DiskView {
                        entries: pre.overlay_branch_entries().union_prefer_right(write_nodes),
                    },
                };
                let cache_lbl = Self::cache_access_label(reads, writes);

                crate::implementation::Cache_v::State::inv_next(pre.cache, new_cache, cache_lbl);
                if aux_ptr is Some {
                    mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, aux_ptr.unwrap());
                    assert(sealed_allocator.all_aus() == pre.mini_allocator.all_aus());
                }
                assert(new_mini_allocator.reserved_aus() == Set::<AU>::empty());

                assert(post.cached_branches == pre.cached_branches.update(pre.active_idx(), sealed_active).push(CachedBranch::empty_active()));
                assert(post.branch_summary == pre.branch_summary.insert(
                    sealed_linked_branch.root.au,
                    sealed_linked_branch.get_summary(),
                ));
                assert(post.seq_end == pre.seq_end);
                assert(post.mini_allocator == new_mini_allocator);
                assert(post.cache == new_cache);
                assert(post.disk == pre.disk);
                assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);

                assert(post.cached_branches.len() == pre.cached_branches.len() + 1);
                assert(post.cached_branches.len() > 0);
                assert(post.active_idx() == pre.cached_branches.len());
                assert(post.active_cached_branch() == CachedBranch::empty_active());

                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies {
                        &&& #[trigger] post.cached_branches[i].wf()
                        &&& post.cached_branches[i].sealed
                        &&& post.cached_branches[i].root is Some
                    } by {
                    if i < pre.cached_branches.len() - 1 {
                        assert(post.cached_branches[i] == pre.cached_branches[i]);
                        assert(pre.cached_branches[i].wf());
                        assert(pre.cached_branches[i].sealed);
                        assert(pre.cached_branches[i].root is Some);
                    } else {
                        assert(i == pre.cached_branches.len() - 1);
                        assert(post.cached_branches[i] == sealed_active);
                        assert(sealed_active.sealed);
                        assert(sealed_active.root == pre.active_cached_branch().root);
                        assert(pre.active_cached_branch().root is Some);
                        assert(sealed_active.wf());
                        assert(sealed_active.root is Some);
                    }
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].sealed by {
                    if i < pre.cached_branches.len() - 1 {
                        assert(post.cached_branches[i] == pre.cached_branches[i]);
                        assert(pre.cached_branches[i].wf());
                        assert(pre.cached_branches[i].sealed);
                    } else {
                        assert(i == pre.cached_branches.len() - 1);
                        assert(post.cached_branches[i] == sealed_active);
                        assert(sealed_active.sealed);
                    }
                }
                assert forall |i: int|
                    0 <= i < post.cached_branches.len() - 1
                    implies #[trigger] post.cached_branches[i].root is Some by {
                    if i < pre.cached_branches.len() - 1 {
                        assert(post.cached_branches[i] == pre.cached_branches[i]);
                        assert(pre.cached_branches[i].wf());
                        assert(pre.cached_branches[i].sealed);
                        assert(pre.cached_branches[i].root is Some);
                    } else {
                        assert(i == pre.cached_branches.len() - 1);
                        assert(post.cached_branches[i] == sealed_active);
                        assert(sealed_active.root == pre.active_cached_branch().root);
                        assert(pre.active_cached_branch().root is Some);
                    }
                }
                assert(post.active_cached_branch().wf());
                assert(!post.active_cached_branch().sealed);
                assert(post.active_cached_branch().valid_allocator(post.mini_allocator));
                assert(post.active_branch_pages_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.all_aus().contains(addr.au) by {
                        assert(post.mini_allocator.page_is_reserved(addr));
                        assert(post.mini_allocator.reserved_aus().contains(addr.au));
                        assert(false);
                    }
                }
                assert(post.active_branch_pages_reserved_in_allocator()) by {
                    assert forall |addr: Address|
                        #[trigger] post.overlay_branch_entries().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr) by {
                        assert(post.active_branch_addrs().contains(addr));
                    }
                }
                assert(sealed_allocator.all_aus() == pre.mini_allocator.all_aus()) by {
                    if aux_ptr is Some {
                        mini_allocator_allocate_preserves_all_aus(pre.mini_allocator, aux_ptr.unwrap());
                    }
                }
                mini_allocator_prune_all_aus_subset(sealed_allocator, sealed_allocator.reserved_aus());
                mini_allocator_prune_disjoint_from_pruned_aus(sealed_allocator, sealed_allocator.reserved_aus());
                let root = pre.active_cached_branch().root.unwrap();
                assert(sealed_linked_branch.root == root);
                assert(Set::<Address>::empty().insert(root).contains(root));
                assert(read_nodes[root] == pre.overlay_branch_entries()[root]);
                assert(pre.overlay_branch_entries().contains_key(root));
                assert(pre.mini_allocator.page_is_reserved(root));
                assert(pre.mini_allocator.reserved_aus().contains(root.au));
                assert(sealed_linked_branch.get_summary() <= pre.mini_allocator.reserved_aus()) by {
                    if aux_ptr is Some {
                        let ptr = aux_ptr.unwrap();
                        assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
                            root,
                            read_nodes,
                            aux_ptr,
                            pre.mini_allocator.reserved_aus(),
                        ));
                        assert(write_nodes.contains_key(root));
                        assert(write_nodes.contains_key(ptr));
                        assert(write_nodes[ptr] == AllocationBranchNode::Auxiliary(
                            pre.mini_allocator.reserved_aus(),
                        ));
                        assert(sealed_linked_branch.disk_view.entries.contains_key(ptr));
                        assert(sealed_linked_branch.disk_view.entries[ptr]
                            == AllocationBranchNode::Auxiliary(pre.mini_allocator.reserved_aus()));
                        assert(sealed_linked_branch.disk_view.entries.contains_key(root));
                        assert(sealed_linked_branch.root() is Index);
                        assert(sealed_linked_branch.root()->aux_ptr == aux_ptr);
                        assert(sealed_linked_branch.get_summary()
                            == pre.mini_allocator.reserved_aus());
                    } else {
                        assert(write_nodes == Map::<Address, AllocationBranchNode>::empty());
                        assert(!(read_nodes[root] is Index));
                        assert(!(read_nodes[root] is Auxiliary));
                        assert(read_nodes[root] is Leaf);
                        assert(pre.overlay_branch_entries()[root] is Leaf);
                        assert(sealed_linked_branch.root() is Leaf);
                        assert(sealed_linked_branch.get_summary() == set!{root.au});
                    }
                }
                assert(sealed_linked_branch.get_summary().contains(sealed_linked_branch.root.au)) by {
                    if aux_ptr is Some {
                        assert(sealed_linked_branch.get_summary()
                            == pre.mini_allocator.reserved_aus());
                        assert(pre.mini_allocator.reserved_aus().contains(root.au));
                    } else {
                        assert(sealed_linked_branch.get_summary() == set!{root.au});
                    }
                }
                assert(sealed_linked_branch.get_summary() <= sealed_allocator.reserved_aus()) by {
                    if aux_ptr is Some {
                        let ptr = aux_ptr.unwrap();
                        mini_allocator_allocate_in_reserved_au_preserves_reserved_aus(
                            pre.mini_allocator,
                            ptr,
                        );
                        assert(sealed_allocator.reserved_aus() == pre.mini_allocator.reserved_aus());
                    } else {
                        assert(sealed_allocator == pre.mini_allocator);
                    }
                }
                assert(summary_aus(pre.branch_summary).disjoint(sealed_linked_branch.get_summary())) by {
                    assert(sealed_allocator.all_aus() == pre.mini_allocator.all_aus());
                    assert forall |au: AU| #[trigger] summary_aus(pre.branch_summary).contains(au)
                        implies !sealed_linked_branch.get_summary().contains(au) by {
                        if sealed_linked_branch.get_summary().contains(au) {
                            assert(sealed_allocator.reserved_aus().contains(au));
                            assert(sealed_allocator.all_aus().contains(au));
                            assert(pre.mini_allocator.all_aus().contains(au));
                            assert(false);
                        }
                    }
                }
                assert(pre.branch_summary.dom().finite());
                assert(!pre.branch_summary.contains_key(sealed_linked_branch.root.au)) by {
                    if pre.branch_summary.contains_key(sealed_linked_branch.root.au) {
                        assert(pre.branch_summary[sealed_linked_branch.root.au]
                            .contains(sealed_linked_branch.root.au));
                        assert(pre.branch_summary.values().contains(
                            pre.branch_summary[sealed_linked_branch.root.au],
                        ));
                        lemma_values_finite(pre.branch_summary);
                        lemma_union_set_of_sets_subset(
                            pre.branch_summary.values(),
                            pre.branch_summary[sealed_linked_branch.root.au],
                        );
                        assert(summary_aus(pre.branch_summary).contains(sealed_linked_branch.root.au));
                        assert(pre.overlay_branch_entries().contains_key(sealed_linked_branch.root));
                        assert(pre.mini_allocator.all_aus().contains(sealed_linked_branch.root.au));
                        assert(false);
                    }
                }
                branch_summary_insert_fresh_ensures(
                    pre.branch_summary,
                    sealed_linked_branch.root.au,
                    sealed_linked_branch.get_summary(),
                );
                assert(summary_aus(post.branch_summary)
                    == summary_aus(pre.branch_summary) + sealed_linked_branch.get_summary());
                assert(map_with_disjoint_values(post.branch_summary));
                assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus())) by {
                    assert forall |au: AU| #[trigger] summary_aus(post.branch_summary).contains(au)
                        implies !post.mini_allocator.all_aus().contains(au) by {
                        if sealed_linked_branch.get_summary().contains(au) {
                            assert(sealed_allocator.reserved_aus().contains(au));
                        } else {
                            assert(summary_aus(pre.branch_summary).contains(au));
                            assert(!pre.mini_allocator.all_aus().contains(au));
                            assert(sealed_allocator.all_aus() == pre.mini_allocator.all_aus());
                            assert(!sealed_allocator.all_aus().contains(au));
                        }
                    }
                }
                Self::cache_access_preserves_outstanding_reqs_consistent(pre, post, reads, writes);
                assert(post.outstanding_reqs_consistent());
                assert(post.mini_allocator.wf());
                assert(post.cache.inv());
                assert(post.disk.inv());
                assert(post.cache_agrees_with_disk());
                assert(post.active_allocator_aus_have_only_reserved_branch_nodes()) by {
                    assert forall |addr: Address|
                        post.mini_allocator.all_aus().contains(addr.au)
                        && #[trigger] post.available_branch_nodes().contains_key(addr)
                        implies post.mini_allocator.page_is_reserved(addr)
                    by {
                        assert(!sealed_allocator.reserved_aus().contains(addr.au)) by {
                            if sealed_allocator.reserved_aus().contains(addr.au) {
                                assert(!post.mini_allocator.all_aus().contains(addr.au));
                            }
                        }
                        assert(!writes.contains_key(addr)) by {
                            if writes.contains_key(addr) {
                                assert(write_nodes.contains_key(addr));
                                if aux_ptr is Some {
                                    assert(write_nodes == crate::implementation::CachedBranch_v::loaded_seal_write_nodes(
                                        root,
                                        read_nodes,
                                        aux_ptr,
                                        pre.mini_allocator.reserved_aus(),
                                    ));
                                    assert(addr == root || addr == aux_ptr.unwrap());
                                } else {
                                    assert(write_nodes == Map::<Address, AllocationBranchNode>::empty());
                                }
                                if addr == root {
                                    assert(pre.mini_allocator.reserved_aus().contains(addr.au));
                                    if aux_ptr is Some {
                                        mini_allocator_allocate_in_reserved_au_preserves_reserved_aus(
                                            pre.mini_allocator,
                                            aux_ptr.unwrap(),
                                        );
                                    }
                                    assert(sealed_allocator.reserved_aus().contains(addr.au));
                                } else {
                                    assert(aux_ptr is Some);
                                    assert(addr == aux_ptr.unwrap());
                                    if aux_ptr is Some {
                                        mini_allocator_allocate_in_reserved_au_preserves_reserved_aus(
                                            pre.mini_allocator,
                                            aux_ptr.unwrap(),
                                        );
                                    }
                                    assert(sealed_allocator.reserved_aus().contains(addr.au));
                                }
                            }
                        }
                        Cache::State::access_unwritten_addr_unchanged(
                            pre.cache,
                            post.cache,
                            reads,
                            writes,
                            addr,
                        );
                        if pre.has_cached_page(addr) {
                            assert(post.has_cached_page(addr));
                            assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                            assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
                        } else {
                            assert(!post.has_cached_page(addr));
                            assert(post.disk.content.contains_key(addr));
                            assert(pre.disk.content.contains_key(addr));
                            assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
                        }
                        assert(pre.available_branch_nodes().contains_key(addr));
                        assert(sealed_allocator.all_aus() == pre.mini_allocator.all_aus());
                        assert(pre.mini_allocator.all_aus().contains(addr.au));
                        assert(pre.mini_allocator.page_is_reserved(addr));
                        assert(pre.mini_allocator.reserved_aus().contains(addr.au));
                        if aux_ptr is Some {
                            mini_allocator_allocate_in_reserved_au_preserves_reserved_aus(
                                pre.mini_allocator,
                                aux_ptr.unwrap(),
                            );
                        }
                        assert(sealed_allocator.reserved_aus().contains(addr.au));
                        assert(false);
                    }
                }
                assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary))) by {
                    assert forall |addr: Address| #[trigger] post.sealed_disk_i().entries.dom().contains(addr)
                        implies summary_aus(post.branch_summary).contains(addr.au) by { }
                }
                post.wf_from_parts();
            }
            _ => { assert(false); }
        }
    }

    #[inductive(fill_au)]
    fn fill_au_inductive(pre: Self, post: Self, lbl: Label) {
        match lbl {
            Label::FillAU{aus} => {
                mini_allocator_add_aus_preserves_all_aus(pre.mini_allocator, aus);
                assert(post.mini_allocator.all_aus() == pre.mini_allocator.all_aus() + aus);
                Self::available_branch_nodes_ignore_mini_allocator(pre, post);
                assert forall |i: int|
                    0 <= i < post.cached_branches.len()
                    implies #[trigger] post.overlay_branch_at(i as nat) == pre.overlay_branch_at(i as nat) by {
                    Self::overlay_at_ignores_mini_allocator(pre, post, i as nat);
                }
                assert(post.sealed_disk_i() == pre.sealed_disk_i());
                assert(post.sealed_roots_i() =~= pre.sealed_roots_i());
                Self::overlay_at_ignores_mini_allocator(pre, post, pre.active_idx() as nat);
                assert(post.active_idx() == pre.active_idx());
                assert(post.overlay_branch_entries() == pre.overlay_branch_entries());
                assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus())) by {
                    assert forall |au: AU| #[trigger] summary_aus(post.branch_summary).contains(au)
                        implies !post.mini_allocator.all_aus().contains(au) by {
                        if pre.mini_allocator.all_aus().contains(au) {
                            assert(false);
                        }
                        if aus.contains(au) {
                            assert(false);
                        }
                    }
                }
            }
            _ => { assert(false); }
        }
        assert(post.cached_branches.len() > 0);
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies {
                &&& #[trigger] post.cached_branches[i].wf()
                &&& post.cached_branches[i].sealed
                &&& post.cached_branches[i].root is Some
            } by {
                assert(post.cached_branches[i].wf());
                assert(post.cached_branches[i].sealed);
                assert(post.cached_branches[i].root is Some);
            }
        assert(post.active_cached_branch().wf());
        assert(!post.active_cached_branch().sealed);
        assert(post.active_cached_branch().valid_allocator(post.mini_allocator));
        assert(post.active_branch_pages_in_allocator());
        assert(map_with_disjoint_values(post.branch_summary));
        assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus()));
        assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary)));
        assert(post.mini_allocator.wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.outstanding_reqs_consistent());
        assert(post.cache_agrees_with_disk());
        assert(post.wf());
    }

    #[inductive(internal_cache)]
    fn internal_cache_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State) {
        crate::implementation::Cache_v::State::inv_next(pre.cache, new_cache, Cache::Label::Internal{});
        Self::available_branch_nodes_equal_if_raw_pages_equal(pre, post);
        assert forall |i: int|
            0 <= i < post.cached_branches.len()
            implies #[trigger] post.overlay_branch_at(i as nat) == pre.overlay_branch_at(i as nat) by {
            Self::overlay_at_same_available_branch_nodes(pre, post, i as nat);
        }
        assert(post.sealed_disk_i() == pre.sealed_disk_i());
        assert(post.sealed_roots_i() =~= pre.sealed_roots_i());
        Self::overlay_at_same_available_branch_nodes(pre, post, pre.active_idx() as nat);
        assert(post.active_idx() == pre.active_idx());
        assert(post.overlay_branch_entries() == pre.overlay_branch_entries());
        assert(post.outstanding_reqs_requests_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
                implies {
                    let req = post.disk.requests[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& req.addr() == addr
                    &&& req is ReadReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& req is WriteReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                let req = pre.disk.requests[id];
                let addr = pre.outstanding_cache_reqs[id];
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(pre.disk.requests[id] == post.disk.requests[id]);
                if req is ReadReq {
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                    assert(pre.io_id_valid(id));
                    cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
                } else {
                    assert(req is WriteReq);
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]]
                        == Entry::Filled{addr, data: req->data});
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback);
                    assert(pre.io_id_valid(id));
                    cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
                }
            }
        }
        assert(post.outstanding_reqs_responses_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id)
                implies {
                    let resp = post.disk.responses[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& resp is ReadResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& resp->data == post.disk.content[addr]
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& resp is WriteResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: post.disk.content[addr]}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                let resp = pre.disk.responses[id];
                let addr = pre.outstanding_cache_reqs[id];
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(pre.disk.responses[id] == post.disk.responses[id]);
                if resp is ReadResp {
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                    assert(pre.io_id_valid(id));
                    cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
                } else {
                    assert(resp is WriteResp);
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]]
                        == Entry::Filled{addr, data: pre.disk.content[addr]});
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback);
                    assert(pre.io_id_valid(id));
                    cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
                }
            }
        }
        assert forall |id: ID|
            (#[trigger] post.disk.requests.contains_key(id) || #[trigger] post.disk.responses.contains_key(id))
            implies post.io_id_valid(id) by {
            let addr = pre.outstanding_cache_reqs[id];
            assert(pre.io_id_valid(id));
            if post.disk.requests.contains_key(id) {
                let req = pre.disk.requests[id];
                if req is ReadReq {
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                } else {
                    assert(req is WriteReq);
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback);
                }
            } else {
                assert(post.disk.responses.contains_key(id));
                let resp = pre.disk.responses[id];
                if resp is ReadResp {
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                } else {
                    assert(resp is WriteResp);
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback);
                }
            }
            cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
            assert(post.outstanding_cache_reqs.contains_key(id));
            assert(post.cache.lookup_map.contains_key(post.outstanding_cache_reqs[id]));
            cache_lookup_gets_addr(post.cache, post.outstanding_cache_reqs[id]);
            assert(post.cache.entries.contains_key(post.cache.lookup_map[post.outstanding_cache_reqs[id]]));
            assert(post.cache.status_map.contains_key(post.cache.lookup_map[post.outstanding_cache_reqs[id]]));
        }
        assert(post.outstanding_reqs_consistent());
        assert(post.cache_agrees_with_disk());
        assert(post.cached_branches.len() > 0);
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies {
                &&& #[trigger] post.cached_branches[i].wf()
                &&& post.cached_branches[i].sealed
                &&& post.cached_branches[i].root is Some
            } by {
                assert(post.cached_branches[i].wf());
                assert(post.cached_branches[i].sealed);
                assert(post.cached_branches[i].root is Some);
            }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].wf() by {
            assert(post.cached_branches[i].wf());
        }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].sealed by {
            assert(post.cached_branches[i].wf());
            assert(post.cached_branches[i].sealed);
        }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].root is Some by {
            assert(post.cached_branches[i].wf());
            assert(post.cached_branches[i].root is Some);
        }
        assert(post.active_cached_branch().wf());
        assert(!post.active_cached_branch().sealed);
        assert(post.active_cached_branch().valid_allocator(post.mini_allocator));
        assert(post.active_branch_pages_in_allocator());
        assert(map_with_disjoint_values(post.branch_summary));
        assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus()));
        assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary)));
        assert(post.mini_allocator.wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.outstanding_reqs_consistent());
        assert(post.cache_agrees_with_disk());
        post.wf_from_parts();
    }

    #[inductive(internal_disk)]
    fn internal_disk_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State) {
        crate::spec::AsyncDisk_t::inv_next(pre.disk, new_disk, AsyncDisk::Label::Internal{});
        Self::available_branch_nodes_equal_if_raw_pages_equal(pre, post);
        assert forall |i: int|
            0 <= i < post.cached_branches.len()
            implies #[trigger] post.overlay_branch_at(i as nat) == pre.overlay_branch_at(i as nat) by {
            Self::overlay_at_same_available_branch_nodes(pre, post, i as nat);
        }
        assert(post.sealed_disk_i() == pre.sealed_disk_i());
        assert(post.sealed_roots_i() =~= pre.sealed_roots_i());
        Self::overlay_at_same_available_branch_nodes(pre, post, pre.active_idx() as nat);
        assert(post.active_idx() == pre.active_idx());
        assert(post.overlay_branch_entries() == pre.overlay_branch_entries());
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_lbl = AsyncDisk::Label::Internal{};
        let disk_step = choose |step| AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
        match disk_step {
            AsyncDisk::Step::process_read(id) => {
                let resp = DiskResponse::ReadResp{data: pre.disk.content[pre.disk.requests[id]->from]};
                assert(post.disk.requests == pre.disk.requests.remove(id));
                assert(post.disk.responses == pre.disk.responses.insert(id, resp));
                assert(post.disk.content == pre.disk.content);
                assert(post.outstanding_reqs_requests_ok()) by {
                    assert forall |id2: ID| #[trigger] post.disk.requests.contains_key(id2)
                        implies {
                            let req = post.disk.requests[id2];
                            let addr = post.outstanding_cache_reqs[id2];
                            &&& post.outstanding_cache_reqs.contains_key(id2)
                            &&& req.addr() == addr
                            &&& req is ReadReq ==> {
                                let slot = post.cache.lookup_map[addr];
                                &&& post.cache.entries[slot] is Loading
                            }
                            &&& req is WriteReq ==> {
                                let slot = post.cache.lookup_map[addr];
                                &&& post.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                                &&& post.cache.status_map[slot] is Writeback
                            }
                        } by {
                        assert(id2 != id);
                        vstd::map::axiom_map_remove_different(pre.disk.requests, id2, id);
                        assert(pre.disk.requests.contains_key(id2));
                        assert(post.disk.requests[id2] == pre.disk.requests[id2]);
                    }
                }
            }
            AsyncDisk::Step::process_write(id) => {
                let req = pre.disk.requests[id];
                let resp = DiskResponse::WriteResp{};
                assert(post.disk.requests == pre.disk.requests.remove(id));
                assert(post.disk.responses == pre.disk.responses.insert(id, resp));
                assert(post.disk.content == pre.disk.content.insert(req->to, req->data));
                assert(post.outstanding_reqs_requests_ok()) by {
                    assert forall |id2: ID| #[trigger] post.disk.requests.contains_key(id2)
                        implies {
                            let req2 = post.disk.requests[id2];
                            let addr = post.outstanding_cache_reqs[id2];
                            &&& post.outstanding_cache_reqs.contains_key(id2)
                            &&& req2.addr() == addr
                            &&& req2 is ReadReq ==> {
                                let slot = post.cache.lookup_map[addr];
                                &&& post.cache.entries[slot] is Loading
                            }
                            &&& req2 is WriteReq ==> {
                                let slot = post.cache.lookup_map[addr];
                                &&& post.cache.entries[slot] == Entry::Filled{addr, data: req2->data}
                                &&& post.cache.status_map[slot] is Writeback
                            }
                        } by {
                        assert(id2 != id);
                        vstd::map::axiom_map_remove_different(pre.disk.requests, id2, id);
                        assert(pre.disk.requests.contains_key(id2));
                        assert(post.disk.requests[id2] == pre.disk.requests[id2]);
                    }
                }
            }
            _ => {
                assert(false);
            }
        }
        async_disk_internal_pending_dom_preserved(pre.disk, post.disk);
        assert(post.disk.requests.dom() + post.disk.responses.dom() == pre.disk.requests.dom() + pre.disk.responses.dom());
        assert(pre.disk.requests.dom() + pre.disk.responses.dom() == pre.outstanding_cache_reqs.dom());
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.outstanding_reqs_consistent());
        assert(post.cache_agrees_with_disk());
        assert(post.cached_branches.len() > 0);
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies {
                &&& #[trigger] post.cached_branches[i].wf()
                &&& post.cached_branches[i].sealed
                &&& post.cached_branches[i].root is Some
            } by {
                assert(post.cached_branches[i].wf());
                assert(post.cached_branches[i].sealed);
                assert(post.cached_branches[i].root is Some);
            }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].wf() by {
            assert(post.cached_branches[i].wf());
        }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].sealed by {
            assert(post.cached_branches[i].wf());
            assert(post.cached_branches[i].sealed);
        }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].root is Some by {
            assert(post.cached_branches[i].wf());
            assert(post.cached_branches[i].root is Some);
        }
        assert(post.active_cached_branch().wf());
        assert(!post.active_cached_branch().sealed);
        assert(post.active_cached_branch().valid_allocator(post.mini_allocator));
        assert(post.active_branch_pages_in_allocator());
        assert(map_with_disjoint_values(post.branch_summary));
        assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus()));
        assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary)));
        assert(post.mini_allocator.wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.outstanding_reqs_consistent());
        assert(post.cache_agrees_with_disk());
        post.wf_from_parts();
    }

    #[inductive(cache_disk_ops)]
    fn cache_disk_ops_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_cache: Cache::State,
        new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    ) {
        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        crate::implementation::Cache_v::State::inv_next(pre.cache, new_cache, cache_lbl);
        let disk_lbl = AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        crate::spec::AsyncDisk_t::inv_next(pre.disk, new_disk, disk_lbl);
        Self::available_branch_nodes_equal_if_raw_pages_equal(pre, post);
        assert forall |i: int|
            0 <= i < post.cached_branches.len()
            implies #[trigger] post.overlay_branch_at(i as nat) == pre.overlay_branch_at(i as nat) by {
            Self::overlay_at_same_available_branch_nodes(pre, post, i as nat);
        }
        assert(post.sealed_disk_i() == pre.sealed_disk_i());
        assert(post.sealed_roots_i() =~= pre.sealed_roots_i());
        Self::overlay_at_same_available_branch_nodes(pre, post, pre.active_idx() as nat);
        assert(post.active_idx() == pre.active_idx());
        assert(post.overlay_branch_entries() == pre.overlay_branch_entries());
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step| AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
        match disk_step {
            AsyncDisk::Step::disk_ops() => {
                assert(post.disk.requests == pre.disk.requests.union_prefer_right(disk_requests));
                assert(post.disk.responses == pre.disk.responses.remove_keys(disk_responses.dom()));
                assert(post.disk.content == pre.disk.content);
            }
            _ => {
                assert(false);
            }
        }
        assert(post.outstanding_cache_reqs == pre.next_outstanding_cache_reqs(disk_requests, disk_responses));
        assert_sets_equal!(post.disk.requests.dom() + post.disk.responses.dom(), post.outstanding_cache_reqs.dom());
        let old_outstanding = pre.outstanding_cache_reqs.remove_keys(disk_responses.dom());
        let request_addr_map = Map::new(
            |id: ID| disk_requests.contains_key(id),
            |id: ID| disk_requests[id].addr(),
        );
        assert(request_addr_map.is_injective());
        assert(request_addr_map.values().disjoint(pre.outstanding_cache_reqs.values()));
        assert(post.outstanding_cache_reqs == old_outstanding.union_prefer_right(request_addr_map));
        assert(post.outstanding_cache_reqs.is_injective()) by {
            assert forall |x: ID, y: ID|
                x != y
                && post.outstanding_cache_reqs.contains_key(x)
                && post.outstanding_cache_reqs.contains_key(y)
                implies #[trigger] post.outstanding_cache_reqs[x] != #[trigger] post.outstanding_cache_reqs[y] by {
                if request_addr_map.contains_key(x) {
                    assert(post.outstanding_cache_reqs[x] == request_addr_map[x]);
                    assert(request_addr_map.values().contains(request_addr_map[x]));
                    if request_addr_map.contains_key(y) {
                        assert(post.outstanding_cache_reqs[y] == request_addr_map[y]);
                        assert(request_addr_map[x] != request_addr_map[y]);
                    } else {
                        assert(old_outstanding.contains_key(y));
                        assert(post.outstanding_cache_reqs[y] == old_outstanding[y]);
                        assert(pre.outstanding_cache_reqs.contains_key(y));
                        assert(old_outstanding[y] == pre.outstanding_cache_reqs[y]);
                        assert(pre.outstanding_cache_reqs.values().contains(pre.outstanding_cache_reqs[y]));
                    }
                } else {
                    assert(old_outstanding.contains_key(x));
                    assert(post.outstanding_cache_reqs[x] == old_outstanding[x]);
                    assert(pre.outstanding_cache_reqs.contains_key(x));
                    assert(old_outstanding[x] == pre.outstanding_cache_reqs[x]);
                    assert(pre.outstanding_cache_reqs.values().contains(pre.outstanding_cache_reqs[x]));
                    if request_addr_map.contains_key(y) {
                        assert(post.outstanding_cache_reqs[y] == request_addr_map[y]);
                        assert(request_addr_map.values().contains(request_addr_map[y]));
                    } else {
                        assert(old_outstanding.contains_key(y));
                        assert(post.outstanding_cache_reqs[y] == old_outstanding[y]);
                        assert(pre.outstanding_cache_reqs.contains_key(y));
                        assert(old_outstanding[y] == pre.outstanding_cache_reqs[y]);
                        assert(pre.outstanding_cache_reqs[x] != pre.outstanding_cache_reqs[y]);
                    }
                }
            }
        }
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        assert(post.outstanding_reqs_requests_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
                implies {
                    let req = post.disk.requests[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& req.addr() == addr
                    &&& req is ReadReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& req is WriteReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                if disk_requests.contains_key(id) {
                    let req = disk_requests[id];
                    let addr = req.addr();
                    assert(post.disk.requests[id] == req);
                    assert(request_addr_map.contains_key(id));
                    assert(post.outstanding_cache_reqs[id] == request_addr_map[id]);
                    assert(post.outstanding_cache_reqs[id] == addr);
                    assert(cache_requests.contains(req));
                    match cache_step {
                        Cache::Step::load_initiate(new_slots_mapping) => {
                            assert(req is ReadReq);
                            assert(crate::implementation::Cache_v::addr_maps_to_req(
                                cache_requests,
                                req,
                                addr,
                            ));
                            assert(Cache::State::valid_load_requests(cache_requests, new_slots_mapping));
                            assert(new_slots_mapping.contains_value(addr));
                            Cache::State::invert_contains_pair(new_slots_mapping, addr);
                            let slot = choose |slot: Slot|
                                new_slots_mapping.contains_key(slot)
                                && #[trigger] new_slots_mapping[slot] == addr;
                            assert(new_slots_mapping.invert().contains_pair(addr, slot));
                            assert(new_slots_mapping.invert()[addr] == slot);
                            assert(post.cache.lookup_map.contains_key(addr));
                            assert(post.cache.lookup_map[addr] == slot);
                            let updated_entries = Map::new(
                                |slot| new_slots_mapping.contains_key(slot),
                                |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                            );
                            assert(updated_entries.contains_key(slot));
                            assert(updated_entries[slot] == Entry::Loading{addr});
                            assert(post.cache.entries[slot] == Entry::Loading{addr});
                        }
                        Cache::Step::writeback_initiate() => {
                            assert(req is WriteReq);
                            assert(pre.cache.valid_writeback_requests(cache_requests));
                            assert(pre.cache.lookup_map.contains_key(addr));
                            let slot = pre.cache.lookup_map[addr];
                            assert(pre.cache.entries[slot] == Entry::Filled{addr, data: req->data});
                            let writeback_slots = Map::new(
                                |req: DiskRequest| cache_requests.contains(req),
                                |req: DiskRequest| pre.cache.lookup_map[req->to],
                            ).values();
                            assert(cache_requests.contains(req));
                            assert(Map::new(
                                |req: DiskRequest| cache_requests.contains(req),
                                |req: DiskRequest| pre.cache.lookup_map[req->to],
                            ).contains_key(req));
                            assert(Map::new(
                                |req: DiskRequest| cache_requests.contains(req),
                                |req: DiskRequest| pre.cache.lookup_map[req->to],
                            )[req] == slot);
                            assert(writeback_slots.contains(slot));
                            assert(post.cache.lookup_map == pre.cache.lookup_map);
                            assert(post.cache.entries == pre.cache.entries);
                            assert(post.cache.status_map[slot] is Writeback);
                        }
                        _ => {
                            assert(false);
                        }
                    }
                } else {
                    assert(old_outstanding.contains_key(id));
                    assert(pre.outstanding_cache_reqs.contains_key(id));
                    assert(!disk_responses.contains_key(id));
                    assert(pre.disk.requests.contains_key(id));
                    assert(post.disk.requests[id] == pre.disk.requests[id]);
                    let req = pre.disk.requests[id];
                    let addr = pre.outstanding_cache_reqs[id];
                    assert(pre.outstanding_cache_reqs[id] == old_outstanding[id]);
                    assert(post.outstanding_cache_reqs[id] == old_outstanding[id]);
                    cache_response_absent_for_unresponded_outstanding(
                        pre,
                        cache_responses,
                        disk_responses,
                        id,
                    );
                    cache_disk_ops_preserves_pending_slot(
                        pre.cache,
                        post.cache,
                        cache_requests,
                        cache_responses,
                        addr,
                    );
                }
            }
        }
        assert(post.outstanding_reqs_responses_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id)
                implies {
                    let resp = post.disk.responses[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& resp is ReadResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& resp->data == post.disk.content[addr]
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& resp is WriteResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: post.disk.content[addr]}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                assert(pre.disk.responses.contains_key(id));
                assert(!disk_responses.contains_key(id));
                assert(old_outstanding.contains_key(id));
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(post.disk.responses[id] == pre.disk.responses[id]);
                assert(post.disk.content == pre.disk.content);
                let resp = pre.disk.responses[id];
                let addr = pre.outstanding_cache_reqs[id];
                assert(pre.outstanding_cache_reqs[id] == old_outstanding[id]);
                assert(post.outstanding_cache_reqs[id] == old_outstanding[id]);
                cache_response_absent_for_unresponded_outstanding(
                    pre,
                    cache_responses,
                    disk_responses,
                    id,
                );
                cache_disk_ops_preserves_pending_slot(
                    pre.cache,
                    post.cache,
                    cache_requests,
                    cache_responses,
                    addr,
                );
            }
        }
        assert forall |id: ID|
            (#[trigger] post.disk.requests.contains_key(id) || #[trigger] post.disk.responses.contains_key(id))
            implies post.io_id_valid(id) by {
            if disk_requests.contains_key(id) {
                let req = disk_requests[id];
                let addr = req.addr();
                assert(request_addr_map.contains_key(id));
                assert(post.outstanding_cache_reqs[id] == addr);
                assert(cache_requests.contains(req));
                match cache_step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(req is ReadReq);
                        assert(crate::implementation::Cache_v::addr_maps_to_req(
                            cache_requests,
                            req,
                            addr,
                        ));
                        assert(Cache::State::valid_load_requests(cache_requests, new_slots_mapping));
                        assert(new_slots_mapping.contains_value(addr));
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        let slot = choose |slot: Slot|
                            new_slots_mapping.contains_key(slot)
                            && #[trigger] new_slots_mapping[slot] == addr;
                        assert(new_slots_mapping.invert().contains_pair(addr, slot));
                        assert(new_slots_mapping.invert()[addr] == slot);
                        assert(post.cache.lookup_map.contains_key(addr));
                        assert(post.cache.lookup_map[addr] == slot);
                        let updated_entries = Map::new(
                            |slot| new_slots_mapping.contains_key(slot),
                            |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                        );
                        assert(updated_entries.contains_key(slot));
                        assert(updated_entries[slot] == Entry::Loading{addr});
                        assert(post.cache.entries[slot] == Entry::Loading{addr});
                        assert(post.cache.entries.contains_key(slot));
                        assert(post.cache.inv());
                        assert(post.cache.status_map.dom() =~= post.cache.entries.dom());
                        assert(post.cache.status_map.contains_key(slot));
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                    Cache::Step::writeback_initiate() => {
                        assert(req is WriteReq);
                        assert(pre.cache.valid_writeback_requests(cache_requests));
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                        assert(post.cache.entries == pre.cache.entries);
                        assert(pre.cache.lookup_map.contains_key(addr));
                        let slot = pre.cache.lookup_map[addr];
                        cache_lookup_gets_addr(pre.cache, addr);
                        assert(pre.cache.entries.contains_key(slot));
                        assert(post.cache.entries.contains_key(slot));
                        assert(post.cache.inv());
                        assert(post.cache.status_map.dom() =~= post.cache.entries.dom());
                        assert(post.cache.status_map.contains_key(slot));
                    }
                    _ => {
                        assert(false);
                    }
                }
            } else {
                assert(old_outstanding.contains_key(id));
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(!disk_responses.contains_key(id));
                let addr = pre.outstanding_cache_reqs[id];
                cache_response_absent_for_unresponded_outstanding(
                    pre,
                    cache_responses,
                    disk_responses,
                    id,
                );
                cache_disk_ops_preserves_pending_slot(
                    pre.cache,
                    post.cache,
                    cache_requests,
                    cache_responses,
                    addr,
                );
                assert(post.outstanding_cache_reqs[id] == addr);
                assert(pre.io_id_valid(id));
                if post.disk.requests.contains_key(id) {
                    assert(pre.disk.requests.contains_key(id));
                    let req = pre.disk.requests[id];
                    if req is ReadReq {
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                } else {
                    assert(post.disk.responses.contains_key(id));
                    assert(pre.disk.responses.contains_key(id));
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                }
            }
        }
        assert(post.outstanding_reqs_consistent());
        assert(post.cache_agrees_with_disk());
        assert(post.cached_branches.len() > 0);
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies {
                &&& #[trigger] post.cached_branches[i].wf()
                &&& post.cached_branches[i].sealed
                &&& post.cached_branches[i].root is Some
            } by {
                assert(post.cached_branches[i].wf());
                assert(post.cached_branches[i].sealed);
                assert(post.cached_branches[i].root is Some);
            }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].wf() by {
            assert(post.cached_branches[i].wf());
        }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].sealed by {
            assert(post.cached_branches[i].wf());
            assert(post.cached_branches[i].sealed);
        }
        assert forall |i: int|
            0 <= i < post.cached_branches.len() - 1
            implies #[trigger] post.cached_branches[i].root is Some by {
            assert(post.cached_branches[i].wf());
            assert(post.cached_branches[i].root is Some);
        }
        assert(post.active_cached_branch().wf());
        assert(!post.active_cached_branch().sealed);
        assert(post.active_cached_branch().valid_allocator(post.mini_allocator));
        assert(post.active_branch_pages_in_allocator());
        assert(map_with_disjoint_values(post.branch_summary));
        assert(summary_aus(post.branch_summary).disjoint(post.mini_allocator.all_aus()));
        assert(addrs_closed(post.sealed_disk_i().entries.dom(), summary_aus(post.branch_summary)));
        assert(post.mini_allocator.wf());
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.outstanding_reqs_consistent());
        assert(post.cache_agrees_with_disk());
        post.wf_from_parts();
    }
}}

pub open spec fn concrete_branch_init_wf(
    cached_branches: Seq<CachedBranch>,
    seq_end: nat,
    init_aus: Set<AU>,
    cache: Cache::State,
    disk: AsyncDisk::State,
) -> bool
{
    ConcreteBranch::State{
        cached_branches: cached_branches.push(CachedBranch::empty_active()),
        branch_summary: init_branch_summary(cached_branches, disk),
        seq_end,
        mini_allocator: init_mini_allocator(init_aus),
        cache,
        disk,
        outstanding_cache_reqs: Map::empty(),
    }.wf()
}

impl ConcreteBranch::State {
    pub open spec fn active_idx(self) -> int
        recommends self.cached_branches.len() > 0
    {
        self.cached_branches.len() - 1
    }

    pub open spec fn active_cached_branch(self) -> CachedBranch
        recommends self.cached_branches.len() > 0
    {
        self.cached_branches[self.active_idx()]
    }

    pub open spec fn historical_len(self) -> nat
    {
        if self.cached_branches.len() == 0 {
            0
        } else {
            (self.cached_branches.len() - 1) as nat
        }
    }

    pub open spec fn sealed_roots_i(self) -> Seq<Address>
    {
        Seq::new(self.historical_len() as nat, |i: int| {
            if self.cached_branches[i].root is Some {
                self.cached_branches[i].root.unwrap()
            } else {
                Address{au: 0, page: 0}
            }
        })
    }

    pub open spec fn cache_access_label(
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) -> Cache::Label
    {
        Cache::Label::Access{reads, writes}
    }

    pub open spec fn has_cached_page(self, addr: Address) -> bool
    {
        Self::has_cached_page_in(self.cache, addr)
    }

    pub open spec fn has_cached_page_in(cache: Cache::State, addr: Address) -> bool
    {
        &&& cache.lookup_map.contains_key(addr)
        &&& cache.entries[cache.lookup_map[addr]] is Filled
    }

    pub open spec fn cache_raw_page(self, addr: Address) -> RawPage
        recommends self.has_cached_page(addr)
    {
        Self::cache_raw_page_in(self.cache, addr)
    }

    pub open spec fn cache_raw_page_in(cache: Cache::State, addr: Address) -> RawPage
        recommends Self::has_cached_page_in(cache, addr)
    {
        cache.entries[cache.lookup_map[addr]]->data
    }

    pub open spec fn available_raw_pages(self) -> Map<Address, RawPage>
    {
        Self::available_raw_pages_from(self.cache, self.disk)
    }

    pub open spec fn available_raw_pages_from(cache: Cache::State, disk: AsyncDisk::State) -> Map<Address, RawPage>
    {
        Map::new(
            |addr: Address| Self::has_cached_page_in(cache, addr) || disk.content.contains_key(addr),
            |addr: Address| if Self::has_cached_page_in(cache, addr) { Self::cache_raw_page_in(cache, addr) } else { disk.content[addr] },
        )
    }

    pub open spec fn available_branch_nodes(self) -> Map<Address, AllocationBranchNode>
    {
        to_branch_nodes(self.available_raw_pages())
    }

    pub open spec fn aus_have_no_available_branch_nodes_from(
        cache: Cache::State,
        disk: AsyncDisk::State,
        aus: Set<AU>,
    ) -> bool
    {
        forall |addr: Address|
            aus.contains(addr.au)
            ==> !#[trigger] to_branch_nodes(Self::available_raw_pages_from(cache, disk)).contains_key(addr)
    }

    pub open spec fn aus_have_no_available_branch_nodes(self, aus: Set<AU>) -> bool
    {
        Self::aus_have_no_available_branch_nodes_from(self.cache, self.disk, aus)
    }

    pub open spec fn sealed_disk_i(self) -> BufferDisk<AllocationBranchNode>
    {
        let nodes = self.available_branch_nodes();
        let sealed_domain = restrict_domain_au(nodes, summary_aus(self.branch_summary));
        BufferDisk{ entries: nodes.restrict(sealed_domain) }
    }

    pub open spec fn follow_aux_ptr_at(self, branch_idx: nat, addr: Address, node: AllocationBranchNode) -> bool
        recommends branch_idx < self.cached_branches.len()
    {
        &&& self.cached_branches[branch_idx as int].sealed
        &&& self.cached_branches[branch_idx as int].root is Some
        &&& addr == self.cached_branches[branch_idx as int].root.unwrap()
        &&& node is Index
        &&& node->aux_ptr is Some
    }

    pub open spec(checked) fn reachable_branch_addrs_from_with_fuel_contains(self, branch_idx: nat, addr: Address, fuel: nat, a: Address) -> bool
        recommends branch_idx < self.cached_branches.len()
        decreases fuel, 1nat
    {
        if fuel == 0 || !self.available_branch_nodes().contains_key(addr) {
            false
        } else {
            let node = self.available_branch_nodes()[addr];
            if node is Leaf || node is Auxiliary {
                a == addr
            } else {
                ||| a == addr
                ||| self.follow_aux_ptr_at(branch_idx, addr, node)
                    && self.reachable_branch_addrs_from_with_fuel_contains(branch_idx, node->aux_ptr.unwrap(), (fuel - 1) as nat, a)
                ||| exists |i: int|
                    0 <= i < node->children.len()
                    && self.reachable_branch_addrs_from_with_fuel_contains(branch_idx, node->children[i], (fuel - 1) as nat, a)
            }
        }
    }

    pub open spec(checked) fn reachable_branch_addrs_from_with_fuel(self, branch_idx: nat, addr: Address, fuel: nat) -> Set<Address>
        recommends branch_idx < self.cached_branches.len()
        decreases fuel, 2nat
    {
        Set::new(|a: Address| self.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a))
    }

    pub open spec fn active_branch_addrs(self) -> Set<Address>
        recommends self.cached_branches.len() > 0
    {
        Set::new(|addr: Address|
            self.mini_allocator.page_is_reserved(addr)
            && self.available_branch_nodes().contains_key(addr)
        )
    }

    pub open spec fn active_branch_entries(self) -> Map<Address, AllocationBranchNode>
        recommends self.cached_branches.len() > 0
    {
        self.available_branch_nodes().restrict(self.active_branch_addrs())
    }

    pub open spec fn overlay_branch_addrs_at(self, branch_idx: nat) -> Set<Address>
        recommends branch_idx < self.cached_branches.len()
    {
        if self.cached_branches[branch_idx as int].root is Some {
            self.reachable_branch_addrs_from_with_fuel(
                branch_idx,
                self.cached_branches[branch_idx as int].root.unwrap(),
                self.available_branch_nodes().dom().len(),
            )
        } else {
            Set::<Address>::empty()
        }
    }

    pub open spec fn has_overlay_page_at(self, branch_idx: nat, addr: Address) -> bool
        recommends branch_idx < self.cached_branches.len()
    {
        self.overlay_branch_addrs_at(branch_idx).contains(addr)
    }

    pub open spec fn overlay_raw_page_at(self, branch_idx: nat, addr: Address) -> RawPage
        recommends branch_idx < self.cached_branches.len(), self.has_overlay_page_at(branch_idx, addr)
    {
        if self.has_cached_page(addr) {
            self.cache_raw_page(addr)
        } else {
            self.disk.content[addr]
        }
    }

    pub open spec fn overlay_branch_entries_at(self, branch_idx: nat) -> Map<Address, AllocationBranchNode>
        recommends branch_idx < self.cached_branches.len()
    {
        to_branch_nodes(Map::new(
            |addr: Address| self.has_overlay_page_at(branch_idx, addr),
            |addr: Address| self.overlay_raw_page_at(branch_idx, addr),
        ))
    }

    pub open spec fn overlay_branch_at(self, branch_idx: nat) -> Option<LinkedBranch<Summary>>
        recommends branch_idx < self.cached_branches.len()
    {
        match self.cached_branches[branch_idx as int].root {
            Some(root) => Some(LinkedBranch {
                root,
                disk_view: crate::betree::LinkedBranch_v::DiskView { entries: self.overlay_branch_entries_at(branch_idx) },
            }),
            None => None,
        }
    }

    pub open spec fn has_overlay_page(self, addr: Address) -> bool
        recommends self.cached_branches.len() > 0
    {
        self.active_branch_addrs().contains(addr)
    }

    pub open spec fn overlay_branch_entries(self) -> Map<Address, AllocationBranchNode>
        recommends self.cached_branches.len() > 0
    {
        self.active_branch_entries()
    }

    pub open spec fn overlay_branch(self) -> Option<LinkedBranch<Summary>>
        recommends self.cached_branches.len() > 0
    {
        match self.active_cached_branch().root {
            Some(root) => Some(LinkedBranch {
                root,
                disk_view: crate::betree::LinkedBranch_v::DiskView { entries: self.active_branch_entries() },
            }),
            None => None,
        }
    }

    pub open spec fn active_managed_reads_agree(
        self,
        needed: Set<Address>,
        read_nodes: Map<Address, AllocationBranchNode>,
    ) -> bool
        recommends self.cached_branches.len() > 0
    {
        &&& needed <= read_nodes.dom()
        &&& needed <= self.available_branch_nodes().dom()
        &&& needed <= self.overlay_branch_entries().dom()
        &&& forall |addr: Address|
            #[trigger] needed.contains(addr)
            ==> self.mini_allocator.all_aus().contains(addr.au)
        &&& forall |addr: Address|
            #[trigger] needed.contains(addr)
            ==> read_nodes[addr] == self.available_branch_nodes()[addr]
        &&& forall |addr: Address|
            #[trigger] needed.contains(addr)
            ==> read_nodes[addr] == self.overlay_branch_entries()[addr]
    }

    pub open spec fn active_branch_pages_in_allocator(self) -> bool
        recommends self.cached_branches.len() > 0
    {
        forall |addr: Address|
            #[trigger] self.overlay_branch_entries().contains_key(addr)
            ==> self.mini_allocator.all_aus().contains(addr.au)
    }

    pub open spec fn active_branch_pages_reserved_in_allocator(self) -> bool
        recommends self.cached_branches.len() > 0
    {
        forall |addr: Address|
            #[trigger] self.overlay_branch_entries().contains_key(addr)
            ==> self.mini_allocator.page_is_reserved(addr)
    }

    pub open spec fn active_allocator_aus_have_only_reserved_branch_nodes(self) -> bool
        recommends self.cached_branches.len() > 0
    {
        forall |addr: Address|
            self.mini_allocator.all_aus().contains(addr.au)
            && #[trigger] self.available_branch_nodes().contains_key(addr)
            ==> self.mini_allocator.page_is_reserved(addr)
    }

    pub open spec fn branch_summary_keys_in_values(self) -> bool
    {
        forall |au: AU| #[trigger] self.branch_summary.contains_key(au)
            ==> self.branch_summary[au].contains(au)
    }

    pub open spec fn fresh_aus_for_active(self, aus: Set<AU>) -> bool
        recommends self.cached_branches.len() > 0
    {
        &&& aus.disjoint(self.mini_allocator.all_aus())
        &&& self.aus_have_no_available_branch_nodes(aus)
        &&& forall |i: int|
            0 <= i < self.cached_branches.len() - 1
            ==> #[trigger] self.fresh_aus_disjoint_from_sealed_branch_at(aus, i as nat)
    }

    pub open spec fn fresh_aus_disjoint_from_sealed_branch_at(self, aus: Set<AU>, i: nat) -> bool
        recommends
            self.cached_branches.len() > 0,
            i < self.cached_branches.len() - 1,
    {
        let branch = self.overlay_branch_at(i);
        &&& branch is Some
        &&& aus.disjoint(branch.unwrap().get_summary())
    }

    pub open spec fn cache_agrees_with_disk(self) -> bool
    {
        self.active_cached_branch().sealed ==> (
            forall |addr: Address|
                #![trigger self.has_cached_page(addr)]
                self.has_cached_page(addr)
                ==> {
                    &&& self.disk.content.contains_key(addr)
                    &&& self.cache_raw_page(addr) == #[trigger] self.disk.content[addr]
                }
        )
    }

    pub open spec fn io_id_valid(self, id: ID) -> bool
    {
        &&& self.outstanding_cache_reqs.contains_key(id)
        &&& {
            let addr = self.outstanding_cache_reqs[id];
            &&& self.cache.lookup_map.contains_key(addr)
            &&& self.cache.entries.contains_key(self.cache.lookup_map[addr])
            &&& self.cache.status_map.contains_key(self.cache.lookup_map[addr])
            &&& (self.disk.requests.contains_key(id) && self.disk.requests[id] is ReadReq ==> self.disk.content.contains_key(addr))
            &&& (self.disk.responses.contains_key(id) ==> self.disk.content.contains_key(addr))
        }
    }

    pub open spec fn outstanding_reqs_requests_ok(self) -> bool
    {
        forall |id: ID| #[trigger] self.disk.requests.contains_key(id)
            ==> {
                let req = self.disk.requests[id];
                let addr = self.outstanding_cache_reqs[id];
                &&& self.outstanding_cache_reqs.contains_key(id)
                &&& req.addr() == addr
                &&& req is ReadReq ==> {
                    let slot = self.cache.lookup_map[addr];
                    &&& self.cache.entries[slot] is Loading
                }
                &&& req is WriteReq ==> {
                    let slot = self.cache.lookup_map[addr];
                    &&& self.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                    &&& self.cache.status_map[slot] is Writeback
                }
            }
    }

    pub open spec fn outstanding_reqs_responses_ok(self) -> bool
    {
        forall |id: ID| #[trigger] self.disk.responses.contains_key(id)
            ==> {
                let resp = self.disk.responses[id];
                let addr = self.outstanding_cache_reqs[id];
                &&& self.outstanding_cache_reqs.contains_key(id)
                &&& resp is ReadResp ==> {
                    let slot = self.cache.lookup_map[addr];
                    &&& resp->data == self.disk.content[addr]
                    &&& self.cache.entries[slot] is Loading
                }
                &&& resp is WriteResp ==> {
                    let slot = self.cache.lookup_map[addr];
                    &&& self.cache.entries[slot] == Entry::Filled{addr, data: self.disk.content[addr]}
                    &&& self.cache.status_map[slot] is Writeback
                }
            }
    }

    pub open spec fn outstanding_reqs_consistent(self) -> bool
    {
        &&& self.outstanding_cache_reqs.is_injective()
        &&& self.disk.requests.dom() + self.disk.responses.dom() == self.outstanding_cache_reqs.dom()
        &&& self.outstanding_reqs_requests_ok()
        &&& self.outstanding_reqs_responses_ok()
        &&& forall |id: ID|
            #![trigger self.disk.requests.contains_key(id)]
            #![trigger self.disk.responses.contains_key(id)]
            (self.disk.requests.contains_key(id) || self.disk.responses.contains_key(id))
            ==> self.io_id_valid(id)
    }

    pub open spec fn disk_requests_match_cache_requests(
        self,
        cache_requests: Set<DiskRequest>,
        disk_requests: Map<ID, DiskRequest>,
    ) -> bool
    {
        &&& disk_requests.is_injective()
        &&& disk_requests.values() =~= cache_requests
        &&& disk_requests.dom().disjoint(self.outstanding_cache_reqs.dom())
        &&& {
            let request_addr_map =
                Map::new(|id: ID| disk_requests.contains_key(id), |id: ID| disk_requests[id].addr());
            &&& request_addr_map.is_injective()
            &&& request_addr_map.values().disjoint(self.outstanding_cache_reqs.values())
            &&& forall |id: ID| #[trigger] disk_requests.contains_key(id)
                ==> (disk_requests[id] is ReadReq ==> self.disk.content.contains_key(disk_requests[id]->from))
        }
    }

    pub open spec fn disk_responses_match_cache_responses(
        self,
        cache_responses: Map<Address, DiskResponse>,
        disk_responses: Map<ID, DiskResponse>,
    ) -> bool
    {
        &&& disk_responses.dom() <= self.outstanding_cache_reqs.dom()
        &&& cache_responses.dom() =~= self.outstanding_cache_reqs.restrict(disk_responses.dom()).values()
        &&& forall |id: ID| #[trigger] disk_responses.contains_key(id) ==> {
            let addr = self.outstanding_cache_reqs[id];
            &&& cache_responses.contains_key(addr)
            &&& cache_responses[addr] == disk_responses[id]
        }
    }

    pub open spec fn next_outstanding_cache_reqs(
        self,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    ) -> Map<ID, Address>
    {
        self.outstanding_cache_reqs.remove_keys(disk_responses.dom()).union_prefer_right(
            Map::new(
                |id: ID| disk_requests.contains_key(id),
                |id: ID| disk_requests[id].addr(),
            ),
        )
    }

    pub open spec fn branch_query_matches(
        self,
        branch_idx: nat,
        key: Key,
        msg: Message,
        receipt: Option<LoadedPathReceipt>,
        read_nodes: Map<Address, AllocationBranchNode>,
    ) -> bool
        recommends branch_idx < self.cached_branches.len()
    {
        let branch = self.cached_branches[branch_idx as int];
        if branch.root is Some {
            &&& receipt is Some
            &&& receipt.unwrap().key == key
            &&& branch.can_query(self.mini_allocator, receipt.unwrap(), read_nodes)
            &&& branch.query_result(receipt.unwrap(), read_nodes) == msg
        } else {
            &&& branch.is_empty_active()
            &&& receipt is None
            &&& msg == Message::Update{delta: nop_delta()}
        }
    }

    pub open spec fn branch_query_returns_nop(
        self,
        branch_idx: nat,
        key: Key,
        receipt: Option<LoadedPathReceipt>,
        read_nodes: Map<Address, AllocationBranchNode>,
    ) -> bool
        recommends branch_idx < self.cached_branches.len()
    {
        self.branch_query_matches(
            branch_idx,
            key,
            Message::Update{delta: nop_delta()},
            receipt,
            read_nodes,
        )
    }

    pub open spec fn query_matches_stack(
        self,
        branch_idx: nat,
        key: Key,
        msg: Message,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
        read_nodes: Map<Address, AllocationBranchNode>,
    ) -> bool
        recommends
            self.cached_branches.len() > 0,
            branch_idx < self.cached_branches.len(),
            query_receipts.len() == self.cached_branches.len(),
    {
        if msg == (Message::Update{delta: nop_delta()}) {
            forall |j: int|
                0 <= j < self.cached_branches.len()
                ==> self.branch_query_returns_nop(
                    j as nat,
                    key,
                    query_receipts[j],
                    read_nodes,
                )
        } else {
            &&& self.branch_query_matches(
                    branch_idx,
                    key,
                    msg,
                    query_receipts[branch_idx as int],
                    read_nodes,
                )
            &&& forall |j: int|
                branch_idx < j < self.cached_branches.len()
                ==> self.branch_query_returns_nop(
                    j as nat,
                    key,
                    query_receipts[j],
                    read_nodes,
                )
        }
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.cached_branches.len() > 0
        &&& forall |i: int|
            0 <= i < self.cached_branches.len() - 1
            ==> {
                &&& #[trigger] self.cached_branches[i].wf()
                &&& self.cached_branches[i].sealed
                &&& self.cached_branches[i].root is Some
            }
        &&& self.active_cached_branch().wf()
        &&& !self.active_cached_branch().sealed
        &&& self.active_cached_branch().valid_allocator(self.mini_allocator)
        &&& self.active_branch_pages_in_allocator()
        &&& self.active_branch_pages_reserved_in_allocator()
        &&& self.active_allocator_aus_have_only_reserved_branch_nodes()
        &&& self.branch_summary.dom().finite()
        &&& self.branch_summary_keys_in_values()
        &&& map_with_disjoint_values(self.branch_summary)
        &&& summary_aus(self.branch_summary).disjoint(self.mini_allocator.all_aus())
        &&& addrs_closed(self.sealed_disk_i().entries.dom(), summary_aus(self.branch_summary))
        &&& self.mini_allocator.wf()
        &&& self.cache.inv()
        &&& self.disk.inv()
        &&& self.outstanding_reqs_consistent()
        &&& self.cache_agrees_with_disk()
    }

    pub proof fn wf_from_parts(self)
        requires
            self.cached_branches.len() > 0,
            forall |i: int|
                0 <= i < self.cached_branches.len() - 1
                ==> #[trigger] self.cached_branches[i].wf(),
            forall |i: int|
                0 <= i < self.cached_branches.len() - 1
                ==> #[trigger] self.cached_branches[i].sealed,
            forall |i: int|
                0 <= i < self.cached_branches.len() - 1
                ==> #[trigger] self.cached_branches[i].root is Some,
            self.active_cached_branch().wf(),
            !self.active_cached_branch().sealed,
            self.active_cached_branch().valid_allocator(self.mini_allocator),
            self.active_branch_pages_in_allocator(),
            self.active_branch_pages_reserved_in_allocator(),
            self.active_allocator_aus_have_only_reserved_branch_nodes(),
            self.branch_summary.dom().finite(),
            self.branch_summary_keys_in_values(),
            map_with_disjoint_values(self.branch_summary),
            summary_aus(self.branch_summary).disjoint(self.mini_allocator.all_aus()),
            addrs_closed(self.sealed_disk_i().entries.dom(), summary_aus(self.branch_summary)),
            self.mini_allocator.wf(),
            self.cache.inv(),
            self.disk.inv(),
            self.outstanding_reqs_consistent(),
            self.cache_agrees_with_disk(),
        ensures
            self.wf(),
    {
        assert forall |i: int|
            0 <= i < self.cached_branches.len() - 1
            implies {
                &&& #[trigger] self.cached_branches[i].wf()
                &&& self.cached_branches[i].sealed
                &&& self.cached_branches[i].root is Some
            } by {
            assert(self.cached_branches[i].wf());
            assert(self.cached_branches[i].sealed);
            assert(self.cached_branches[i].root is Some);
        }
    }

    pub proof fn available_branch_nodes_ignore_mini_allocator(pre: Self, post: Self)
        requires
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.cache == post.cache,
            pre.disk == post.disk,
        ensures
            pre.available_raw_pages() == post.available_raw_pages(),
            pre.available_branch_nodes() == post.available_branch_nodes(),
    {
        let pre_raw = pre.available_raw_pages();
        let post_raw = post.available_raw_pages();
        assert forall |addr: Address| #[trigger] pre_raw.contains_key(addr) <==> post_raw.contains_key(addr) by { };
        assert forall |addr: Address| #[trigger] pre_raw.contains_key(addr) implies pre_raw[addr] == post_raw[addr] by { };
        assert_maps_equal!(pre_raw, post_raw);

        let pre_nodes = pre.available_branch_nodes();
        let post_nodes = post.available_branch_nodes();
        assert forall |addr: Address| #[trigger] pre_nodes.contains_key(addr) <==> post_nodes.contains_key(addr) by { };
        assert forall |addr: Address| #[trigger] pre_nodes.contains_key(addr) implies pre_nodes[addr] == post_nodes[addr] by { };
        assert_maps_equal!(pre_nodes, post_nodes);
    }

    pub proof fn reachable_branch_addrs_contains_ignore_mini_allocator(
        pre: Self,
        post: Self,
        branch_idx: nat,
        addr: Address,
        fuel: nat,
        a: Address,
    )
        requires
            branch_idx < pre.cached_branches.len(),
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.cache == post.cache,
            pre.disk == post.disk,
        ensures
            pre.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a)
                == post.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a),
        decreases fuel,
    {
        Self::available_branch_nodes_ignore_mini_allocator(pre, post);
        let pre_nodes = pre.available_branch_nodes();
        let post_nodes = post.available_branch_nodes();

        if fuel == 0 {
        } else {
            assert(pre_nodes.contains_key(addr) == post_nodes.contains_key(addr));
            if pre_nodes.contains_key(addr) {
                assert(pre_nodes[addr] == post_nodes[addr]);
                let node = pre_nodes[addr];
                assert(pre.follow_aux_ptr_at(branch_idx, addr, node) == post.follow_aux_ptr_at(branch_idx, addr, node));
                if !(node is Leaf) && !(node is Auxiliary) {
                    if pre.follow_aux_ptr_at(branch_idx, addr, node) {
                        Self::reachable_branch_addrs_contains_ignore_mini_allocator(
                            pre, post, branch_idx, node->aux_ptr.unwrap(), (fuel - 1) as nat, a,
                        );
                    }
                    assert forall |i: int|
                        0 <= i < node->children.len()
                        implies pre.reachable_branch_addrs_from_with_fuel_contains(
                            branch_idx, node->children[i], (fuel - 1) as nat, a,
                        ) == post.reachable_branch_addrs_from_with_fuel_contains(
                            branch_idx, node->children[i], (fuel - 1) as nat, a,
                        )
                    by {
                        Self::reachable_branch_addrs_contains_ignore_mini_allocator(
                            pre, post, branch_idx, node->children[i], (fuel - 1) as nat, a,
                        );
                    };
                }
            }
        }
    }

    pub proof fn reachable_branch_addr_implies_available_branch_node(
        self,
        branch_idx: nat,
        root: Address,
        fuel: nat,
        addr: Address,
    )
        requires
            branch_idx < self.cached_branches.len(),
            self.reachable_branch_addrs_from_with_fuel_contains(branch_idx, root, fuel, addr),
        ensures
            self.available_branch_nodes().contains_key(addr),
        decreases fuel,
    {
        if fuel == 0 {
            assert(false);
        } else {
            assert(self.available_branch_nodes().contains_key(root));
            let node = self.available_branch_nodes()[root];
            if node is Leaf || node is Auxiliary {
                assert(addr == root);
            } else if addr == root {
            } else if self.follow_aux_ptr_at(branch_idx, root, node)
                && self.reachable_branch_addrs_from_with_fuel_contains(branch_idx, node->aux_ptr.unwrap(), (fuel - 1) as nat, addr) {
                self.reachable_branch_addr_implies_available_branch_node(
                    branch_idx,
                    node->aux_ptr.unwrap(),
                    (fuel - 1) as nat,
                    addr,
                );
            } else {
                let i = choose |i: int|
                    0 <= i < node->children.len()
                    && self.reachable_branch_addrs_from_with_fuel_contains(branch_idx, node->children[i], (fuel - 1) as nat, addr);
                self.reachable_branch_addr_implies_available_branch_node(
                    branch_idx,
                    node->children[i],
                    (fuel - 1) as nat,
                    addr,
                );
            }
        }
    }

    pub proof fn reachable_branch_addrs_more_fuel(
        self,
        branch_idx: nat,
        root: Address,
        fuel: nat,
        addr: Address,
    )
        requires
            branch_idx < self.cached_branches.len(),
            self.reachable_branch_addrs_from_with_fuel_contains(branch_idx, root, fuel, addr),
        ensures
            self.reachable_branch_addrs_from_with_fuel_contains(branch_idx, root, fuel + 1, addr),
        decreases fuel,
    {
        if fuel == 0 {
            assert(false);
        } else if !self.available_branch_nodes().contains_key(root) {
            assert(false);
        } else {
            let node = self.available_branch_nodes()[root];
            if node is Leaf || node is Auxiliary {
            } else if addr == root {
            } else if self.follow_aux_ptr_at(branch_idx, root, node)
                && self.reachable_branch_addrs_from_with_fuel_contains(
                    branch_idx,
                    node->aux_ptr.unwrap(),
                    (fuel - 1) as nat,
                    addr,
                ) {
                self.reachable_branch_addrs_more_fuel(
                    branch_idx,
                    node->aux_ptr.unwrap(),
                    (fuel - 1) as nat,
                    addr,
                );
            } else {
                let i = choose |i: int|
                    0 <= i < node->children.len()
                    && self.reachable_branch_addrs_from_with_fuel_contains(
                        branch_idx,
                        node->children[i],
                        (fuel - 1) as nat,
                        addr,
                    );
                self.reachable_branch_addrs_more_fuel(
                    branch_idx,
                    node->children[i],
                    (fuel - 1) as nat,
                    addr,
                );
            }
        }
    }

    pub proof fn overlay_at_ignores_mini_allocator(pre: Self, post: Self, branch_idx: nat)
        requires
            branch_idx < pre.cached_branches.len(),
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.cache == post.cache,
            pre.disk == post.disk,
        ensures
            pre.available_raw_pages() == post.available_raw_pages(),
            pre.available_branch_nodes() == post.available_branch_nodes(),
            pre.overlay_branch_addrs_at(branch_idx) == post.overlay_branch_addrs_at(branch_idx),
            pre.overlay_branch_entries_at(branch_idx) == post.overlay_branch_entries_at(branch_idx),
            pre.overlay_branch_at(branch_idx) == post.overlay_branch_at(branch_idx),
    {
        Self::available_branch_nodes_ignore_mini_allocator(pre, post);
        if pre.cached_branches[branch_idx as int].root is Some {
            let root = pre.cached_branches[branch_idx as int].root.unwrap();
            assert forall |addr: Address|
                #[trigger] pre.overlay_branch_addrs_at(branch_idx).contains(addr)
                <==> post.overlay_branch_addrs_at(branch_idx).contains(addr)
            by {
                Self::reachable_branch_addrs_contains_ignore_mini_allocator(
                    pre,
                    post,
                    branch_idx,
                    root,
                    pre.available_branch_nodes().dom().len(),
                    addr,
                );
            };
        } else {
            assert(pre.overlay_branch_addrs_at(branch_idx) == Set::<Address>::empty());
            assert(post.overlay_branch_addrs_at(branch_idx) == Set::<Address>::empty());
        }
        assert(pre.overlay_branch_addrs_at(branch_idx) == post.overlay_branch_addrs_at(branch_idx));

        let pre_entries = pre.overlay_branch_entries_at(branch_idx);
        let post_entries = post.overlay_branch_entries_at(branch_idx);
        assert forall |addr: Address| #[trigger] pre_entries.contains_key(addr) <==> post_entries.contains_key(addr) by { };
        assert forall |addr: Address| #[trigger] pre_entries.contains_key(addr) implies pre_entries[addr] == post_entries[addr] by {
            pre.overlay_entry_matches_available(branch_idx, addr);
            post.overlay_entry_matches_available(branch_idx, addr);
            assert(pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr]);
        };
        assert_maps_equal!(pre_entries, post_entries);

        assert(pre.overlay_branch_at(branch_idx) == post.overlay_branch_at(branch_idx));
    }

    pub proof fn available_branch_nodes_equal_if_raw_pages_equal(pre: Self, post: Self)
        requires
            pre.available_raw_pages() == post.available_raw_pages(),
        ensures
            pre.available_branch_nodes() == post.available_branch_nodes(),
    {
        let pre_nodes = pre.available_branch_nodes();
        let post_nodes = post.available_branch_nodes();
        assert forall |addr: Address| #[trigger] pre_nodes.contains_key(addr) <==> post_nodes.contains_key(addr) by { };
        assert forall |addr: Address| #[trigger] pre_nodes.contains_key(addr) implies pre_nodes[addr] == post_nodes[addr] by { };
        assert_maps_equal!(pre_nodes, post_nodes);
    }

    pub proof fn sealed_disk_i_unchanged_by_cache_access(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            pre.cache.inv(),
            Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
            post.disk == pre.disk,
            post.branch_summary == pre.branch_summary,
            forall |addr: Address|
                #[trigger] writes.contains_key(addr)
                ==> !summary_aus(pre.branch_summary).contains(addr.au),
        ensures
            post.sealed_disk_i() == pre.sealed_disk_i(),
    {
        let pre_entries = pre.sealed_disk_i().entries;
        let post_entries = post.sealed_disk_i().entries;
        assert forall |addr: Address| #[trigger] post_entries.contains_key(addr) <==> pre_entries.contains_key(addr) by {
            if summary_aus(pre.branch_summary).contains(addr.au) {
                assert(!writes.contains_key(addr));
                Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
            }
        };
        assert forall |addr: Address| #[trigger] post_entries.contains_key(addr) implies post_entries[addr] == pre_entries[addr] by {
            assert(summary_aus(pre.branch_summary).contains(addr.au));
            assert(!writes.contains_key(addr));
            Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
            if pre.has_cached_page(addr) {
                assert(post.has_cached_page(addr));
                assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
            } else {
                assert(!post.has_cached_page(addr));
                assert(post.disk.content.contains_key(addr) == pre.disk.content.contains_key(addr));
                assert(post.available_raw_pages()[addr] == pre.available_raw_pages()[addr]);
            }
            assert(post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]);
        };
        assert_maps_equal!(post_entries, pre_entries);
        assert(post.sealed_disk_i() == pre.sealed_disk_i());
    }

    pub proof fn cache_access_write_visible_as_branch_node(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        addr: Address,
    )
        requires
            pre.cache.inv(),
            Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
            post.disk == pre.disk,
            writes.contains_key(addr),
        ensures
            post.available_branch_nodes().contains_key(addr),
            post.available_branch_nodes()[addr] == to_branch_nodes(writes)[addr],
    {
        let lbl = Cache::Label::Access{reads, writes};
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(pre.cache, post.cache, lbl, Cache::Step::access()));
        let slot = pre.cache.lookup_map[addr];
        assert(pre.cache.valid_write(addr));
        assert(pre.cache.lookup_map.contains_key(addr));
        let updated_entries = pre.cache.write_updated_entries(writes);
        assert(updated_entries.contains_key(slot)) by {
            let restricted = pre.cache.lookup_map.restrict(writes.dom());
            assert(restricted.contains_key(addr));
            assert(restricted[addr] == slot);
            assert(restricted.values().contains(slot));
        }
        assert(pre.cache.entries[slot].get_addr() == addr);
        assert(post.cache.lookup_map == pre.cache.lookup_map);
        assert(post.cache.entries[slot] == Entry::Filled{addr, data: writes[addr]});
        assert(post.has_cached_page(addr));
        assert(post.cache_raw_page(addr) == writes[addr]);
        assert(post.available_raw_pages().contains_key(addr));
        assert(post.available_raw_pages()[addr] == writes[addr]);
        assert(post.available_branch_nodes().contains_key(addr));
        assert(post.available_branch_nodes()[addr] == to_branch_nodes(writes)[addr]);
    }

    pub proof fn cache_access_preserves_outstanding_reqs_consistent(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            pre.cache.inv(),
            pre.outstanding_reqs_consistent(),
            Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
            post.disk == pre.disk,
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        ensures
            post.outstanding_reqs_consistent(),
    {
        let lbl = Cache::Label::Access{reads, writes};
        crate::implementation::Cache_v::State::inv_next(pre.cache, post.cache, lbl);
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        assert(Cache::State::next_by(pre.cache, post.cache, lbl, Cache::Step::access()));
        assert(post.outstanding_reqs_requests_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
                implies {
                    let req = post.disk.requests[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& req.addr() == addr
                    &&& req is ReadReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& req is WriteReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                let req = pre.disk.requests[id];
                let addr = pre.outstanding_cache_reqs[id];
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(!writes.contains_key(addr)) by {
                    if writes.contains_key(addr) {
                        assert(pre.cache.valid_write(addr));
                        let slot = pre.cache.lookup_map[addr];
                        if req is ReadReq {
                            assert(pre.cache.entries[slot] is Loading);
                            assert(false);
                        } else {
                            assert(req is WriteReq);
                            assert(pre.cache.status_map[slot] is Writeback);
                            assert(false);
                        }
                    }
                }
                Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
            }
        }
        assert(post.outstanding_reqs_responses_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id)
                implies {
                    let resp = post.disk.responses[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& resp is ReadResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& resp->data == post.disk.content[addr]
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& resp is WriteResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: post.disk.content[addr]}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                let resp = pre.disk.responses[id];
                let addr = pre.outstanding_cache_reqs[id];
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(!writes.contains_key(addr)) by {
                    if writes.contains_key(addr) {
                        assert(pre.cache.valid_write(addr));
                        let slot = pre.cache.lookup_map[addr];
                        if resp is ReadResp {
                            assert(pre.cache.entries[slot] is Loading);
                            assert(false);
                        } else {
                            assert(resp is WriteResp);
                            assert(pre.cache.status_map[slot] is Writeback);
                            assert(false);
                        }
                    }
                }
                Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
            }
        }
        assert forall |id: ID|
            (#[trigger] post.disk.requests.contains_key(id) || #[trigger] post.disk.responses.contains_key(id))
            implies post.io_id_valid(id) by {
            let addr = pre.outstanding_cache_reqs[id];
            assert(pre.io_id_valid(id));
            assert(!writes.contains_key(addr)) by {
                if writes.contains_key(addr) {
                    assert(pre.cache.valid_write(addr));
                    let slot = pre.cache.lookup_map[addr];
                    if pre.disk.requests.contains_key(id) {
                        let req = pre.disk.requests[id];
                        if req is ReadReq {
                            assert(pre.cache.entries[slot] is Loading);
                            assert(false);
                        } else {
                            assert(req is WriteReq);
                            assert(pre.cache.status_map[slot] is Writeback);
                            assert(false);
                        }
                    } else {
                        let resp = pre.disk.responses[id];
                        if resp is ReadResp {
                            assert(pre.cache.entries[slot] is Loading);
                            assert(false);
                        } else {
                            assert(resp is WriteResp);
                            assert(pre.cache.status_map[slot] is Writeback);
                            assert(false);
                        }
                    }
                }
            }
            Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
            assert(post.outstanding_cache_reqs.contains_key(id));
            assert(post.cache.lookup_map.contains_key(post.outstanding_cache_reqs[id]));
            cache_lookup_gets_addr(post.cache, post.outstanding_cache_reqs[id]);
            assert(post.cache.entries.contains_key(post.cache.lookup_map[post.outstanding_cache_reqs[id]]));
            assert(post.cache.status_map.contains_key(post.cache.lookup_map[post.outstanding_cache_reqs[id]]));
        }
        assert(post.outstanding_cache_reqs.is_injective());
        assert(post.disk.requests.dom() + post.disk.responses.dom() == post.outstanding_cache_reqs.dom());
        assert(post.outstanding_reqs_consistent());
    }

    pub proof fn reachable_branch_addrs_contains_same_available_nodes(
        pre: Self,
        post: Self,
        branch_idx: nat,
        addr: Address,
        fuel: nat,
        a: Address,
    )
        requires
            branch_idx < pre.cached_branches.len(),
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.available_branch_nodes() == post.available_branch_nodes(),
        ensures
            pre.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a)
                == post.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a),
        decreases fuel,
    {
        let pre_nodes = pre.available_branch_nodes();
        let post_nodes = post.available_branch_nodes();

        if fuel == 0 {
        } else {
            assert(pre_nodes.contains_key(addr) == post_nodes.contains_key(addr));
            if pre_nodes.contains_key(addr) {
                assert(pre_nodes[addr] == post_nodes[addr]);
                let node = pre_nodes[addr];
                assert(pre.follow_aux_ptr_at(branch_idx, addr, node) == post.follow_aux_ptr_at(branch_idx, addr, node));
                if !(node is Leaf) && !(node is Auxiliary) {
                    if pre.follow_aux_ptr_at(branch_idx, addr, node) {
                        Self::reachable_branch_addrs_contains_same_available_nodes(
                            pre, post, branch_idx, node->aux_ptr.unwrap(), (fuel - 1) as nat, a,
                        );
                    }
                    assert forall |i: int|
                        0 <= i < node->children.len()
                        implies pre.reachable_branch_addrs_from_with_fuel_contains(
                            branch_idx, node->children[i], (fuel - 1) as nat, a,
                        ) == post.reachable_branch_addrs_from_with_fuel_contains(
                            branch_idx, node->children[i], (fuel - 1) as nat, a,
                        )
                    by {
                        Self::reachable_branch_addrs_contains_same_available_nodes(
                            pre, post, branch_idx, node->children[i], (fuel - 1) as nat, a,
                        );
                    }
                }
            }
        }
    }

    pub proof fn overlay_at_same_available_branch_nodes(pre: Self, post: Self, branch_idx: nat)
        requires
            branch_idx < pre.cached_branches.len(),
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.available_branch_nodes() == post.available_branch_nodes(),
        ensures
            pre.overlay_branch_addrs_at(branch_idx) == post.overlay_branch_addrs_at(branch_idx),
            pre.overlay_branch_entries_at(branch_idx) == post.overlay_branch_entries_at(branch_idx),
            pre.overlay_branch_at(branch_idx) == post.overlay_branch_at(branch_idx),
    {
        if pre.cached_branches[branch_idx as int].root is Some {
            let root = pre.cached_branches[branch_idx as int].root.unwrap();
            assert forall |addr: Address|
                #[trigger] pre.overlay_branch_addrs_at(branch_idx).contains(addr)
                <==> post.overlay_branch_addrs_at(branch_idx).contains(addr)
            by {
                Self::reachable_branch_addrs_contains_same_available_nodes(
                    pre,
                    post,
                    branch_idx,
                    root,
                    pre.available_branch_nodes().dom().len(),
                    addr,
                );
            };
        } else {
            assert(pre.overlay_branch_addrs_at(branch_idx) == Set::<Address>::empty());
            assert(post.overlay_branch_addrs_at(branch_idx) == Set::<Address>::empty());
        }
        assert(pre.overlay_branch_addrs_at(branch_idx) == post.overlay_branch_addrs_at(branch_idx));

        let pre_entries = pre.overlay_branch_entries_at(branch_idx);
        let post_entries = post.overlay_branch_entries_at(branch_idx);
        assert forall |addr: Address| #[trigger] pre_entries.contains_key(addr) <==> post_entries.contains_key(addr) by { };
        assert forall |addr: Address| #[trigger] pre_entries.contains_key(addr) implies pre_entries[addr] == post_entries[addr] by {
            pre.overlay_entry_matches_available(branch_idx, addr);
            post.overlay_entry_matches_available(branch_idx, addr);
            assert(pre.available_branch_nodes()[addr] == post.available_branch_nodes()[addr]);
        };
        assert_maps_equal!(pre_entries, post_entries);

        assert(pre.overlay_branch_at(branch_idx) == post.overlay_branch_at(branch_idx));
    }

    pub proof fn reachable_branch_addrs_contains_same_after_leaf_update(
        pre: Self,
        post: Self,
        branch_idx: nat,
        addr: Address,
        fuel: nat,
        target: Address,
        a: Address,
    )
        requires
            branch_idx < pre.cached_branches.len(),
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.available_branch_nodes().dom() == post.available_branch_nodes().dom(),
            forall |x: Address|
                x != target && #[trigger] pre.available_branch_nodes().contains_key(x)
                ==> post.available_branch_nodes()[x] == pre.available_branch_nodes()[x],
            pre.available_branch_nodes().contains_key(target),
            post.available_branch_nodes().contains_key(target),
            pre.available_branch_nodes()[target] is Leaf,
            post.available_branch_nodes()[target] is Leaf,
        ensures
            pre.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a)
                == post.reachable_branch_addrs_from_with_fuel_contains(branch_idx, addr, fuel, a),
        decreases fuel,
    {
        let pre_nodes = pre.available_branch_nodes();
        let post_nodes = post.available_branch_nodes();
        if fuel == 0 {
        } else {
            assert(pre_nodes.contains_key(addr) == post_nodes.contains_key(addr));
            if pre_nodes.contains_key(addr) {
                if addr == target {
                    assert(pre_nodes[addr] is Leaf);
                    assert(post_nodes[addr] is Leaf);
                } else {
                    assert(post_nodes[addr] == pre_nodes[addr]);
                    let node = pre_nodes[addr];
                    assert(pre.follow_aux_ptr_at(branch_idx, addr, node)
                        == post.follow_aux_ptr_at(branch_idx, addr, node));
                    if !(node is Leaf) && !(node is Auxiliary) {
                        if pre.follow_aux_ptr_at(branch_idx, addr, node) {
                            Self::reachable_branch_addrs_contains_same_after_leaf_update(
                                pre,
                                post,
                                branch_idx,
                                node->aux_ptr.unwrap(),
                                (fuel - 1) as nat,
                                target,
                                a,
                            );
                        }
                        assert forall |i: int|
                            0 <= i < node->children.len()
                            implies pre.reachable_branch_addrs_from_with_fuel_contains(
                                branch_idx,
                                node->children[i],
                                (fuel - 1) as nat,
                                a,
                            ) == post.reachable_branch_addrs_from_with_fuel_contains(
                                branch_idx,
                                node->children[i],
                                (fuel - 1) as nat,
                                a,
                            )
                        by {
                            Self::reachable_branch_addrs_contains_same_after_leaf_update(
                                pre,
                                post,
                                branch_idx,
                                node->children[i],
                                (fuel - 1) as nat,
                                target,
                                a,
                            );
                        }
                    }
                }
            }
        }
    }

    pub proof fn overlay_addrs_same_after_leaf_update(
        pre: Self,
        post: Self,
        branch_idx: nat,
        target: Address,
    )
        requires
            branch_idx < pre.cached_branches.len(),
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.available_branch_nodes().dom() == post.available_branch_nodes().dom(),
            forall |x: Address|
                x != target && #[trigger] pre.available_branch_nodes().contains_key(x)
                ==> post.available_branch_nodes()[x] == pre.available_branch_nodes()[x],
            pre.available_branch_nodes().contains_key(target),
            post.available_branch_nodes().contains_key(target),
            pre.available_branch_nodes()[target] is Leaf,
            post.available_branch_nodes()[target] is Leaf,
        ensures
            pre.overlay_branch_addrs_at(branch_idx) == post.overlay_branch_addrs_at(branch_idx),
    {
        if pre.cached_branches[branch_idx as int].root is Some {
            let root = pre.cached_branches[branch_idx as int].root.unwrap();
            assert(pre.available_branch_nodes().dom().len() == post.available_branch_nodes().dom().len());
            assert forall |addr: Address|
                #[trigger] pre.overlay_branch_addrs_at(branch_idx).contains(addr)
                <==> post.overlay_branch_addrs_at(branch_idx).contains(addr)
            by {
                Self::reachable_branch_addrs_contains_same_after_leaf_update(
                    pre,
                    post,
                    branch_idx,
                    root,
                    pre.available_branch_nodes().dom().len(),
                    target,
                    addr,
                );
            };
        } else {
            assert(pre.overlay_branch_addrs_at(branch_idx) == Set::<Address>::empty());
            assert(post.overlay_branch_addrs_at(branch_idx) == Set::<Address>::empty());
        }
        assert(pre.overlay_branch_addrs_at(branch_idx) == post.overlay_branch_addrs_at(branch_idx));
    }

    pub proof fn overlay_branch_wf_after_leaf_update(
        pre: Self,
        post: Self,
        branch_idx: nat,
        target: Address,
    )
        requires
            branch_idx < pre.cached_branches.len(),
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.overlay_branch_at(branch_idx) is Some,
            pre.overlay_branch_at(branch_idx).unwrap().wf(),
            pre.available_branch_nodes().dom() == post.available_branch_nodes().dom(),
            forall |x: Address|
                x != target && #[trigger] pre.available_branch_nodes().contains_key(x)
                ==> post.available_branch_nodes()[x] == pre.available_branch_nodes()[x],
            pre.available_branch_nodes().contains_key(target),
            post.available_branch_nodes().contains_key(target),
            pre.available_branch_nodes()[target] is Leaf,
            post.available_branch_nodes()[target] is Leaf,
            post.available_branch_nodes()[target].wf(),
        ensures
            post.overlay_branch_at(branch_idx) is Some,
            post.overlay_branch_at(branch_idx).unwrap().wf(),
    {
        Self::overlay_addrs_same_after_leaf_update(pre, post, branch_idx, target);
        assert(post.overlay_branch_at(branch_idx) is Some);

        let pre_branch = pre.overlay_branch_at(branch_idx).unwrap();
        let post_branch = post.overlay_branch_at(branch_idx).unwrap();
        let pre_entries = pre.overlay_branch_entries_at(branch_idx);
        let post_entries = post.overlay_branch_entries_at(branch_idx);

        assert(post_branch.disk_view.entries_wf()) by {
            assert forall |addr: Address|
                #[trigger] post_entries.contains_key(addr)
                implies post_entries[addr].wf()
            by {
                post.overlay_entry_matches_available(branch_idx, addr);
                if addr == target {
                    assert(post_entries[addr] == post.available_branch_nodes()[addr]);
                    assert(post.available_branch_nodes()[target].wf());
                } else {
                    assert(pre_entries.contains_key(addr));
                    pre.overlay_entry_matches_available(branch_idx, addr);
                    assert(pre.available_branch_nodes().contains_key(addr));
                    assert(post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]);
                    assert(post_entries[addr] == post.available_branch_nodes()[addr]);
                    assert(pre_entries[addr] == pre.available_branch_nodes()[addr]);
                    assert(pre_branch.disk_view.entries.contains_key(addr));
                    assert(pre_branch.disk_view.entries[addr].wf());
                }
            }
        };

        assert(post_branch.disk_view.no_dangling_address()) by {
            assert forall |addr: Address|
                #[trigger] post_entries.contains_key(addr)
                implies post_branch.disk_view.node_has_valid_child_address(post_entries[addr])
            by {
                post.overlay_entry_matches_available(branch_idx, addr);
                if addr == target {
                    assert(post_entries[addr] is Leaf);
                } else {
                    assert(pre_entries.contains_key(addr));
                    pre.overlay_entry_matches_available(branch_idx, addr);
                    assert(post_entries[addr] == pre_entries[addr]);
                    if post_entries[addr] is Index {
                        assert(pre_branch.disk_view.node_has_valid_child_address(pre_entries[addr]));
                        assert forall |idx: int|
                            0 <= idx < post_entries[addr]->children.len()
                            implies {
                                &&& post_branch.disk_view.valid_address(
                                    #[trigger] post_entries[addr]->children[idx],
                                )
                                &&& !(post_branch.disk_view.entries[post_entries[addr]->children[idx]]
                                    is Auxiliary)
                            }
                        by {
                            let child = post_entries[addr]->children[idx];
                            assert(pre_branch.disk_view.valid_address(child));
                            assert(pre_entries.contains_key(child));
                            assert(post_entries.contains_key(child));
                            if child == target {
                                assert(post_entries[child] is Leaf);
                            } else {
                                post.overlay_entry_matches_available(branch_idx, child);
                                pre.overlay_entry_matches_available(branch_idx, child);
                                assert(post_entries[child] == pre_entries[child]);
                                assert(!(pre_entries[child] is Auxiliary));
                            }
                        }
                    }
                }
            }
        };

        assert(post_branch.disk_view.wf());
        assert(post_branch.has_root()) by {
            assert(pre_branch.has_root());
            let root = pre_branch.root;
            assert(post_branch.root == root);
            assert(pre_entries.contains_key(root));
            assert(post_entries.contains_key(root));
            if root == target {
                assert(post_entries[root] is Leaf);
            } else {
                post.overlay_entry_matches_available(branch_idx, root);
                pre.overlay_entry_matches_available(branch_idx, root);
                assert(post_entries[root] == pre_entries[root]);
                assert(!(pre_entries[root] is Auxiliary));
            }
        };
        assert(post_branch.wf());
    }

    pub proof fn active_overlay_branch_wf_after_leaf_update(
        pre: Self,
        post: Self,
        target: Address,
    )
        requires
            pre.cached_branches.len() > 0,
            pre.cached_branches.len() == post.cached_branches.len(),
            pre.cached_branches == post.cached_branches,
            pre.mini_allocator == post.mini_allocator,
            pre.overlay_branch() is Some,
            pre.overlay_branch().unwrap().wf(),
            pre.available_branch_nodes().dom() == post.available_branch_nodes().dom(),
            forall |x: Address|
                x != target && #[trigger] pre.available_branch_nodes().contains_key(x)
                ==> post.available_branch_nodes()[x] == pre.available_branch_nodes()[x],
            pre.available_branch_nodes().contains_key(target),
            post.available_branch_nodes().contains_key(target),
            pre.available_branch_nodes()[target] is Leaf,
            post.available_branch_nodes()[target] is Leaf,
            post.available_branch_nodes()[target].wf(),
        ensures
            post.overlay_branch() is Some,
            post.overlay_branch().unwrap().wf(),
    {
        assert(post.cached_branches.len() > 0);
        assert(post.active_idx() == pre.active_idx());
        assert(post.active_cached_branch() == pre.active_cached_branch());
        assert(post.overlay_branch() is Some);

        let pre_branch = pre.overlay_branch().unwrap();
        let post_branch = post.overlay_branch().unwrap();
        let pre_entries = pre.overlay_branch_entries();
        let post_entries = post.overlay_branch_entries();

        assert forall |addr: Address|
            #[trigger] pre_entries.contains_key(addr) <==> post_entries.contains_key(addr)
        by {
            assert(pre.mini_allocator.page_is_reserved(addr)
                <==> post.mini_allocator.page_is_reserved(addr));
            assert(pre.available_branch_nodes().contains_key(addr)
                <==> post.available_branch_nodes().contains_key(addr));
        };

        assert(post_branch.disk_view.entries_wf()) by {
            assert forall |addr: Address|
                #[trigger] post_entries.contains_key(addr)
                implies post_entries[addr].wf()
            by {
                assert(pre_entries.contains_key(addr));
                if addr == target {
                    assert(post_entries[addr] == post.available_branch_nodes()[addr]);
                    assert(post.available_branch_nodes()[target].wf());
                } else {
                    assert(pre.available_branch_nodes().contains_key(addr));
                    assert(post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]);
                    assert(post_entries[addr] == post.available_branch_nodes()[addr]);
                    assert(pre_entries[addr] == pre.available_branch_nodes()[addr]);
                    assert(pre_branch.disk_view.entries.contains_key(addr));
                    assert(pre_branch.disk_view.entries[addr].wf());
                }
            }
        };

        assert(post_branch.disk_view.no_dangling_address()) by {
            assert forall |addr: Address|
                #[trigger] post_entries.contains_key(addr)
                implies post_branch.disk_view.node_has_valid_child_address(post_entries[addr])
            by {
                assert(pre_entries.contains_key(addr));
                if addr == target {
                    assert(post_entries[addr] is Leaf);
                } else {
                    assert(post_entries[addr] == pre_entries[addr]);
                    if post_entries[addr] is Index {
                        assert(pre_branch.disk_view.node_has_valid_child_address(pre_entries[addr]));
                        assert forall |idx: int|
                            0 <= idx < post_entries[addr]->children.len()
                            implies {
                                &&& post_branch.disk_view.valid_address(
                                    #[trigger] post_entries[addr]->children[idx],
                                )
                                &&& !(post_branch.disk_view.entries[post_entries[addr]->children[idx]]
                                    is Auxiliary)
                            }
                        by {
                            let child = post_entries[addr]->children[idx];
                            assert(pre_branch.disk_view.valid_address(child));
                            assert(pre_entries.contains_key(child));
                            assert(post_entries.contains_key(child));
                            if child == target {
                                assert(post_entries[child] is Leaf);
                            } else {
                                assert(pre.available_branch_nodes().contains_key(child));
                                assert(post.available_branch_nodes()[child]
                                    == pre.available_branch_nodes()[child]);
                                assert(post_entries[child] == pre_entries[child]);
                                assert(!(pre_entries[child] is Auxiliary));
                            }
                        }
                    }
                }
            }
        };

        assert(post_branch.disk_view.wf());
        assert(post_branch.has_root()) by {
            assert(pre_branch.has_root());
            let root = pre_branch.root;
            assert(post_branch.root == root);
            assert(pre_entries.contains_key(root));
            assert(post_entries.contains_key(root));
            if root == target {
                assert(post_entries[root] is Leaf);
            } else {
                assert(post_entries[root] == pre_entries[root]);
                assert(!(pre_entries[root] is Auxiliary));
            }
        };
        assert(post_branch.wf());
    }

    pub proof fn active_overlay_branch_wf_after_grow(
        pre: Self,
        post: Self,
        new_root_addr: Address,
    )
        requires
            pre.cached_branches.len() > 0,
            pre.active_cached_branch().root is Some,
            post.cached_branches.len() == pre.cached_branches.len(),
            post.active_cached_branch().root == Some(new_root_addr),
            post.mini_allocator == pre.mini_allocator.allocate(new_root_addr),
            pre.mini_allocator.wf(),
            pre.mini_allocator.can_allocate(new_root_addr),
            pre.overlay_branch() is Some,
            pre.overlay_branch().unwrap().wf(),
            post.available_branch_nodes().contains_key(new_root_addr),
            post.available_branch_nodes()[new_root_addr] == (AllocationBranchNode::Index{
                pivots: seq![],
                children: seq![pre.active_cached_branch().root.unwrap()],
                aux_ptr: None,
            }),
            forall |addr: Address|
                addr != new_root_addr
                ==> (#[trigger] post.available_branch_nodes().contains_key(addr)
                    <==> pre.available_branch_nodes().contains_key(addr)),
            forall |addr: Address|
                addr != new_root_addr
                && #[trigger] post.available_branch_nodes().contains_key(addr)
                ==> post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr],
        ensures
            post.overlay_branch() is Some,
            post.overlay_branch().unwrap().wf(),
    {
        assert(post.cached_branches.len() > 0);
        let old_root = pre.active_cached_branch().root.unwrap();
        let pre_branch = pre.overlay_branch().unwrap();
        let post_branch = post.overlay_branch().unwrap();
        let pre_entries = pre.overlay_branch_entries();
        let post_entries = post.overlay_branch_entries();

        assert(pre_branch.root == old_root);
        assert(pre_branch.has_root());
        assert(pre_entries.contains_key(old_root));
        assert(pre.mini_allocator.page_is_reserved(old_root));
        assert(!pre.mini_allocator.page_is_reserved(new_root_addr));
        assert(old_root != new_root_addr);

        assert(post_entries.contains_key(new_root_addr)) by {
            assert(post.mini_allocator.page_is_reserved(new_root_addr));
            assert(post.available_branch_nodes().contains_key(new_root_addr));
        };

        assert forall |addr: Address|
            #[trigger] post_entries.contains_key(addr)
            implies addr == new_root_addr || pre_entries.contains_key(addr)
        by {
            assert(post.mini_allocator.page_is_reserved(addr));
            mini_allocator_allocate_page_is_reserved(pre.mini_allocator, new_root_addr, addr);
            if addr != new_root_addr {
                assert(pre.mini_allocator.page_is_reserved(addr));
                assert(pre.available_branch_nodes().contains_key(addr));
                assert(pre_entries.contains_key(addr));
            }
        };

        assert forall |addr: Address|
            #[trigger] pre_entries.contains_key(addr)
            implies post_entries.contains_key(addr)
        by {
            assert(pre.mini_allocator.page_is_reserved(addr));
            mini_allocator_allocate_page_is_reserved(pre.mini_allocator, new_root_addr, addr);
            assert(addr != new_root_addr) by {
                if addr == new_root_addr {
                    assert(pre.mini_allocator.page_is_reserved(new_root_addr));
                    assert(false);
                }
            }
            assert(post.mini_allocator.page_is_reserved(addr));
            assert(pre.available_branch_nodes().contains_key(addr));
            assert(post.available_branch_nodes().contains_key(addr));
        };

        assert(post_branch.disk_view.entries_wf()) by {
            assert forall |addr: Address|
                #[trigger] post_entries.contains_key(addr)
                implies post_entries[addr].wf()
            by {
                if addr == new_root_addr {
                    assert(post_entries[addr] == AllocationBranchNode::Index{
                        pivots: seq![],
                        children: seq![old_root],
                        aux_ptr: None,
                    });
                } else {
                    assert(pre_entries.contains_key(addr));
                    assert(post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]);
                    assert(post_entries[addr] == post.available_branch_nodes()[addr]);
                    assert(pre_entries[addr] == pre.available_branch_nodes()[addr]);
                    assert(pre_branch.disk_view.entries[addr].wf());
                }
            }
        };

        assert(post_branch.disk_view.no_dangling_address()) by {
            assert forall |addr: Address|
                #[trigger] post_entries.contains_key(addr)
                implies post_branch.disk_view.node_has_valid_child_address(post_entries[addr])
            by {
                if addr == new_root_addr {
                    assert(post_entries[addr] == AllocationBranchNode::Index{
                        pivots: seq![],
                        children: seq![old_root],
                        aux_ptr: None,
                    });
                    assert(post_entries.contains_key(old_root));
                    assert(!(post_entries[old_root] is Auxiliary)) by {
                        assert(pre_branch.disk_view.entries.contains_key(old_root));
                        assert(!(pre_branch.disk_view.entries[old_root] is Auxiliary));
                        assert(post_entries[old_root] == pre_entries[old_root]);
                    }
                } else {
                    assert(pre_entries.contains_key(addr));
                    assert(post_entries[addr] == pre_entries[addr]);
                    if post_entries[addr] is Index {
                        assert(pre_branch.disk_view.node_has_valid_child_address(pre_entries[addr]));
                        assert forall |idx: int|
                            0 <= idx < post_entries[addr]->children.len()
                            implies {
                                &&& post_branch.disk_view.valid_address(
                                    #[trigger] post_entries[addr]->children[idx],
                                )
                                &&& !(post_branch.disk_view.entries[post_entries[addr]->children[idx]]
                                    is Auxiliary)
                            }
                        by {
                            let child = post_entries[addr]->children[idx];
                            assert(pre_branch.disk_view.valid_address(child));
                            assert(pre_entries.contains_key(child));
                            assert(child != new_root_addr) by {
                                if child == new_root_addr {
                                    assert(pre.mini_allocator.page_is_reserved(new_root_addr));
                                    assert(false);
                                }
                            }
                            assert(post_entries.contains_key(child));
                            assert(post_entries[child] == pre_entries[child]);
                            assert(!(pre_entries[child] is Auxiliary));
                        }
                    }
                }
            }
        };

        assert(post_branch.disk_view.wf());
        assert(post_branch.has_root()) by {
            assert(post_branch.root == new_root_addr);
            assert(post_entries.contains_key(new_root_addr));
            assert(!(post_entries[new_root_addr] is Auxiliary));
        };
        assert(post_branch.wf());
    }

    pub proof fn active_overlay_branch_wf_after_split(
        pre: Self,
        post: Self,
        receipt: LoadedPathReceipt,
        read_nodes: Map<Address, AllocationBranchNode>,
        write_nodes: Map<Address, AllocationBranchNode>,
        split_arg: SplitArg,
        new_child_addr: Address,
    )
        requires
            pre.cached_branches.len() > 0,
            pre.active_cached_branch().root is Some,
            post.cached_branches.len() == pre.cached_branches.len(),
            post.active_cached_branch() == pre.active_cached_branch(),
            post.mini_allocator == pre.mini_allocator.allocate(new_child_addr),
            pre.mini_allocator.wf(),
            pre.mini_allocator.can_allocate(new_child_addr),
            pre.overlay_branch() is Some,
            pre.overlay_branch().unwrap().wf(),
            receipt.valid_for(pre.active_cached_branch().root.unwrap(), read_nodes),
            crate::implementation::CachedBranch_v::loaded_split_ready(receipt, read_nodes, split_arg),
            write_nodes == crate::implementation::CachedBranch_v::loaded_split_write_nodes(
                receipt,
                read_nodes,
                split_arg,
                new_child_addr,
            ),
            pre.active_managed_reads_agree(receipt.needed_addrs().insert(receipt.child_addr()), read_nodes),
            post.available_branch_nodes().contains_key(receipt.target().addr),
            post.available_branch_nodes()[receipt.target().addr] == write_nodes[receipt.target().addr],
            post.available_branch_nodes().contains_key(receipt.child_addr()),
            post.available_branch_nodes()[receipt.child_addr()] == write_nodes[receipt.child_addr()],
            post.available_branch_nodes().contains_key(new_child_addr),
            post.available_branch_nodes()[new_child_addr] == write_nodes[new_child_addr],
            forall |addr: Address|
                addr != receipt.target().addr
                && addr != receipt.child_addr()
                && addr != new_child_addr
                ==> (#[trigger] post.available_branch_nodes().contains_key(addr)
                    <==> pre.available_branch_nodes().contains_key(addr)),
            forall |addr: Address|
                addr != receipt.target().addr
                && addr != receipt.child_addr()
                && addr != new_child_addr
                && #[trigger] post.available_branch_nodes().contains_key(addr)
                ==> post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr],
        ensures
            post.overlay_branch() is Some,
            post.overlay_branch().unwrap().wf(),
    {
        assert(post.cached_branches.len() > 0);
        let parent_addr = receipt.target().addr;
        let child_addr = receipt.child_addr();
        let pre_branch = pre.overlay_branch().unwrap();
        let post_branch = post.overlay_branch().unwrap();
        let pre_entries = pre.overlay_branch_entries();
        let post_entries = post.overlay_branch_entries();
        let parent = receipt.target().node;
        let child = read_nodes[child_addr];
        let child_idx = parent.route(receipt.key) + 1;

        assert(pre_branch.has_root());
        assert(post_branch.root == pre_branch.root);
        assert(receipt.target().node is Index);
        assert(receipt.target().wf());
        assert(parent.wf());
        assert(parent.keys_strictly_sorted());
        crate::betree::LinkedBranch_v::Refinement_v::lemma_route_ensures(parent, receipt.key);
        assert(parent.valid_child_index(child_idx));
        assert(parent == read_nodes[parent_addr]);
        assert(child == read_nodes[child_addr]);
        assert(parent->children[child_idx] == child_addr);
        assert(parent_addr != child_addr);
        assert(receipt.needed_addrs().contains(parent_addr)) by {
            let i = receipt.lines.len() - 1;
            assert(0 <= i < receipt.lines.len());
            assert(receipt.lines[i].addr == parent_addr);
        }
        assert(receipt.needed_addrs().insert(child_addr).contains(parent_addr));
        assert(receipt.needed_addrs().insert(child_addr).contains(child_addr));
        assert(write_nodes.contains_key(parent_addr));
        assert(write_nodes.contains_key(child_addr));
        assert(write_nodes.contains_key(new_child_addr));
        assert(!pre.mini_allocator.page_is_reserved(new_child_addr));
        assert(!pre_entries.contains_key(new_child_addr)) by {
            if pre_entries.contains_key(new_child_addr) {
                assert(pre.mini_allocator.page_is_reserved(new_child_addr));
                assert(false);
            }
        }

        assert(pre_entries.contains_key(parent_addr));
        assert(pre_entries.contains_key(child_addr));
        assert(read_nodes[parent_addr] == pre_entries[parent_addr]);
        assert(read_nodes[child_addr] == pre_entries[child_addr]);
        assert(pre_entries[parent_addr] == parent);
        assert(pre_entries[child_addr] == child);
        assert(pre.mini_allocator.page_is_reserved(parent_addr));
        assert(pre.mini_allocator.page_is_reserved(child_addr));

        assert(post_entries.contains_key(parent_addr)) by {
            assert(post.mini_allocator.page_is_reserved(parent_addr));
            assert(post.available_branch_nodes().contains_key(parent_addr));
        };
        assert(post_entries.contains_key(child_addr)) by {
            assert(post.mini_allocator.page_is_reserved(child_addr));
            assert(post.available_branch_nodes().contains_key(child_addr));
        };
        assert(post_entries.contains_key(new_child_addr)) by {
            assert(post.mini_allocator.page_is_reserved(new_child_addr));
            assert(post.available_branch_nodes().contains_key(new_child_addr));
        };
        assert(post_entries[parent_addr] == write_nodes[parent_addr]);
        assert(post_entries[child_addr] == write_nodes[child_addr]);
        assert(post_entries[new_child_addr] == write_nodes[new_child_addr]);
        assert(write_nodes[parent_addr] == AllocationBranchNode::Index{
            pivots: parent->pivots.insert(child_idx, receipt.key),
            children: parent->children.insert(child_idx + 1, new_child_addr),
            aux_ptr: None,
        });

        assert forall |addr: Address|
            #[trigger] post_entries.contains_key(addr)
            implies addr == new_child_addr || pre_entries.contains_key(addr)
        by {
            assert(post.mini_allocator.page_is_reserved(addr));
            mini_allocator_allocate_page_is_reserved(pre.mini_allocator, new_child_addr, addr);
            if addr != new_child_addr {
                assert(pre.mini_allocator.page_is_reserved(addr));
                if addr == parent_addr || addr == child_addr {
                    assert(pre_entries.contains_key(addr));
                } else {
                    assert(pre.available_branch_nodes().contains_key(addr));
                    assert(pre_entries.contains_key(addr));
                }
            }
        };

        assert forall |addr: Address|
            #[trigger] pre_entries.contains_key(addr)
            implies post_entries.contains_key(addr)
        by {
            assert(pre.mini_allocator.page_is_reserved(addr));
            mini_allocator_allocate_page_is_reserved(pre.mini_allocator, new_child_addr, addr);
            assert(addr != new_child_addr) by {
                if addr == new_child_addr {
                    assert(false);
                }
            }
            assert(post.mini_allocator.page_is_reserved(addr));
            if addr == parent_addr || addr == child_addr {
                assert(post.available_branch_nodes().contains_key(addr));
            } else {
                assert(pre.available_branch_nodes().contains_key(addr));
                assert(post.available_branch_nodes().contains_key(addr));
            }
        };

        assert(post_branch.disk_view.entries_wf()) by {
            assert forall |addr: Address|
                #[trigger] post_entries.contains_key(addr)
                implies post_entries[addr].wf()
            by {
                if addr == parent_addr {
                    assert(post_entries[addr] == write_nodes[parent_addr]);
                    assert(post_entries[addr] == AllocationBranchNode::Index{
                        pivots: parent->pivots.insert(child_idx, receipt.key),
                        children: parent->children.insert(child_idx + 1, new_child_addr),
                        aux_ptr: None,
                    });
                    assert(parent.wf());
                    assert(post_entries[addr]->pivots.len() == parent->pivots.len() + 1);
                    assert(post_entries[addr]->children.len() == parent->children.len() + 1);
                } else if addr == child_addr {
                    assert(post_entries[addr] == write_nodes[child_addr]);
                    if split_arg is SplitLeaf {
                        let split_index = Key::largest_lt(child->keys, split_arg.get_pivot()) + 1;
                        assert(0 < split_index);
                        assert(split_index < child->keys.len());
                        assert(child.wf());
                    } else {
                        assert(child.wf());
                    }
                } else if addr == new_child_addr {
                    assert(post_entries[addr] == write_nodes[new_child_addr]);
                    if split_arg is SplitLeaf {
                        let split_index = Key::largest_lt(child->keys, split_arg.get_pivot()) + 1;
                        assert(0 < split_index);
                        assert(split_index < child->keys.len());
                        assert(child.wf());
                    } else {
                        assert(child.wf());
                    }
                } else {
                    assert(pre_entries.contains_key(addr));
                    assert(post.available_branch_nodes()[addr] == pre.available_branch_nodes()[addr]);
                    assert(post_entries[addr] == post.available_branch_nodes()[addr]);
                    assert(pre_entries[addr] == pre.available_branch_nodes()[addr]);
                    assert(pre_branch.disk_view.entries[addr].wf());
                }
            }
        };

        assert(post_branch.disk_view.no_dangling_address()) by {
            assert forall |addr: Address|
                #[trigger] post_entries.contains_key(addr)
                implies post_branch.disk_view.node_has_valid_child_address(post_entries[addr])
            by {
                if addr == parent_addr {
                    assert(post_entries[addr] == write_nodes[parent_addr]);
                    if post_entries[addr] is Index {
                        assert(post_entries[addr] == AllocationBranchNode::Index{
                            pivots: parent->pivots.insert(child_idx, receipt.key),
                            children: parent->children.insert(child_idx + 1, new_child_addr),
                            aux_ptr: None,
                        });
                        assert forall |idx: int|
                            0 <= idx < post_entries[addr]->children.len()
                            implies {
                                &&& post_branch.disk_view.valid_address(
                                    #[trigger] post_entries[addr]->children[idx],
                                )
                                &&& !(post_branch.disk_view.entries[post_entries[addr]->children[idx]]
                                    is Auxiliary)
                            }
                        by {
                            let new_parent = post_entries[addr];
                            let old_parent = parent;
                            assert(new_parent->children == old_parent->children.insert(child_idx + 1, new_child_addr));
                            let old_child =
                                if idx < child_idx + 1 {
                                    old_parent->children[idx]
                                } else {
                                    old_parent->children[idx - 1]
                                };
                            if idx == child_idx + 1 {
                                assert(0 <= child_idx + 1 <= old_parent->children.len());
                                assert(new_parent->children[idx] == new_child_addr);
                                assert(post_entries.contains_key(new_child_addr));
                                assert(!(post_entries[new_child_addr] is Auxiliary));
                            } else {
                                assert(idx < child_idx + 1 || idx > child_idx + 1);
                                assert(old_parent.valid_child_index(
                                    if idx < child_idx + 1 { idx } else { idx - 1 },
                                ));
                                assert(new_parent->children[idx] == old_child);
                                assert(pre_branch.disk_view.node_has_valid_child_address(old_parent));
                                assert(pre_entries.contains_key(old_child));
                                assert(!(pre_entries[old_child] is Auxiliary));
                                assert(post_entries.contains_key(old_child));
                                if old_child == parent_addr {
                                    assert(!(post_entries[old_child] is Auxiliary));
                                } else if old_child == child_addr {
                                    assert(!(post_entries[old_child] is Auxiliary));
                                } else {
                                    assert(old_child != new_child_addr) by {
                                        if old_child == new_child_addr {
                                            assert(pre.mini_allocator.page_is_reserved(new_child_addr));
                                            assert(false);
                                        }
                                    }
                                    assert(post_entries[old_child] == pre_entries[old_child]);
                                    assert(!(post_entries[old_child] is Auxiliary));
                                }
                            }
                        }
                    }
                } else if addr == child_addr || addr == new_child_addr {
                    if post_entries[addr] is Index {
                        assert(child is Index);
                        assert(pre_branch.disk_view.node_has_valid_child_address(child));
                        assert forall |idx: int|
                            0 <= idx < post_entries[addr]->children.len()
                            implies {
                                &&& post_branch.disk_view.valid_address(
                                    #[trigger] post_entries[addr]->children[idx],
                                )
                                &&& !(post_branch.disk_view.entries[post_entries[addr]->children[idx]]
                                    is Auxiliary)
                            }
                        by {
                            let split_child = post_entries[addr]->children[idx];
                            assert(child.valid_child_index(
                                if addr == child_addr {
                                    idx
                                } else {
                                    idx + split_arg->pivot_index + 1
                                },
                            ));
                            assert(pre_entries.contains_key(split_child));
                            assert(!(pre_entries[split_child] is Auxiliary));
                            assert(post_entries.contains_key(split_child));
                            if split_child == parent_addr {
                                assert(!(post_entries[split_child] is Auxiliary));
                            } else if split_child == child_addr {
                                assert(!(post_entries[split_child] is Auxiliary));
                            } else {
                                assert(split_child != new_child_addr) by {
                                    if split_child == new_child_addr {
                                        assert(pre.mini_allocator.page_is_reserved(new_child_addr));
                                        assert(false);
                                    }
                                }
                                assert(post_entries[split_child] == pre_entries[split_child]);
                                assert(!(post_entries[split_child] is Auxiliary));
                            }
                        }
                    }
                } else {
                    assert(pre_entries.contains_key(addr));
                    assert(post_entries[addr] == pre_entries[addr]);
                    if post_entries[addr] is Index {
                        assert(pre_branch.disk_view.node_has_valid_child_address(pre_entries[addr]));
                        assert forall |idx: int|
                            0 <= idx < post_entries[addr]->children.len()
                            implies {
                                &&& post_branch.disk_view.valid_address(
                                    #[trigger] post_entries[addr]->children[idx],
                                )
                                &&& !(post_branch.disk_view.entries[post_entries[addr]->children[idx]]
                                    is Auxiliary)
                            }
                        by {
                            let old_child = post_entries[addr]->children[idx];
                            assert(pre_entries.contains_key(old_child));
                            assert(!(pre_entries[old_child] is Auxiliary));
                            assert(post_entries.contains_key(old_child));
                            if old_child == parent_addr {
                                assert(!(post_entries[old_child] is Auxiliary));
                            } else if old_child == child_addr {
                                assert(!(post_entries[old_child] is Auxiliary));
                            } else {
                                assert(old_child != new_child_addr) by {
                                    if old_child == new_child_addr {
                                        assert(pre.mini_allocator.page_is_reserved(new_child_addr));
                                        assert(false);
                                    }
                                }
                                assert(post_entries[old_child] == pre_entries[old_child]);
                                assert(!(post_entries[old_child] is Auxiliary));
                            }
                        }
                    }
                }
            }
        };

        assert(post_branch.disk_view.wf());
        assert(post_branch.has_root()) by {
            assert(pre_branch.has_root());
            let root = pre_branch.root;
            assert(post_branch.root == root);
            assert(pre_entries.contains_key(root));
            assert(post_entries.contains_key(root));
            if root == parent_addr {
                assert(!(post_entries[root] is Auxiliary));
            } else if root == child_addr {
                assert(!(post_entries[root] is Auxiliary));
            } else {
                assert(root != new_child_addr) by {
                    if root == new_child_addr {
                        assert(pre.mini_allocator.page_is_reserved(new_child_addr));
                        assert(false);
                    }
                }
                assert(post_entries[root] == pre_entries[root]);
                assert(!(pre_entries[root] is Auxiliary));
            }
        };
        assert(post_branch.wf());
    }

    pub proof fn overlay_entry_matches_available(self, branch_idx: nat, addr: Address)
        requires
            branch_idx < self.cached_branches.len(),
            self.overlay_branch_entries_at(branch_idx).contains_key(addr),
        ensures
            self.available_branch_nodes().contains_key(addr),
            self.available_branch_nodes()[addr] == self.overlay_branch_entries_at(branch_idx)[addr],
    {
        assert(self.has_overlay_page_at(branch_idx, addr));
        assert(self.cached_branches[branch_idx as int].root is Some);
        let root = self.cached_branches[branch_idx as int].root.unwrap();
        self.reachable_branch_addr_implies_available_branch_node(
            branch_idx,
            root,
            self.available_branch_nodes().dom().len(),
            addr,
        );
        assert(self.available_raw_pages().contains_key(addr));
        assert(self.available_branch_nodes()[addr]
            == raw_page_to_branch_node(self.available_raw_pages()[addr]));
        assert(self.overlay_branch_entries_at(branch_idx)[addr]
            == raw_page_to_branch_node(self.overlay_raw_page_at(branch_idx, addr)));
        if self.has_cached_page(addr) {
            assert(self.available_raw_pages()[addr] == self.cache_raw_page(addr));
            assert(self.overlay_raw_page_at(branch_idx, addr) == self.cache_raw_page(addr));
        } else {
            assert(self.disk.content.contains_key(addr));
            assert(self.available_raw_pages()[addr] == self.disk.content[addr]);
            assert(self.overlay_raw_page_at(branch_idx, addr) == self.disk.content[addr]);
        }
    }
}

} // verus!
