// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::{map::*, set::*};

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranch_v::{BranchNode as AllocationBranchNode, Summary};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::Utils_v::union_seq_of_sets;
use crate::betree::LinkedBranch_v::{LinkedBranch, Path as BranchPath, SplitArg};
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::Cache_v::{Cache, Entry, Status};
use crate::implementation::CachedBranch_v::{CachedBranch, init_mini_allocator};
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::spec::Messages_t::Message;

verus! {

// TODO: replace this placeholder with a real branch-page marshaller/parser.
pub open spec fn encode_branch_page(node: AllocationBranchNode) -> RawPage
{
    arbitrary()
}

// TODO: replace this placeholder with a real branch-page marshaller/parser.
pub open spec fn decode_branch_page(raw_page: RawPage) -> AllocationBranchNode
{
    arbitrary()
}

pub open spec fn to_branch_nodes(raw_pages: Map<Address, RawPage>) -> Map<Address, AllocationBranchNode>
{
    Map::new(
        |addr: Address| raw_pages.contains_key(addr),
        |addr: Address| decode_branch_page(raw_pages[addr]),
    )
}

pub proof fn invert_contains_pair<K, V>(map: Map<K, V>, value: V)
    requires
        map.contains_value(value),
    ensures
        map.contains_pair(map.invert()[value], value),
{
    assert(exists |key: K| map.contains_pair(key, value)) by {
        let key = choose |key: K|
            #![trigger map[key]]
            map.contains_key(key) && map[key] == value;
        assert(map.contains_pair(key, value));
    }
    let key = choose |key: K| map.contains_pair(key, value);
    assert(map.contains_pair(key, value));
    reveal(Map::invert);
    assert(map.invert()[value] == key);
    assert(map.contains_pair(map.invert()[value], value));
}

pub proof fn remove_keys_preserves_unremoved<K, V>(base: Map<K, V>, keys: Set<K>, key: K)
    requires
        base.contains_key(key),
        !keys.contains(key),
    ensures
        base.remove_keys(keys).contains_key(key),
        base.remove_keys(keys)[key] == base[key],
{
    assert(base.remove_keys(keys).contains_key(key));
    assert(base.remove_keys(keys)[key] == base[key]);
}

pub proof fn remove_keys_removes_removed<K, V>(base: Map<K, V>, keys: Set<K>, key: K)
    requires
        keys.contains(key),
    ensures
        !base.remove_keys(keys).contains_key(key),
{
    assert(!base.remove_keys(keys).contains_key(key));
}

pub proof fn remove_keys_preserves_injective<K, V>(base: Map<K, V>, keys: Set<K>)
    requires
        base.is_injective(),
    ensures
        base.remove_keys(keys).is_injective(),
{
    let reduced = base.remove_keys(keys);
    assert forall |k1: K, k2: K|
        k1 != k2
        && reduced.contains_key(k1)
        && reduced.contains_key(k2)
        implies #[trigger] reduced[k1] != #[trigger] reduced[k2]
    by {
        assert(base.contains_key(k1));
        assert(base.contains_key(k2));
        assert(reduced[k1] == base[k1]);
        assert(reduced[k2] == base[k2]);
        assert(base[k1] != base[k2]);
    }
}

pub proof fn union_prefer_right_uses_left<K, V>(left: Map<K, V>, right: Map<K, V>, key: K)
    requires
        left.contains_key(key),
        !right.contains_key(key),
    ensures
        left.union_prefer_right(right).contains_key(key),
        left.union_prefer_right(right)[key] == left[key],
{
    assert(left.union_prefer_right(right).contains_key(key));
    assert(left.union_prefer_right(right)[key] == left[key]);
}

pub proof fn union_prefer_right_uses_right<K, V>(left: Map<K, V>, right: Map<K, V>, key: K)
    requires
        right.contains_key(key),
    ensures
        left.union_prefer_right(right).contains_key(key),
        left.union_prefer_right(right)[key] == right[key],
{
    assert(left.union_prefer_right(right).contains_key(key));
    assert(left.union_prefer_right(right)[key] == right[key]);
}

pub open spec fn init_has_projected_page(disk: AsyncDisk::State, addr: Address) -> bool
{
    disk.content.contains_key(addr)
}

pub open spec fn init_projected_raw_page(disk: AsyncDisk::State, addr: Address) -> RawPage
    recommends init_has_projected_page(disk, addr)
{
    disk.content[addr]
}

pub open spec fn init_projected_branch_entries(disk: AsyncDisk::State) -> Map<Address, AllocationBranchNode>
{
    to_branch_nodes(Map::new(
        |addr: Address| init_has_projected_page(disk, addr),
        |addr: Address| init_projected_raw_page(disk, addr),
    ))
}

pub open spec fn init_projected_branch(cached_branch: CachedBranch, disk: AsyncDisk::State) -> LinkedBranch<Summary>
    recommends
        cached_branch.sealed,
        cached_branch.root is Some,
{
    LinkedBranch {
        root: cached_branch.root.unwrap(),
        disk_view: crate::betree::LinkedBranch_v::DiskView { entries: init_projected_branch_entries(disk) },
    }
}

pub open spec fn init_projection_valid(cached_branch: CachedBranch, disk: AsyncDisk::State) -> bool
{
    if cached_branch.sealed {
        init_projected_branch(cached_branch, disk).valid_sealed_branch()
    } else {
        cached_branch.root is None
    }
}

state_machine!{ ConcreteBranch {
    fields {
        pub cached_branch: CachedBranch,
        pub mini_allocator: MiniAllocator,
        pub cache: Cache::State,
        pub disk: AsyncDisk::State,
        pub outstanding_cache_reqs: Map<ID, Address>,
    }

    pub enum Label {
        Query{key: Key, msg: Message, depth: nat},
        Append{
            keys: Seq<Key>,
            msgs: Seq<Message>,
            depth: nat,
        },
        Grow{new_root_addr: Address},
        Split{
            new_child_addr: Address,
            pivot: Key,
            depth: nat,
            split_arg: SplitArg,
        },
        Seal{aux_ptr: Pointer},
        Internal{},
    }

    init!{ initialize(cached_branch: CachedBranch, init_aus: Set<AU>, cache: Cache::State, cache_slots: nat, disk: AsyncDisk::State) {
        require cached_branch.valid_init(init_aus);
        require Cache::State::initialize(cache, cache_slots);
        require disk.inv();
        require disk.requests.is_empty();
        require disk.responses.is_empty();
        require init_projection_valid(cached_branch, disk);

        init cached_branch = cached_branch;
        init mini_allocator = init_mini_allocator(init_aus);
        init cache = cache;
        init disk = disk;
        init outstanding_cache_reqs = Map::empty();
    }}

    transition!{ query(
        lbl: Label,
        reads: Map<Address, RawPage>,
        needed: Set<Address>,
    ) {
        require let Label::Query{key, msg, depth} = lbl;
        require pre.wf();
        let read_nodes = to_branch_nodes(reads);
        require pre.cached_branch.can_query(pre.mini_allocator, key, depth, read_nodes, needed);
        require msg == pre.cached_branch.query_result(key, depth, read_nodes);

        let cache_lbl = Self::cache_access_label(reads, Map::<Address, RawPage>::empty());
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);
    }}

    transition!{ append(
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        needed: Set<Address>,
        new_cache: Cache::State,
    ) {
        require let Label::Append{keys, msgs, depth} = lbl;
        require pre.wf();
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pre.cached_branch.can_append(pre.mini_allocator, keys, msgs, depth, read_nodes, write_nodes, needed);
        let new_cached_branch = pre.cached_branch.append(keys, msgs, depth, read_nodes, write_nodes, needed);

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branch = new_cached_branch;
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
        require pre.cached_branch.can_grow(pre.mini_allocator, new_root_addr, read_nodes, write_nodes);
        let new_cached_branch = pre.cached_branch.grow(pre.mini_allocator, new_root_addr, read_nodes, write_nodes);
        let new_mini_allocator = pre.mini_allocator.allocate(new_root_addr);

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branch = new_cached_branch;
        update mini_allocator = new_mini_allocator;
        update cache = new_cache;
    }}

    transition!{ split(
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        needed: Set<Address>,
        new_cache: Cache::State,
    ) {
        require let Label::Split{new_child_addr, pivot, depth, split_arg} = lbl;
        require pre.wf();
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pre.cached_branch.can_split(pre.mini_allocator, new_child_addr, pivot, depth, split_arg, read_nodes, write_nodes, needed);
        let new_cached_branch = pre.cached_branch.split(pre.mini_allocator, new_child_addr, pivot, depth, split_arg, read_nodes, write_nodes, needed);
        let new_mini_allocator = pre.mini_allocator.allocate(new_child_addr);

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branch = new_cached_branch;
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
        require pre.cached_branch.can_seal(pre.mini_allocator, aux_ptr, read_nodes, write_nodes);
        let new_cached_branch = pre.cached_branch.seal(pre.mini_allocator, aux_ptr, read_nodes, write_nodes);
        let new_mini_allocator =
            if aux_ptr is Some {
                pre.mini_allocator.allocate(aux_ptr.unwrap()).prune(Set::<AU>::empty())
            } else {
                pre.mini_allocator.prune(Set::<AU>::empty())
            };

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branch = new_cached_branch;
        update mini_allocator = new_mini_allocator;
        update cache = new_cache;
    }}

    transition!{ internal_cache(lbl: Label, new_cache: Cache::State) {
        require lbl is Internal;
        require pre.wf();
        require Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{});

        update cache = new_cache;
    }}

    transition!{ internal_disk(lbl: Label, new_disk: AsyncDisk::State) {
        require lbl is Internal;
        require pre.wf();
        require AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{});

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

        update cache = new_cache;
        update disk = new_disk;
        update outstanding_cache_reqs = pre.next_outstanding_cache_reqs(disk_requests, disk_responses);
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        self.wf()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, cached_branch: CachedBranch, init_aus: Set<AU>, cache: Cache::State, cache_slots: nat, disk: AsyncDisk::State) {
        reveal(Cache::State::initialize);
        assert(post.cached_branch == cached_branch);
        assert(post.mini_allocator == init_mini_allocator(init_aus));
        assert(post.cache == cache);
        assert(post.disk == disk);
        assert(post.outstanding_cache_reqs == Map::<ID, Address>::empty());
        assert(post.cached_branch.wf());
        assert(post.cached_branch.valid_allocator(post.mini_allocator));
        assert(post.mini_allocator.wf());
        Cache::State::initialize_inductive(post.cache, cache_slots);
        assert(post.cache.inv());
        assert(post.disk.inv());
        assert(post.disk.requests.is_empty());
        assert(post.disk.responses.is_empty());
        assert(post.outstanding_reqs_consistent()) by {
            assert(post.outstanding_cache_reqs.is_injective());
            assert(post.disk.requests.dom() + post.disk.responses.dom() == post.outstanding_cache_reqs.dom());
            assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id) implies post.outstanding_reqs_requests_ok() by {
                assert(false);
            }
            assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id) implies post.outstanding_reqs_responses_ok() by {
                assert(false);
            }
        }
        assert(post.cache.lookup_map == Map::<Address, crate::implementation::Cache_v::Slot>::empty());
        assert forall |addr: Address|
            post.has_cached_page(addr) && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
        implies {
            &&& post.disk.content.contains_key(addr)
            &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
        } by {
            assert(!post.has_cached_page(addr));
        };
        assert(post.cache_agrees_with_disk());
        assert(post.wf());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>, needed: Set<Address>) {
        Self::query_preserves_wf(pre, post, lbl, reads, needed);
    }

    #[inductive(append)]
    fn append_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        needed: Set<Address>,
        new_cache: Cache::State,
    ) {
        Self::append_preserves_wf(pre, post, lbl, reads, writes, needed, new_cache);
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
        Self::grow_preserves_wf(pre, post, lbl, reads, writes, new_cache);
    }

    #[inductive(split)]
    fn split_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        needed: Set<Address>,
        new_cache: Cache::State,
    ) {
        Self::split_preserves_wf(pre, post, lbl, reads, writes, needed, new_cache);
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
        Self::seal_preserves_wf(pre, post, lbl, reads, writes, new_cache);
    }

    #[inductive(internal_cache)]
    fn internal_cache_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State) {
        Self::internal_cache_preserves_wf(pre, post, lbl, new_cache);
    }

    #[inductive(internal_disk)]
    fn internal_disk_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State) {
        Self::internal_disk_preserves_wf(pre, post, lbl, new_disk);
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
        Self::cache_disk_ops_preserves_wf(
            pre,
            post,
            lbl,
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        );
    }
}}

impl ConcreteBranch::State {
    proof fn cache_access_preserves_inv(
        pre: Self,
        post_cache: Cache::State,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, post_cache, Self::cache_access_label(reads, writes)),
        ensures
            post_cache.inv(),
    {
        Cache::State::inv_next(pre.cache, post_cache, Self::cache_access_label(reads, writes));
    }

    proof fn cache_internal_preserves_inv(
        pre: Self,
        post_cache: Cache::State,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, post_cache, Cache::Label::Internal{}),
        ensures
            post_cache.inv(),
    {
        Cache::State::inv_next(pre.cache, post_cache, Cache::Label::Internal{});
    }

    proof fn cache_diskops_preserves_inv(
        pre: Self,
        post_cache: Cache::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
    )
        requires
            pre.wf(),
            Cache::State::next(
                pre.cache,
                post_cache,
                Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses},
            ),
        ensures
            post_cache.inv(),
    {
        Cache::State::inv_next(
            pre.cache,
            post_cache,
            Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses},
        );
    }

    proof fn disk_internal_preserves_inv(
        pre: Self,
        post_disk: AsyncDisk::State,
    )
        requires
            pre.wf(),
            AsyncDisk::State::next(pre.disk, post_disk, AsyncDisk::Label::Internal{}),
        ensures
            post_disk.inv(),
    {
        crate::spec::AsyncDisk_t::inv_next(pre.disk, post_disk, AsyncDisk::Label::Internal{});
    }

    proof fn disk_diskops_preserves_inv(
        pre: Self,
        post_disk: AsyncDisk::State,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            pre.wf(),
            AsyncDisk::State::next(
                pre.disk,
                post_disk,
                AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses},
            ),
        ensures
            post_disk.inv(),
    {
        crate::spec::AsyncDisk_t::inv_next(
            pre.disk,
            post_disk,
            AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses},
        );
    }

    proof fn cache_has_cached_page_gets_addr(cache: Cache::State, addr: Address)
        requires
            cache.inv(),
            cache.lookup_map.contains_key(addr),
            cache.entries[cache.lookup_map[addr]] is Filled,
        ensures
            cache.entries.contains_key(cache.lookup_map[addr]),
            cache.entries[cache.lookup_map[addr]] is Filled,
            cache.entries[cache.lookup_map[addr]].get_addr() == addr,
    {
        cache.build_lookup_map_ensures();
    }

    proof fn cache_non_empty_slot_in_lookup(cache: Cache::State, slot: crate::implementation::Cache_v::Slot)
        requires
            cache.inv(),
            cache.entries.contains_key(slot),
            !(cache.entries[slot] is Empty),
        ensures
            cache.lookup_map.contains_key(cache.entries[slot].get_addr()),
            cache.lookup_map[cache.entries[slot].get_addr()] == slot,
    {
        cache.build_lookup_map_ensures();
    }

    proof fn cache_lookup_slot_gets_addr(cache: Cache::State, addr: Address)
        requires
            cache.inv(),
            cache.lookup_map.contains_key(addr),
        ensures
            cache.entries.contains_key(cache.lookup_map[addr]),
            !(cache.entries[cache.lookup_map[addr]] is Empty),
            cache.entries[cache.lookup_map[addr]].get_addr() == addr,
    {
        cache.build_lookup_map_ensures();
    }

    pub open spec fn cache_access_label(
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) -> Cache::Label
    {
        Cache::Label::Access{
            reads,
            writes,
        }
    }

    pub open spec fn available_raw_pages(self) -> Map<Address, RawPage>
    {
        Map::new(
            |addr: Address| self.has_cached_page(addr) || self.disk.content.contains_key(addr),
            |addr: Address| if self.has_cached_page(addr) {
                self.cache_raw_page(addr)
            } else {
                self.disk.content[addr]
            },
        )
    }

    pub open spec fn available_branch_nodes(self) -> Map<Address, AllocationBranchNode>
    {
        to_branch_nodes(self.available_raw_pages())
    }

    pub open spec(checked) fn reachable_branch_addrs_from_with_fuel_contains(self, addr: Address, fuel: nat, a: Address) -> bool
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
                ||| node->aux_ptr is Some
                    && self.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), (fuel - 1) as nat, a)
                ||| exists |i: int|
                    0 <= i < node->children.len()
                    && self.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a)
            }
        }
    }

    pub open spec(checked) fn reachable_branch_addrs_from_with_fuel(self, addr: Address, fuel: nat) -> Set<Address>
        decreases fuel, 2nat
    {
        Set::new(|a: Address| self.reachable_branch_addrs_from_with_fuel_contains(addr, fuel, a))
    }

    pub open spec fn effective_branch_addrs(self) -> Set<Address>
    {
        if self.cached_branch.root is Some {
            self.reachable_branch_addrs_from_with_fuel(
                self.cached_branch.root.unwrap(),
                self.available_branch_nodes().dom().len(),
            )
        } else {
            Set::<Address>::empty()
        }
    }

    pub proof fn reachable_branch_addrs_index_contains(self, addr: Address, fuel: nat, a: Address)
        requires
            fuel > 0,
            self.available_branch_nodes().contains_key(addr),
            !(self.available_branch_nodes()[addr] is Leaf),
            !(self.available_branch_nodes()[addr] is Auxiliary),
        ensures
            self.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
                <==> {
                    let node = self.available_branch_nodes()[addr];
                    ||| a == addr
                    ||| node->aux_ptr is Some
                        && self.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), (fuel - 1) as nat, a)
                    ||| exists |i: int|
                        0 <= i < node->children.len()
                        && self.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a)
                },
    {
        reveal(ConcreteBranch::State::reachable_branch_addrs_from_with_fuel);
        reveal(ConcreteBranch::State::reachable_branch_addrs_from_with_fuel_contains);
        assert(self.reachable_branch_addrs_from_with_fuel(addr, fuel).contains(a)
            <==> {
                let node = self.available_branch_nodes()[addr];
                ||| a == addr
                ||| node->aux_ptr is Some
                    && self.reachable_branch_addrs_from_with_fuel_contains(node->aux_ptr.unwrap(), (fuel - 1) as nat, a)
                ||| exists |i: int|
                    0 <= i < node->children.len()
                    && self.reachable_branch_addrs_from_with_fuel_contains(node->children[i], (fuel - 1) as nat, a)
            });
    }

    pub open spec fn reserved_branch_addrs(self) -> Set<Address>
    {
        self.effective_branch_addrs()
    }

    pub open spec fn has_cached_page(self, addr: Address) -> bool
    {
        &&& self.cache.lookup_map.contains_key(addr)
        &&& self.cache.entries[self.cache.lookup_map[addr]] is Filled
    }

    pub open spec fn cache_raw_page(self, addr: Address) -> RawPage
        recommends self.has_cached_page(addr)
    {
        self.cache.entries[self.cache.lookup_map[addr]]->data
    }

    pub open spec fn cache_agrees_with_disk(self) -> bool
    {
        self.cached_branch.sealed ==> (
            forall |addr: Address|
                #![trigger self.has_cached_page(addr)]
                #![trigger self.cache.status_map[self.cache.lookup_map[addr]]]
                self.has_cached_page(addr)
                && self.cache.status_map[self.cache.lookup_map[addr]] is Clean
                ==> {
                    &&& self.disk.content.contains_key(addr)
                    &&& self.cache_raw_page(addr) == #[trigger] self.disk.content[addr]
                }
        )
    }

    pub open spec fn has_effective_page(self, addr: Address) -> bool
    {
        self.effective_branch_addrs().contains(addr)
    }

    pub open spec fn effective_raw_page(self, addr: Address) -> RawPage
        recommends self.has_effective_page(addr)
    {
        if self.has_cached_page(addr) {
            self.cache_raw_page(addr)
        } else {
            self.disk.content[addr]
        }
    }

    pub open spec fn effective_branch_entries(self) -> Map<Address, AllocationBranchNode>
    {
        to_branch_nodes(Map::new(
            |addr: Address| self.has_effective_page(addr),
            |addr: Address| self.effective_raw_page(addr),
        ))
    }

    pub open spec fn effective_branch(self) -> Option<LinkedBranch<Summary>>
    {
        match self.cached_branch.root {
            Some(root) => Some(LinkedBranch {
                root,
                disk_view: crate::betree::LinkedBranch_v::DiskView { entries: self.effective_branch_entries() },
            }),
            None => None,
        }
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.cached_branch.wf()
        &&& self.cached_branch.valid_allocator(self.mini_allocator)
        &&& self.mini_allocator.wf()
        &&& self.cache.inv()
        &&& self.disk.inv()
        &&& self.outstanding_reqs_consistent()
        &&& forall |addr: Address|
            #![trigger self.has_cached_page(addr)]
            #![trigger self.cache.status_map[self.cache.lookup_map[addr]]]
            self.has_cached_page(addr)
            && self.cache.status_map[self.cache.lookup_map[addr]] is Clean
            ==> {
                &&& self.disk.content.contains_key(addr)
                &&& self.cache_raw_page(addr) == #[trigger] self.disk.content[addr]
            }
        &&& self.cache_agrees_with_disk()
    }

    proof fn clean_cached_page_matches_disk(self, addr: Address)
        requires
            self.wf(),
            self.has_cached_page(addr),
            self.cache.status_map[self.cache.lookup_map[addr]] is Clean,
        ensures
            self.disk.content.contains_key(addr),
            self.cache_raw_page(addr) == self.disk.content[addr],
    {
        assert({
            &&& self.disk.content.contains_key(addr)
            &&& self.cache_raw_page(addr) == self.disk.content[addr]
        });
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

    proof fn mini_allocator_allocate_preserves_wf_and_aus(
        mini_allocator: MiniAllocator,
        addr: Address,
    )
        requires
            mini_allocator.wf(),
            mini_allocator.can_allocate(addr),
        ensures
            mini_allocator.allocate(addr).wf(),
            mini_allocator.allocate(addr).all_aus() == mini_allocator.all_aus(),
    {
        assert(mini_allocator.allocs.contains_key(addr.au));
        assert(mini_allocator.allocate(addr).allocs.dom() == mini_allocator.allocs.dom());
    }

    proof fn mini_allocator_prune_empty_preserves_wf_and_aus(
        mini_allocator: MiniAllocator,
    )
        requires
            mini_allocator.wf(),
        ensures
            mini_allocator.prune(Set::<AU>::empty()).wf(),
            mini_allocator.prune(Set::<AU>::empty()).all_aus() == mini_allocator.all_aus(),
    {
        assert(mini_allocator.prune(Set::<AU>::empty()).allocs.dom() == mini_allocator.allocs.dom());
    }

    pub proof fn access_preserves_cached_page(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        addr: Address,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::cache_access_label(reads, writes) is Access,
            Cache::State::next(pre.cache, post.cache, Self::cache_access_label(reads, writes)),
            post.disk == pre.disk,
            writes.contains_key(addr),
        ensures
            post.has_cached_page(addr),
            post.cache_raw_page(addr) == writes[addr],
            post.cache.status_map[post.cache.lookup_map[addr]] is Dirty,
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Self::cache_access_label(reads, writes);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        match step {
            Cache::Step::access() => {
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                let slot = pre.cache.lookup_map[addr];
                let updated_entries = pre.cache.write_updated_entries(writes);
                let updated_status_map = pre.cache.write_updated_status(writes);
                assert(pre.cache.lookup_map.restrict(writes.dom()).contains_key(addr));
                assert(pre.cache.lookup_map.restrict(writes.dom())[addr] == slot);
                assert(updated_entries.contains_key(slot));
                assert(updated_status_map.contains_key(slot));
                assert(post.cache.entries[slot] == updated_entries[slot]);
                assert(post.cache.status_map[slot] == updated_status_map[slot]);
                assert(updated_entries[slot] is Filled);
                assert(updated_entries[slot].get_addr() == addr);
                assert(post.has_cached_page(addr));
                assert(post.cache_raw_page(addr) == writes[addr]);
                assert(post.cache.status_map[slot] is Dirty);
            }
            _ => { assert(false); }
        }
    }

    pub proof fn access_unwritten_post_cached_page_is_pre_cached(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        addr: Address,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, post.cache, Self::cache_access_label(reads, writes)),
            post.disk == pre.disk,
            post.has_cached_page(addr),
            !writes.contains_key(addr),
        ensures
            pre.has_cached_page(addr),
            post.cache_raw_page(addr) == pre.cache_raw_page(addr),
            post.cache.status_map[post.cache.lookup_map[addr]] == pre.cache.status_map[pre.cache.lookup_map[addr]],
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Self::cache_access_label(reads, writes);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        match step {
            Cache::Step::access() => {
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                let slot = post.cache.lookup_map[addr];
                let updated_entries = pre.cache.write_updated_entries(writes);
                let updated_status_map = pre.cache.write_updated_status(writes);
                pre.cache.build_lookup_map_ensures();
                assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                assert(!updated_entries.contains_key(slot)) by {
                    if updated_entries.contains_key(slot) {
                        let write_addr = choose |write_addr: Address|
                            #![trigger pre.cache.lookup_map.restrict(writes.dom())[write_addr]]
                            pre.cache.lookup_map.restrict(writes.dom()).contains_key(write_addr)
                            && pre.cache.lookup_map.restrict(writes.dom())[write_addr] == slot;
                        assert(pre.cache.lookup_map.contains_key(write_addr));
                        assert(writes.contains_key(write_addr));
                        assert(pre.cache.lookup_map[write_addr] == slot);
                        assert(pre.cache.lookup_map.is_injective());
                        assert(write_addr == addr);
                        assert(false);
                    }
                };
                assert(!updated_status_map.contains_key(slot)) by {
                    if updated_status_map.contains_key(slot) {
                        let write_addr = choose |write_addr: Address|
                            #![trigger pre.cache.lookup_map.restrict(writes.dom())[write_addr]]
                            pre.cache.lookup_map.restrict(writes.dom()).contains_key(write_addr)
                            && pre.cache.lookup_map.restrict(writes.dom())[write_addr] == slot;
                        assert(pre.cache.lookup_map.contains_key(write_addr));
                        assert(writes.contains_key(write_addr));
                        assert(pre.cache.lookup_map[write_addr] == slot);
                        assert(pre.cache.lookup_map.is_injective());
                        assert(write_addr == addr);
                        assert(false);
                    }
                };
                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                assert(pre.cache.entries[slot] is Filled);
                assert(pre.has_cached_page(addr));
                assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
            }
            _ => { assert(false); }
        }
    }

    pub proof fn access_unwritten_pre_cached_page_stays_cached(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        addr: Address,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, post.cache, Self::cache_access_label(reads, writes)),
            post.disk == pre.disk,
            pre.has_cached_page(addr),
            !writes.contains_key(addr),
        ensures
            post.has_cached_page(addr),
            post.cache_raw_page(addr) == pre.cache_raw_page(addr),
            post.cache.status_map[post.cache.lookup_map[addr]] == pre.cache.status_map[pre.cache.lookup_map[addr]],
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Self::cache_access_label(reads, writes);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        match step {
            Cache::Step::access() => {
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                let slot = pre.cache.lookup_map[addr];
                let updated_entries = pre.cache.write_updated_entries(writes);
                let updated_status_map = pre.cache.write_updated_status(writes);
                pre.cache.build_lookup_map_ensures();
                assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                assert(!updated_entries.contains_key(slot)) by {
                    if updated_entries.contains_key(slot) {
                        let write_addr = choose |write_addr: Address|
                            #![trigger pre.cache.lookup_map.restrict(writes.dom())[write_addr]]
                            pre.cache.lookup_map.restrict(writes.dom()).contains_key(write_addr)
                            && pre.cache.lookup_map.restrict(writes.dom())[write_addr] == slot;
                        assert(pre.cache.lookup_map.restrict(writes.dom()).contains_key(write_addr));
                        assert(pre.cache.lookup_map.contains_key(write_addr));
                        assert(pre.cache.lookup_map[write_addr] == slot);
                        assert(pre.cache.entries[slot].get_addr() == addr);
                        assert(pre.cache.entries[slot].get_addr() == write_addr);
                        assert(write_addr == addr);
                        assert(false);
                    }
                };
                assert(!updated_status_map.contains_key(slot)) by {
                    if updated_status_map.contains_key(slot) {
                        let write_addr = choose |write_addr: Address|
                            #![trigger pre.cache.lookup_map.restrict(writes.dom())[write_addr]]
                            pre.cache.lookup_map.restrict(writes.dom()).contains_key(write_addr)
                            && pre.cache.lookup_map.restrict(writes.dom())[write_addr] == slot;
                        assert(pre.cache.lookup_map.restrict(writes.dom()).contains_key(write_addr));
                        assert(pre.cache.lookup_map.contains_key(write_addr));
                        assert(pre.cache.lookup_map[write_addr] == slot);
                        assert(pre.cache.entries[slot].get_addr() == addr);
                        assert(pre.cache.entries[slot].get_addr() == write_addr);
                        assert(write_addr == addr);
                        assert(false);
                    }
                };
                assert(post.has_cached_page(addr));
                assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                assert(post.cache.status_map[post.cache.lookup_map[addr]] == pre.cache.status_map[pre.cache.lookup_map[addr]]);
            }
            _ => { assert(false); }
        }
    }

    proof fn access_preserves_unwritten_lookup_slot(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        addr: Address,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, post.cache, Self::cache_access_label(reads, writes)),
            post.disk == pre.disk,
            pre.outstanding_cache_reqs == post.outstanding_cache_reqs,
            pre.cache.lookup_map.contains_key(addr),
            !writes.contains_key(addr),
        ensures
            post.cache.lookup_map.contains_key(addr),
            post.cache.lookup_map[addr] == pre.cache.lookup_map[addr],
            post.cache.entries[post.cache.lookup_map[addr]] == pre.cache.entries[pre.cache.lookup_map[addr]],
            post.cache.status_map[post.cache.lookup_map[addr]] == pre.cache.status_map[pre.cache.lookup_map[addr]],
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Self::cache_access_label(reads, writes);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        match step {
            Cache::Step::access() => {
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                let slot = pre.cache.lookup_map[addr];
                let updated_entries = pre.cache.write_updated_entries(writes);
                let updated_status_map = pre.cache.write_updated_status(writes);
                pre.cache.build_lookup_map_ensures();
                assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                assert(!updated_entries.contains_key(slot)) by {
                    if updated_entries.contains_key(slot) {
                        let write_addr = choose |write_addr: Address|
                            #![trigger pre.cache.lookup_map.restrict(writes.dom())[write_addr]]
                            pre.cache.lookup_map.restrict(writes.dom()).contains_key(write_addr)
                            && pre.cache.lookup_map.restrict(writes.dom())[write_addr] == slot;
                        assert(pre.cache.lookup_map.contains_key(write_addr));
                        assert(writes.contains_key(write_addr));
                        assert(pre.cache.lookup_map[write_addr] == slot);
                        assert(pre.cache.lookup_map.is_injective());
                        assert(write_addr == addr);
                        assert(false);
                    }
                };
                assert(!updated_status_map.contains_key(slot)) by {
                    if updated_status_map.contains_key(slot) {
                        let write_addr = choose |write_addr: Address|
                            #![trigger pre.cache.lookup_map.restrict(writes.dom())[write_addr]]
                            pre.cache.lookup_map.restrict(writes.dom()).contains_key(write_addr)
                            && pre.cache.lookup_map.restrict(writes.dom())[write_addr] == slot;
                        assert(pre.cache.lookup_map.contains_key(write_addr));
                        assert(writes.contains_key(write_addr));
                        assert(pre.cache.lookup_map[write_addr] == slot);
                        assert(pre.cache.lookup_map.is_injective());
                        assert(write_addr == addr);
                        assert(false);
                    }
                };
                assert(post.cache.lookup_map.contains_key(addr));
                assert(post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]);
                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
            }
            _ => { assert(false); }
        }
    }

    proof fn access_preserves_cache_agrees_with_disk(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, post.cache, Self::cache_access_label(reads, writes)),
            post.disk == pre.disk,
        ensures
            forall |addr: Address|
                #![trigger post.has_cached_page(addr)]
                #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                post.has_cached_page(addr)
                && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                ==> {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                },
    {
        assert forall |addr: Address|
            #![trigger post.has_cached_page(addr)]
            #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
            post.has_cached_page(addr)
            && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
        implies {
            &&& post.disk.content.contains_key(addr)
            &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
        } by {
            if writes.contains_key(addr) {
                Self::access_preserves_cached_page(pre, post, reads, writes, addr);
                assert(post.cache.status_map[post.cache.lookup_map[addr]] is Dirty);
                assert(false);
            }
            Self::access_unwritten_post_cached_page_is_pre_cached(pre, post, reads, writes, addr);
            assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Clean);
            Self::clean_cached_page_matches_disk(pre, addr);
            assert(post.disk.content == pre.disk.content);
            assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
        };
    }

    proof fn internal_cache_preserves_cache_agrees_with_disk(
        pre: Self,
        post: Self,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{}),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == new_cache,
            post.disk == pre.disk,
            post.cache.inv(),
        ensures
            forall |addr: Address|
                #![trigger post.has_cached_page(addr)]
                #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                post.has_cached_page(addr)
                && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                ==> {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                },
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, Cache::Label::Internal{}, step);
        match step {
            Cache::Step::reserve(new_slots_mapping) => {
                assert forall |addr: Address|
                    #![trigger post.has_cached_page(addr)]
                    #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                    post.has_cached_page(addr)
                    && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    Self::cache_has_cached_page_gets_addr(post.cache, addr);
                    let slot = post.cache.lookup_map[addr];
                    assert(!new_slots_mapping.contains_key(slot));
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    assert(pre.cache.entries[slot] is Filled);
                    assert(pre.cache.entries[slot].get_addr() == addr);
                    Self::cache_non_empty_slot_in_lookup(pre.cache, slot);
                    assert(pre.cache.lookup_map.contains_key(addr));
                    assert(pre.cache.lookup_map[addr] == slot);
                    assert(pre.has_cached_page(addr));
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Clean);
                    Self::clean_cached_page_matches_disk(pre, addr);
                    assert(post.disk.content == pre.disk.content);
                    assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                };
            }
            Cache::Step::evict(evicted_slots) => {
                assert forall |addr: Address|
                    #![trigger post.has_cached_page(addr)]
                    #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                    post.has_cached_page(addr)
                    && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    Self::cache_has_cached_page_gets_addr(post.cache, addr);
                    let slot = post.cache.lookup_map[addr];
                    assert(!evicted_slots.contains(slot));
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    assert(pre.cache.entries[slot] is Filled);
                    assert(pre.cache.entries[slot].get_addr() == addr);
                    Self::cache_non_empty_slot_in_lookup(pre.cache, slot);
                    assert(pre.cache.lookup_map.contains_key(addr));
                    assert(pre.cache.lookup_map[addr] == slot);
                    assert(pre.has_cached_page(addr));
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Clean);
                    Self::clean_cached_page_matches_disk(pre, addr);
                    assert(post.disk.content == pre.disk.content);
                    assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                };
            }
            Cache::Step::noop() => {
                assert(post.cache == pre.cache);
                assert forall |addr: Address|
                    post.has_cached_page(addr) && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    assert(post.disk == pre.disk);
                }
            }
            _ => { assert(false); }
        }
    }

    proof fn access_preserves_outstanding_reqs_consistent(
        pre: Self,
        post: Self,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, post.cache, Self::cache_access_label(reads, writes)),
            post.disk == pre.disk,
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
            post.cache.inv(),
        ensures
            post.outstanding_reqs_consistent(),
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Self::cache_access_label(reads, writes);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        match step {
            Cache::Step::access() => {
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.outstanding_cache_reqs.is_injective());
                assert(post.disk.requests.dom() + post.disk.responses.dom() == post.outstanding_cache_reqs.dom());
                assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id) implies {
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
                    assert(pre.disk.requests.contains_key(id));
                    let req = pre.disk.requests[id];
                    let addr = pre.outstanding_cache_reqs[id];
                    let slot = pre.cache.lookup_map[addr];
                    if writes.contains_key(addr) {
                        assert(pre.cache.valid_write(addr));
                        if req is ReadReq {
                            assert(pre.cache.entries[slot] is Loading);
                            assert(false);
                        }
                        assert(req is WriteReq);
                        assert(pre.cache.status_map[slot] is Writeback);
                        assert(false);
                    }
                    Self::access_preserves_unwritten_lookup_slot(pre, post, reads, writes, addr);
                };
                assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id) implies {
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
                    let resp = pre.disk.responses[id];
                    let addr = pre.outstanding_cache_reqs[id];
                    let slot = pre.cache.lookup_map[addr];
                    if writes.contains_key(addr) {
                        assert(pre.cache.valid_write(addr));
                        if resp is ReadResp {
                            assert(pre.cache.entries[slot] is Loading);
                            assert(false);
                        }
                        assert(resp is WriteResp);
                        assert(pre.cache.status_map[slot] is Writeback);
                        assert(false);
                    }
                    Self::access_preserves_unwritten_lookup_slot(pre, post, reads, writes, addr);
                    assert(post.disk.content == pre.disk.content);
                };
                assert forall |id: ID|
                    #![trigger post.disk.requests.contains_key(id)]
                    #![trigger post.disk.responses.contains_key(id)]
                    (post.disk.requests.contains_key(id) || post.disk.responses.contains_key(id))
                    implies post.io_id_valid(id) by {
                    assert(pre.io_id_valid(id));
                    assert(post.disk == pre.disk);
                    let addr = post.outstanding_cache_reqs[id];
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.entries.contains_key(post.cache.lookup_map[addr]));
                    assert(post.cache.status_map.contains_key(post.cache.lookup_map[addr]));
                    if post.disk.responses.contains_key(id) {
                        assert(pre.disk.responses.contains_key(id));
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                    if post.disk.requests.contains_key(id) {
                        assert(pre.disk.requests.contains_key(id));
                        if pre.disk.requests[id] is ReadReq {
                            assert(pre.disk.content.contains_key(addr));
                            assert(post.disk.content.contains_key(addr));
                        }
                    }
                };
            }
            _ => { assert(false); }
        }
    }

    proof fn internal_cache_preserves_outstanding_reqs_consistent(
        pre: Self,
        post: Self,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{}),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == new_cache,
            post.disk == pre.disk,
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
            post.cache.inv(),
        ensures
            post.outstanding_reqs_consistent(),
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let step = choose |step| Cache::State::next_by(pre.cache, post.cache, Cache::Label::Internal{}, step);
        match step {
            Cache::Step::reserve(new_slots_mapping) => {
                assert(post.outstanding_cache_reqs.is_injective());
                assert(post.disk.requests.dom() + post.disk.responses.dom() == post.outstanding_cache_reqs.dom());
                assert forall |id: ID|
                    #![trigger post.disk.requests.contains_key(id)]
                    post.disk.requests.contains_key(id)
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
                    assert(pre.disk.requests.contains_key(id));
                    let addr = pre.outstanding_cache_reqs[id];
                    assert(pre.io_id_valid(id));
                    assert(pre.cache.lookup_map.contains_key(addr));
                    Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                    assert(!new_slots_mapping.contains_value(addr));
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]);
                    let slot = pre.cache.lookup_map[addr];
                    assert(!new_slots_mapping.contains_key(slot));
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                };
                assert forall |id: ID|
                    #![trigger post.disk.responses.contains_key(id)]
                    post.disk.responses.contains_key(id)
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
                    let addr = pre.outstanding_cache_reqs[id];
                    assert(pre.io_id_valid(id));
                    Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                    assert(!new_slots_mapping.contains_value(addr));
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]);
                    let slot = pre.cache.lookup_map[addr];
                    assert(!new_slots_mapping.contains_key(slot));
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    assert(post.disk.content == pre.disk.content);
                };
                assert forall |id: ID|
                    #![trigger post.disk.requests.contains_key(id)]
                    #![trigger post.disk.responses.contains_key(id)]
                    (post.disk.requests.contains_key(id) || post.disk.responses.contains_key(id))
                    implies post.io_id_valid(id) by {
                    assert(pre.io_id_valid(id));
                    assert(post.disk == pre.disk);
                    let addr = post.outstanding_cache_reqs[id];
                    let slot = pre.cache.lookup_map[addr];
                    Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    Self::cache_non_empty_slot_in_lookup(post.cache, slot);
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.lookup_map[addr] == slot);
                    assert(post.cache.entries.contains_key(post.cache.lookup_map[addr]));
                    assert(post.cache.status_map.contains_key(post.cache.lookup_map[addr]));
                    if post.disk.responses.contains_key(id) {
                        assert(pre.disk.responses.contains_key(id));
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                    if post.disk.requests.contains_key(id) {
                        assert(pre.disk.requests.contains_key(id));
                        if pre.disk.requests[id] is ReadReq {
                            assert(pre.disk.content.contains_key(addr));
                            assert(post.disk.content.contains_key(addr));
                        }
                    }
                };
            }
            Cache::Step::evict(evicted_slots) => {
                assert(post.outstanding_cache_reqs.is_injective());
                assert(post.disk.requests.dom() + post.disk.responses.dom() == post.outstanding_cache_reqs.dom());
                assert forall |id: ID|
                    #![trigger post.disk.requests.contains_key(id)]
                    post.disk.requests.contains_key(id)
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
                    assert(pre.disk.requests.contains_key(id));
                    let addr = pre.outstanding_cache_reqs[id];
                    let req = pre.disk.requests[id];
                    let slot = pre.cache.lookup_map[addr];
                    Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                    if req is ReadReq {
                        assert(pre.cache.entries[slot] is Loading);
                    } else {
                        assert(pre.cache.status_map[slot] is Writeback);
                    }
                    assert(!evicted_slots.contains(slot));
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    Self::cache_non_empty_slot_in_lookup(post.cache, slot);
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.lookup_map[addr] == slot);
                };
                assert forall |id: ID|
                    #![trigger post.disk.responses.contains_key(id)]
                    post.disk.responses.contains_key(id)
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
                    let addr = pre.outstanding_cache_reqs[id];
                    let resp = pre.disk.responses[id];
                    let slot = pre.cache.lookup_map[addr];
                    Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                    if resp is ReadResp {
                        assert(pre.cache.entries[slot] is Loading);
                    } else {
                        assert(pre.cache.status_map[slot] is Writeback);
                    }
                    assert(!evicted_slots.contains(slot));
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    Self::cache_non_empty_slot_in_lookup(post.cache, slot);
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.lookup_map[addr] == slot);
                    assert(post.disk.content == pre.disk.content);
                };
                assert forall |id: ID|
                    #![trigger post.disk.requests.contains_key(id)]
                    #![trigger post.disk.responses.contains_key(id)]
                    (post.disk.requests.contains_key(id) || post.disk.responses.contains_key(id))
                    implies post.io_id_valid(id) by {
                    assert(pre.io_id_valid(id));
                    assert(post.disk == pre.disk);
                    let addr = post.outstanding_cache_reqs[id];
                    let slot = pre.cache.lookup_map[addr];
                    Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    Self::cache_non_empty_slot_in_lookup(post.cache, slot);
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.lookup_map[addr] == slot);
                    assert(post.cache.entries.contains_key(post.cache.lookup_map[addr]));
                    assert(post.cache.status_map.contains_key(post.cache.lookup_map[addr]));
                    if post.disk.responses.contains_key(id) {
                        assert(pre.disk.responses.contains_key(id));
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                    if post.disk.requests.contains_key(id) {
                        assert(pre.disk.requests.contains_key(id));
                        if pre.disk.requests[id] is ReadReq {
                            assert(pre.disk.content.contains_key(addr));
                            assert(post.disk.content.contains_key(addr));
                        }
                    }
                };
            }
            Cache::Step::noop() => {
                assert(post.cache == pre.cache);
                assert(post.outstanding_reqs_consistent());
            }
            _ => { assert(false); }
        }
    }

    proof fn internal_disk_preserves_outstanding_reqs_consistent(
        pre: Self,
        post: Self,
        new_disk: AsyncDisk::State,
    )
        requires
            pre.wf(),
            AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{}),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == pre.cache,
            post.disk == new_disk,
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        ensures
            post.outstanding_reqs_consistent(),
    {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |dstep| AsyncDisk::State::next_by(pre.disk, post.disk, AsyncDisk::Label::Internal{}, dstep);
        assert(post.outstanding_cache_reqs.is_injective());
        match disk_step {
            AsyncDisk::Step::process_read(id) => {
                assert(pre.outstanding_reqs_requests_ok());
                assert(pre.outstanding_reqs_responses_ok());
                assert(post.disk.requests == pre.disk.requests.remove(id));
                assert(post.disk.responses == pre.disk.responses.insert(id, post.disk.responses[id]));
                assert(post.disk.requests.dom() + post.disk.responses.dom()
                    == pre.disk.requests.dom() + pre.disk.responses.dom());

                assert forall |id2: ID| #[trigger] post.disk.requests.contains_key(id2) implies {
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
                };

                assert forall |id2: ID| #[trigger] post.disk.responses.contains_key(id2) implies {
                    let resp = post.disk.responses[id2];
                    let addr = post.outstanding_cache_reqs[id2];
                    &&& post.outstanding_cache_reqs.contains_key(id2)
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
                    if id2 == id {
                        let addr = post.outstanding_cache_reqs[id];
                        assert(pre.io_id_valid(id));
                        assert(post.disk.responses[id] is ReadResp);
                        assert(pre.disk.requests[id] is ReadReq);
                        assert(post.disk.responses[id]->data == pre.disk.content[pre.disk.requests[id]->from]);
                        assert(pre.disk.requests[id]->from == addr);
                        assert(post.disk.content == pre.disk.content);
                        let slot = post.cache.lookup_map[addr];
                        assert(post.cache.entries[slot] is Loading);
                    } else {
                        vstd::map::axiom_map_insert_different(pre.disk.responses, id2, id, post.disk.responses[id]);
                        assert(pre.disk.responses.contains_key(id2));
                    }
                };

                assert forall |id2: ID|
                    #![trigger post.disk.requests.contains_key(id2)]
                    #![trigger post.disk.responses.contains_key(id2)]
                    (post.disk.requests.contains_key(id2) || post.disk.responses.contains_key(id2))
                    implies post.io_id_valid(id2) by {
                    if id2 == id {
                        let addr = post.outstanding_cache_reqs[id];
                        assert(pre.io_id_valid(id));
                        assert(post.disk.responses.contains_key(id));
                        assert(post.disk.content == pre.disk.content);
                        assert(post.cache.lookup_map.contains_key(addr));
                        assert(post.cache.entries.contains_key(post.cache.lookup_map[addr]));
                        assert(post.cache.status_map.contains_key(post.cache.lookup_map[addr]));
                        assert(post.disk.content.contains_key(addr));
                    } else {
                        assert(pre.io_id_valid(id2));
                    }
                };
            }
            AsyncDisk::Step::process_write(id) => {
                assert(pre.outstanding_reqs_requests_ok());
                assert(pre.outstanding_reqs_responses_ok());
                let write_addr = pre.disk.requests[id]->to;
                assert(post.disk.requests == pre.disk.requests.remove(id));
                assert(post.disk.responses == pre.disk.responses.insert(id, DiskResponse::WriteResp{}));
                assert(post.disk.content == pre.disk.content.insert(write_addr, pre.disk.requests[id]->data));
                assert(post.disk.requests.dom() + post.disk.responses.dom()
                    == pre.disk.requests.dom() + pre.disk.responses.dom());

                assert forall |id2: ID| #[trigger] post.disk.requests.contains_key(id2) implies {
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
                };

                assert forall |id2: ID| #[trigger] post.disk.responses.contains_key(id2) implies {
                    let resp = post.disk.responses[id2];
                    let addr = post.outstanding_cache_reqs[id2];
                    &&& post.outstanding_cache_reqs.contains_key(id2)
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
                    if id2 == id {
                        let addr = post.outstanding_cache_reqs[id];
                        let slot = post.cache.lookup_map[addr];
                        assert(pre.disk.requests[id] is WriteReq);
                        assert(addr == write_addr);
                        assert(pre.cache.status_map[slot] is Writeback);
                        assert(pre.cache.entries[slot] == Entry::Filled{addr, data: pre.disk.requests[id]->data});
                        assert(post.cache.entries[slot] == Entry::Filled{addr, data: post.disk.content[addr]});
                    } else {
                        vstd::map::axiom_map_insert_different(pre.disk.responses, id2, id, DiskResponse::WriteResp{});
                        assert(pre.disk.responses.contains_key(id2));
                        assert(post.disk.content[post.outstanding_cache_reqs[id2]] == pre.disk.content[pre.outstanding_cache_reqs[id2]]) by {
                            if post.outstanding_cache_reqs[id2] == write_addr {
                                assert(pre.outstanding_cache_reqs[id2] == pre.outstanding_cache_reqs[id]);
                                assert(pre.outstanding_cache_reqs.is_injective());
                                assert(id2 == id);
                                assert(false);
                            }
                        };
                    }
                };

                assert forall |id2: ID|
                    #![trigger post.disk.requests.contains_key(id2)]
                    #![trigger post.disk.responses.contains_key(id2)]
                    (post.disk.requests.contains_key(id2) || post.disk.responses.contains_key(id2))
                    implies post.io_id_valid(id2) by {
                    if id2 == id {
                        let addr = post.outstanding_cache_reqs[id];
                        let slot = post.cache.lookup_map[addr];
                        assert(addr == write_addr);
                        assert(post.cache.entries.contains_key(slot));
                        assert(post.cache.status_map.contains_key(slot));
                        assert(post.disk.content.contains_key(addr));
                    } else {
                        assert(pre.io_id_valid(id2));
                        if post.outstanding_cache_reqs[id2] == write_addr {
                            assert(pre.outstanding_cache_reqs[id2] == pre.outstanding_cache_reqs[id]);
                            assert(pre.outstanding_cache_reqs.is_injective());
                            assert(id2 == id);
                            assert(false);
                        }
                    }
                };
            }
            _ => { assert(false); }
        }
    }

    proof fn internal_disk_preserves_cache_agrees_with_disk(
        pre: Self,
        post: Self,
        new_disk: AsyncDisk::State,
    )
        requires
            pre.wf(),
            AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{}),
            post.cached_branch == pre.cached_branch,
            post.mini_allocator == pre.mini_allocator,
            post.cache == pre.cache,
            post.disk == new_disk,
            post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
        ensures
            forall |addr: Address|
                #![trigger post.has_cached_page(addr)]
                #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                post.has_cached_page(addr)
                && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                ==> {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                },
    {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |dstep| AsyncDisk::State::next_by(pre.disk, post.disk, AsyncDisk::Label::Internal{}, dstep);
        match disk_step {
            AsyncDisk::Step::process_read(id) => {
                assert(post.disk.content == pre.disk.content);
                assert forall |addr: Address|
                    post.has_cached_page(addr) && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    assert(post.cache == pre.cache);
                }
            }
            AsyncDisk::Step::process_write(id) => {
                assert(pre.outstanding_reqs_requests_ok());
                let write_addr = pre.disk.requests[id]->to;
                assert forall |addr: Address|
                    post.has_cached_page(addr)
                    && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    if addr == write_addr {
                        let slot = pre.cache.lookup_map[addr];
                        assert(pre.outstanding_reqs_requests_ok());
                        assert(pre.disk.requests.contains_key(id));
                        assert(pre.disk.requests[id].addr() == addr);
                        assert(pre.cache.status_map[slot] is Writeback);
                    assert(post.cache.status_map[post.cache.lookup_map[addr]] is Clean);
                    assert(post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]);
                    assert(false);
                }
                assert(post.disk.content[addr] == pre.disk.content[addr]);
                assert(pre.has_cached_page(addr));
                assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Clean);
                Self::clean_cached_page_matches_disk(pre, addr);
                assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
            };
        }
            _ => { assert(false); }
        }
    }

    proof fn internal_disk_preserves_wf(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        new_disk: AsyncDisk::State,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::internal_disk(pre, post, lbl, new_disk),
        ensures
            post.wf(),
    {
        reveal(ConcreteBranch::State::internal_disk);
        assert(lbl is Internal);
        assert(post.cached_branch == pre.cached_branch);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.cache == pre.cache);
        assert(post.cache.inv());
        assert(post.disk == new_disk);
        Self::disk_internal_preserves_inv(pre, post.disk);
        assert(post.disk.inv());
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        Self::internal_disk_preserves_outstanding_reqs_consistent(pre, post, new_disk);
        Self::internal_disk_preserves_cache_agrees_with_disk(pre, post, new_disk);
        assert(post.cache_agrees_with_disk());
        assert(post.wf());
    }

    proof fn cache_disk_ops_preserves_unaffected_lookup_slot(
        pre: Self,
        post: Self,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        addr: Address,
    )
        requires
            pre.wf(),
            Cache::State::next(
                pre.cache,
                post.cache,
                Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses},
            ),
            pre.cache.lookup_map.contains_key(addr),
            !cache_responses.contains_key(addr),
            forall |req: DiskRequest| #[trigger] cache_requests.contains(req) ==> req.addr() != addr,
            post.cache.inv(),
        ensures
            post.cache.lookup_map.contains_key(addr),
            post.cache.lookup_map[addr] == pre.cache.lookup_map[addr],
            post.cache.entries[post.cache.lookup_map[addr]] == pre.cache.entries[pre.cache.lookup_map[addr]],
            post.cache.status_map[post.cache.lookup_map[addr]] == pre.cache.status_map[pre.cache.lookup_map[addr]],
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        let slot = pre.cache.lookup_map[addr];
        Self::cache_lookup_slot_gets_addr(pre.cache, addr);
        match cache_step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                assert(pre.cache.valid_new_slots_mapping(new_slots_mapping));
                assert(Cache::State::valid_load_requests(cache_requests, new_slots_mapping));
                assert(post.cache.entries == pre.cache.entries.union_prefer_right(Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Loading{addr: new_slots_mapping[slot]}
                )));
                assert(post.cache.lookup_map == pre.cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                assert(post.cache.status_map == pre.cache.status_map);
                assert(!new_slots_mapping.contains_value(addr)) by {
                    if new_slots_mapping.contains_value(addr) {
                        let req = choose |req: DiskRequest|
                            #[trigger] crate::implementation::Cache_v::addr_maps_to_req(cache_requests, req, addr);
                        assert(cache_requests.contains(req));
                        assert(req.addr() == addr);
                        assert(false);
                    }
                };
                assert(!new_slots_mapping.invert().contains_key(addr)) by {
                    if new_slots_mapping.invert().contains_key(addr) {
                        reveal(Map::invert);
                        assert(new_slots_mapping.contains_value(addr));
                        assert(false);
                    }
                };
                assert(post.cache.lookup_map.contains_key(addr));
                assert(post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]);
                assert(!new_slots_mapping.contains_key(slot)) by {
                    if new_slots_mapping.contains_key(slot) {
                        assert(pre.cache.entries[slot] is Empty);
                        assert(pre.cache.entries[slot] is Filled);
                        assert(false);
                    }
                };
                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
            }
            Cache::Step::load_complete() => {
                let slot_addr_map = pre.cache.lookup_map.restrict(cache_responses.dom()).invert();
                let updated_entries = Map::new(
                    |slot| slot_addr_map.contains_key(slot),
                    |slot| Entry::Filled{
                        addr: slot_addr_map[slot],
                        data: cache_responses[slot_addr_map[slot]]->data
                    }
                );
                let updated_status_map = Map::new(
                    |slot| slot_addr_map.contains_key(slot),
                    |slot| Status::Clean
                );
                assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                if slot_addr_map.contains_key(slot) {
                    let resp_addr = choose |resp_addr: Address|
                        #![trigger pre.cache.lookup_map.restrict(cache_responses.dom())[resp_addr]]
                        pre.cache.lookup_map.restrict(cache_responses.dom()).contains_key(resp_addr)
                        && pre.cache.lookup_map.restrict(cache_responses.dom())[resp_addr] == slot;
                    assert(pre.cache.lookup_map.contains_key(resp_addr));
                    assert(pre.cache.lookup_map[resp_addr] == slot);
                    pre.cache.build_lookup_map_ensures();
                    assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                    assert(pre.cache.lookup_map.is_injective());
                    assert(resp_addr == addr) by {
                        if resp_addr != addr {
                            assert(pre.cache.lookup_map[resp_addr] != pre.cache.lookup_map[addr]);
                            assert(false);
                        }
                    };
                    assert(cache_responses.contains_key(addr));
                    assert(false);
                }
                assert(!updated_entries.contains_key(slot));
                assert(!updated_status_map.contains_key(slot));
                assert(post.cache.lookup_map.contains_key(addr));
                assert(post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]);
                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
            }
            Cache::Step::writeback_initiate() => {
                let writeback_slots = Map::new(
                    |req: DiskRequest| cache_requests.contains(req),
                    |req: DiskRequest| pre.cache.lookup_map[req->to]
                ).values();
                let updated_status_map = Map::new(
                    |slot| writeback_slots.contains(slot),
                    |slot| Status::Writeback
                );
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.cache.entries == pre.cache.entries);
                assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                if writeback_slots.contains(slot) {
                    let req = choose |req: DiskRequest|
                        #![trigger cache_requests.contains(req)]
                        cache_requests.contains(req) && pre.cache.lookup_map[req->to] == slot;
                    assert(cache_requests.contains(req));
                    assert(pre.cache.lookup_map[req->to] == slot);
                    pre.cache.build_lookup_map_ensures();
                    assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                    assert(pre.cache.lookup_map.is_injective());
                    assert(req->to == addr) by {
                        if req->to != addr {
                            assert(pre.cache.lookup_map[req->to] != pre.cache.lookup_map[addr]);
                            assert(false);
                        }
                    };
                    assert(req.addr() == addr);
                    assert(false);
                }
                assert(!updated_status_map.contains_key(slot));
                assert(post.cache.lookup_map.contains_key(addr));
                assert(post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]);
                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
            }
            Cache::Step::writeback_complete() => {
                let resp_slots = pre.cache.lookup_map.restrict(cache_responses.dom()).values();
                let updated_status_map = Map::new(
                    |slot| resp_slots.contains(slot),
                    |slot| Status::Clean
                );
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.cache.entries == pre.cache.entries);
                assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                if resp_slots.contains(slot) {
                    let resp_addr = choose |resp_addr: Address|
                        #![trigger pre.cache.lookup_map.restrict(cache_responses.dom())[resp_addr]]
                        pre.cache.lookup_map.restrict(cache_responses.dom()).contains_key(resp_addr)
                        && pre.cache.lookup_map.restrict(cache_responses.dom())[resp_addr] == slot;
                    assert(pre.cache.lookup_map.contains_key(resp_addr));
                    assert(pre.cache.lookup_map[resp_addr] == slot);
                    pre.cache.build_lookup_map_ensures();
                    assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                    assert(pre.cache.lookup_map.is_injective());
                    assert(resp_addr == addr) by {
                        if resp_addr != addr {
                            assert(pre.cache.lookup_map[resp_addr] != pre.cache.lookup_map[addr]);
                            assert(false);
                        }
                    };
                    assert(cache_responses.contains_key(addr));
                    assert(false);
                }
                assert(!updated_status_map.contains_key(slot));
                assert(post.cache.lookup_map.contains_key(addr));
                assert(post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]);
                assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
            }
            _ => { assert(false); }
        }
    }

    proof fn cache_disk_ops_preserves_clean_pages_match_disk(
        pre: Self,
        post: Self,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            pre.wf(),
            pre.disk_requests_match_cache_requests(cache_requests, disk_requests),
            pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
            Cache::State::next(pre.cache, post.cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses}),
            AsyncDisk::State::next(pre.disk, post.disk, AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses}),
            post.cache.inv(),
            post.disk.inv(),
        ensures
            forall |addr: Address|
                #![trigger post.has_cached_page(addr)]
                #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                post.has_cached_page(addr)
                && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                ==> {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                },
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        let disk_step = choose |step| AsyncDisk::State::next_by(
            pre.disk,
            post.disk,
            AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses},
            step,
        );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {
                assert(post.disk.content == pre.disk.content);
            }
            _ => { assert(false); }
        }

        match cache_step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                assert forall |addr: Address|
                    #![trigger post.has_cached_page(addr)]
                    #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                    post.has_cached_page(addr)
                    && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    Self::cache_has_cached_page_gets_addr(post.cache, addr);
                    let slot = post.cache.lookup_map[addr];
                    assert(!new_slots_mapping.contains_key(slot)) by {
                        if new_slots_mapping.contains_key(slot) {
                            assert(post.cache.entries[slot] is Loading);
                            assert(post.cache.entries[slot] is Filled);
                            assert(false);
                        }
                    };
                    assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    Self::cache_non_empty_slot_in_lookup(pre.cache, slot);
                    assert(pre.cache.lookup_map.contains_key(addr));
                    assert(pre.cache.lookup_map[addr] == slot);
                    assert(pre.has_cached_page(addr));
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Clean);
                    Self::clean_cached_page_matches_disk(pre, addr);
                    assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                    assert(post.disk.content.contains_key(addr));
                };
            }
            Cache::Step::load_complete() => {
                let slot_addr_map = pre.cache.lookup_map.restrict(cache_responses.dom()).invert();
                let updated_entries = Map::new(
                    |slot| slot_addr_map.contains_key(slot),
                    |slot| Entry::Filled{
                        addr: slot_addr_map[slot],
                        data: cache_responses[slot_addr_map[slot]]->data
                    }
                );
                let updated_status_map = Map::new(
                    |slot| slot_addr_map.contains_key(slot),
                    |slot| Status::Clean
                );
                assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert forall |addr: Address|
                    #![trigger post.has_cached_page(addr)]
                    #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                    post.has_cached_page(addr)
                    && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    let slot = post.cache.lookup_map[addr];
                    if cache_responses.contains_key(addr) {
                        let restricted_lookup = pre.cache.lookup_map.restrict(cache_responses.dom());
                        assert(pre.cache.lookup_map.contains_key(addr));
                        assert(slot == pre.cache.lookup_map[addr]);
                        assert(restricted_lookup.contains_key(addr));
                        assert(restricted_lookup[addr] == slot);
                        assert(slot_addr_map.contains_key(slot));
                        assert(restricted_lookup.contains_value(slot));
                        invert_contains_pair(restricted_lookup, slot);
                        let resp_addr = slot_addr_map[slot];
                        assert(restricted_lookup.contains_pair(resp_addr, slot));
                        assert(restricted_lookup.contains_key(resp_addr));
                        assert(restricted_lookup[resp_addr] == slot);
                        pre.cache.build_lookup_map_ensures();
                        assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                        assert(pre.cache.lookup_map.is_injective());
                        assert(pre.cache.lookup_map[resp_addr] == slot);
                        assert(resp_addr == addr) by {
                            if resp_addr != addr {
                                assert(pre.cache.lookup_map[resp_addr] != pre.cache.lookup_map[addr]);
                                assert(false);
                            }
                        };
                        assert(slot_addr_map[slot] == addr);
                        assert(post.cache.entries[slot] == updated_entries[slot]);
                        assert(post.cache.entries[slot] == Entry::Filled{addr, data: cache_responses[addr]->data});
                        assert(post.cache.status_map[slot] == updated_status_map[slot]);
                        assert(cache_responses[addr] is ReadResp);
                        let id = choose |id: ID| #[trigger] disk_responses.contains_key(id) && pre.outstanding_cache_reqs[id] == addr;
                        assert(pre.outstanding_cache_reqs.restrict(disk_responses.dom()).values().contains(addr));
                        assert(disk_responses.contains_key(id));
                        assert(pre.outstanding_cache_reqs[id] == addr);
                        assert(cache_responses[addr] == disk_responses[id]);
                        assert(pre.disk.responses.contains_key(id));
                        assert(pre.outstanding_reqs_responses_ok());
                        assert(pre.disk.responses[id] is ReadResp);
                        assert(pre.disk.responses[id]->data == pre.disk.content[addr]);
                        assert(post.cache_raw_page(addr) == cache_responses[addr]->data);
                        assert(post.disk.content.contains_key(addr));
                    } else {
                        if slot_addr_map.contains_key(slot) {
                            let resp_addr = choose |resp_addr: Address|
                                #![trigger pre.cache.lookup_map.restrict(cache_responses.dom())[resp_addr]]
                                pre.cache.lookup_map.restrict(cache_responses.dom()).contains_key(resp_addr)
                                && pre.cache.lookup_map.restrict(cache_responses.dom())[resp_addr] == slot;
                            assert(pre.cache.lookup_map.contains_key(resp_addr));
                            assert(pre.cache.lookup_map[resp_addr] == slot);
                            Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                            assert(pre.cache.lookup_map[addr] == slot);
                            pre.cache.build_lookup_map_ensures();
                            assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                            assert(pre.cache.lookup_map.is_injective());
                            assert(resp_addr == addr);
                            assert(cache_responses.contains_key(addr));
                            assert(false);
                        }
                        assert(!updated_entries.contains_key(slot));
                        assert(!updated_status_map.contains_key(slot));
                        Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                        assert(pre.cache.entries.contains_key(slot));
                        assert(pre.cache.status_map.contains_key(slot));
                        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                        assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                        assert(pre.has_cached_page(addr));
                        assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Clean);
                        Self::clean_cached_page_matches_disk(pre, addr);
                        assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                };
            }
            Cache::Step::writeback_initiate() => {
                let writeback_slots = Map::new(
                    |req: DiskRequest| cache_requests.contains(req),
                    |req: DiskRequest| pre.cache.lookup_map[req->to]
                ).values();
                let updated_status_map = Map::new(
                    |slot| writeback_slots.contains(slot),
                    |slot| Status::Writeback
                );
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.cache.entries == pre.cache.entries);
                assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                assert forall |addr: Address|
                    #![trigger post.has_cached_page(addr)]
                    #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                    post.has_cached_page(addr)
                    && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    let slot = post.cache.lookup_map[addr];
                    if writeback_slots.contains(slot) {
                        assert(post.cache.status_map[slot] is Writeback);
                        assert(false);
                    }
                    assert(!updated_status_map.contains_key(slot));
                    Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                    assert(pre.cache.entries.contains_key(slot));
                    assert(pre.cache.status_map.contains_key(slot));
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                    assert(pre.has_cached_page(addr));
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Clean);
                    Self::clean_cached_page_matches_disk(pre, addr);
                    assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                    assert(post.disk.content.contains_key(addr));
                };
            }
            Cache::Step::writeback_complete() => {
                let resp_slots = pre.cache.lookup_map.restrict(cache_responses.dom()).values();
                let updated_status_map = Map::new(
                    |slot| resp_slots.contains(slot),
                    |slot| Status::Clean
                );
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.cache.entries == pre.cache.entries);
                assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                assert forall |addr: Address|
                    #![trigger post.has_cached_page(addr)]
                    #![trigger post.cache.status_map[post.cache.lookup_map[addr]]]
                    post.has_cached_page(addr)
                    && post.cache.status_map[post.cache.lookup_map[addr]] is Clean
                implies {
                    &&& post.disk.content.contains_key(addr)
                    &&& post.cache_raw_page(addr) == #[trigger] post.disk.content[addr]
                } by {
                    let slot = post.cache.lookup_map[addr];
                    if cache_responses.contains_key(addr) {
                        assert(pre.cache.lookup_map.contains_key(addr));
                        assert(pre.cache.lookup_map[addr] == slot);
                        assert(cache_responses[addr] is WriteResp);
                        let id = choose |id: ID| #[trigger] disk_responses.contains_key(id) && pre.outstanding_cache_reqs[id] == addr;
                        assert(pre.outstanding_cache_reqs.restrict(disk_responses.dom()).values().contains(addr));
                        assert(disk_responses.contains_key(id));
                        assert(pre.outstanding_cache_reqs[id] == addr);
                        assert(cache_responses[addr] == disk_responses[id]);
                        assert(pre.disk.responses.contains_key(id));
                        assert(pre.outstanding_reqs_responses_ok());
                        assert(pre.disk.responses[id] is WriteResp);
                        assert(pre.cache.entries[slot] == Entry::Filled{addr, data: pre.disk.content[addr]});
                        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                        assert(post.cache_raw_page(addr) == pre.disk.content[addr]);
                        assert(post.disk.content == pre.disk.content);
                        assert(post.disk.content.contains_key(addr));
                    } else {
                        if resp_slots.contains(slot) {
                            let resp_addr = choose |resp_addr: Address|
                                #![trigger pre.cache.lookup_map.restrict(cache_responses.dom())[resp_addr]]
                                pre.cache.lookup_map.restrict(cache_responses.dom()).contains_key(resp_addr)
                                && pre.cache.lookup_map.restrict(cache_responses.dom())[resp_addr] == slot;
                            assert(pre.cache.lookup_map.contains_key(resp_addr));
                            assert(pre.cache.lookup_map[resp_addr] == slot);
                            Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                            assert(pre.cache.lookup_map[addr] == slot);
                            pre.cache.build_lookup_map_ensures();
                            assert(pre.cache.build_lookup_map_props(pre.cache.lookup_map));
                            assert(pre.cache.lookup_map.is_injective());
                            assert(resp_addr == addr);
                            assert(cache_responses.contains_key(addr));
                            assert(false);
                        }
                        assert(!updated_status_map.contains_key(slot));
                        Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                        assert(pre.cache.entries.contains_key(slot));
                        assert(pre.cache.status_map.contains_key(slot));
                        assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                        assert(pre.has_cached_page(addr));
                        assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Clean);
                        Self::clean_cached_page_matches_disk(pre, addr);
                        assert(post.cache_raw_page(addr) == pre.cache_raw_page(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                };
            }
            _ => { assert(false); }
        }
    }

    proof fn cache_disk_ops_preserves_outstanding_reqs_consistent(
        pre: Self,
        post: Self,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            pre.wf(),
            pre.disk_requests_match_cache_requests(cache_requests, disk_requests),
            pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
            Cache::State::next(pre.cache, post.cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses}),
            AsyncDisk::State::next(pre.disk, post.disk, AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses}),
            post.cache.inv(),
            post.disk.inv(),
            post.outstanding_cache_reqs == pre.next_outstanding_cache_reqs(disk_requests, disk_responses),
        ensures
            post.outstanding_reqs_consistent(),
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_lbl = AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        let disk_step = choose |dstep| AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, dstep);
        match disk_step {
            AsyncDisk::Step::disk_ops() => {
                assert(post.disk.content == pre.disk.content);
            }
            _ => { assert(false); }
        }

        let remaining_outstanding = pre.outstanding_cache_reqs.remove_keys(disk_responses.dom());
        let new_request_addr_map = Map::new(
            |id: ID| disk_requests.contains_key(id),
            |id: ID| disk_requests[id].addr(),
        );
        assert(post.outstanding_cache_reqs == remaining_outstanding.union_prefer_right(new_request_addr_map));
        assert(post.disk.requests == pre.disk.requests.union_prefer_right(disk_requests));
        assert(post.disk.responses == pre.disk.responses.remove_keys(disk_responses.dom()));

        remove_keys_preserves_injective(pre.outstanding_cache_reqs, disk_responses.dom());
        assert(new_request_addr_map.is_injective());
        assert(post.outstanding_cache_reqs.is_injective()) by {
            assert forall |id1: ID, id2: ID|
                id1 != id2
                && post.outstanding_cache_reqs.contains_key(id1)
                && post.outstanding_cache_reqs.contains_key(id2)
                implies #[trigger] post.outstanding_cache_reqs[id1] != #[trigger] post.outstanding_cache_reqs[id2]
            by {
                if new_request_addr_map.contains_key(id1) {
                    if new_request_addr_map.contains_key(id2) {
                        union_prefer_right_uses_right(remaining_outstanding, new_request_addr_map, id1);
                        union_prefer_right_uses_right(remaining_outstanding, new_request_addr_map, id2);
                        assert(new_request_addr_map[id1] != new_request_addr_map[id2]);
                    } else {
                        union_prefer_right_uses_right(remaining_outstanding, new_request_addr_map, id1);
                        union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id2);
                        assert(pre.outstanding_cache_reqs.contains_key(id2));
                        assert(remaining_outstanding[id2] == pre.outstanding_cache_reqs[id2]);
                        assert(pre.outstanding_cache_reqs.values().contains(remaining_outstanding[id2]));
                        assert(new_request_addr_map.values().contains(new_request_addr_map[id1]));
                        assert(new_request_addr_map.values().disjoint(pre.outstanding_cache_reqs.values()));
                    }
                } else {
                    if new_request_addr_map.contains_key(id2) {
                        union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id1);
                        union_prefer_right_uses_right(remaining_outstanding, new_request_addr_map, id2);
                        assert(pre.outstanding_cache_reqs.contains_key(id1));
                        assert(remaining_outstanding[id1] == pre.outstanding_cache_reqs[id1]);
                        assert(pre.outstanding_cache_reqs.values().contains(remaining_outstanding[id1]));
                        assert(new_request_addr_map.values().contains(new_request_addr_map[id2]));
                        assert(new_request_addr_map.values().disjoint(pre.outstanding_cache_reqs.values()));
                    } else {
                        union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id1);
                        union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id2);
                        assert(pre.outstanding_cache_reqs.contains_key(id1));
                        assert(pre.outstanding_cache_reqs.contains_key(id2));
                        assert(remaining_outstanding[id1] == pre.outstanding_cache_reqs[id1]);
                        assert(remaining_outstanding[id2] == pre.outstanding_cache_reqs[id2]);
                        assert(pre.outstanding_cache_reqs[id1] != pre.outstanding_cache_reqs[id2]);
                    }
                }
            }
        };

        assert(post.disk.requests.dom() + post.disk.responses.dom() == post.outstanding_cache_reqs.dom()) by {
            assert forall |id: ID| #[trigger] post.outstanding_cache_reqs.contains_key(id)
                <==> (post.disk.requests.dom() + post.disk.responses.dom()).contains(id) by {
                if post.outstanding_cache_reqs.contains_key(id) {
                    if new_request_addr_map.contains_key(id) {
                        union_prefer_right_uses_right(remaining_outstanding, new_request_addr_map, id);
                        assert(disk_requests.contains_key(id));
                        assert(post.disk.requests.contains_key(id));
                    } else {
                        union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id);
                        assert(pre.outstanding_cache_reqs.contains_key(id));
                        assert(!disk_responses.dom().contains(id));
                        if pre.disk.requests.contains_key(id) {
                            assert(post.disk.requests.contains_key(id));
                        } else {
                            assert(pre.disk.responses.contains_key(id));
                            remove_keys_preserves_unremoved(pre.disk.responses, disk_responses.dom(), id);
                            assert(post.disk.responses.contains_key(id));
                        }
                    }
                }
                if (post.disk.requests.dom() + post.disk.responses.dom()).contains(id) {
                    if post.disk.requests.contains_key(id) {
                        if disk_requests.contains_key(id) {
                            union_prefer_right_uses_right(remaining_outstanding, new_request_addr_map, id);
                            assert(post.outstanding_cache_reqs.contains_key(id));
                        } else {
                            assert(pre.disk.requests.contains_key(id));
                            assert(!pre.disk.responses.contains_key(id));
                            assert(pre.outstanding_cache_reqs.contains_key(id));
                            assert(!disk_responses.dom().contains(id));
                            remove_keys_preserves_unremoved(pre.outstanding_cache_reqs, disk_responses.dom(), id);
                            union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id);
                            assert(post.outstanding_cache_reqs.contains_key(id));
                        }
                    } else {
                        assert(post.disk.responses.contains_key(id));
                        assert(pre.disk.responses.contains_key(id));
                        assert(!disk_responses.dom().contains(id));
                        assert(pre.outstanding_cache_reqs.contains_key(id));
                        remove_keys_preserves_unremoved(pre.outstanding_cache_reqs, disk_responses.dom(), id);
                        union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id);
                        assert(post.outstanding_cache_reqs.contains_key(id));
                    }
                }
            }
        };

        assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id) implies {
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
            let req = post.disk.requests[id];
            if disk_requests.contains_key(id) {
                union_prefer_right_uses_right(remaining_outstanding, new_request_addr_map, id);
                assert(post.outstanding_cache_reqs[id] == disk_requests[id].addr());
                assert(req == disk_requests[id]);
                assert(cache_requests.contains(req));
                match cache_step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(Cache::State::valid_load_requests(cache_requests, new_slots_mapping));
                        assert(req is ReadReq);
                        assert(crate::implementation::Cache_v::addr_maps_to_req(cache_requests, req, req->from));
                        assert(new_slots_mapping.contains_value(req->from));
                        invert_contains_pair(new_slots_mapping, req->from);
                        let slot = new_slots_mapping.invert()[req->from];
                        assert(post.cache.lookup_map == pre.cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                        assert(!pre.cache.lookup_map.contains_key(req->from));
                        union_prefer_right_uses_right(pre.cache.lookup_map, new_slots_mapping.invert(), req->from);
                        assert(post.cache.lookup_map[req->from] == slot);
                        assert(post.cache.entries == pre.cache.entries.union_prefer_right(Map::new(
                            |slot| new_slots_mapping.contains_key(slot),
                            |slot| Entry::Loading{addr: new_slots_mapping[slot]}
                        )));
                        union_prefer_right_uses_right(
                            pre.cache.entries,
                            Map::new(
                                |slot| new_slots_mapping.contains_key(slot),
                                |slot| Entry::Loading{addr: new_slots_mapping[slot]}
                            ),
                            slot,
                        );
                        assert(post.cache.entries[slot] is Loading);
                    }
                    Cache::Step::writeback_initiate() => {
                        assert(pre.cache.valid_writeback_requests(cache_requests));
                        assert(req is WriteReq);
                        let slot = pre.cache.lookup_map[req->to];
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                        assert(post.cache.entries == pre.cache.entries);
                        assert(post.cache.lookup_map[req->to] == slot);
                        assert(post.cache.entries[slot] == Entry::Filled{addr: req->to, data: req->data});
                        let request_slot_map = Map::new(
                            |req2: DiskRequest| cache_requests.contains(req2),
                            |req2: DiskRequest| pre.cache.lookup_map[req2->to]
                        );
                        let writeback_slots = request_slot_map.values();
                        assert(request_slot_map.contains_key(req));
                        assert(request_slot_map[req] == slot);
                        assert(writeback_slots.contains(slot));
                        assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(Map::new(
                            |slot| writeback_slots.contains(slot),
                            |slot| Status::Writeback
                        )));
                        union_prefer_right_uses_right(
                            pre.cache.status_map,
                            Map::new(
                                |slot| writeback_slots.contains(slot),
                                |slot| Status::Writeback
                            ),
                            slot,
                        );
                        assert(post.cache.status_map[slot] is Writeback);
                    }
                    Cache::Step::load_complete() => { assert(false); }
                    Cache::Step::writeback_complete() => { assert(false); }
                    _ => { assert(false); }
                }
            } else {
                assert(pre.disk.requests.contains_key(id));
                assert(!pre.disk.responses.contains_key(id));
                assert(pre.outstanding_cache_reqs.contains_key(id));
                let addr = pre.outstanding_cache_reqs[id];
                let slot = pre.cache.lookup_map[addr];
                assert(!cache_responses.contains_key(addr)) by {
                    if cache_responses.contains_key(addr) {
                        let resp_id = choose |resp_id: ID|
                            #[trigger] disk_responses.contains_key(resp_id) && pre.outstanding_cache_reqs[resp_id] == addr;
                        assert(pre.outstanding_cache_reqs.contains_key(resp_id));
                        assert(pre.outstanding_cache_reqs.is_injective());
                        assert(resp_id == id);
                        assert(pre.disk.responses.contains_key(id));
                        assert(false);
                    }
                };
                assert forall |req2: DiskRequest| #[trigger] cache_requests.contains(req2) implies req2.addr() != addr by {
                    assert(cache_requests.contains(req2));
                    let req_id = choose |req_id: ID|
                        #![trigger disk_requests[req_id]]
                        disk_requests.contains_key(req_id) && disk_requests[req_id] == req2;
                    let request_addr_map = Map::new(
                        |id: ID| disk_requests.contains_key(id),
                        |id: ID| disk_requests[id].addr(),
                    );
                    assert(request_addr_map.contains_key(req_id));
                    assert(request_addr_map[req_id] == req2.addr());
                    assert(request_addr_map.values().contains(req2.addr()));
                    assert(pre.outstanding_cache_reqs.values().contains(addr));
                    assert(request_addr_map.values().disjoint(pre.outstanding_cache_reqs.values()));
                };
                Self::cache_disk_ops_preserves_unaffected_lookup_slot(pre, post, cache_requests, cache_responses, addr);
                remove_keys_preserves_unremoved(pre.outstanding_cache_reqs, disk_responses.dom(), id);
                union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id);
                assert(post.outstanding_cache_reqs[id] == addr);
                assert(post.disk.requests[id] == pre.disk.requests[id]);
                assert(req == pre.disk.requests[id]);
                assert(req.addr() == addr);
                if req is ReadReq {
                    assert(post.cache.entries[slot] is Loading);
                } else {
                    assert(post.cache.entries[slot] == Entry::Filled{addr, data: req->data});
                    assert(post.cache.status_map[slot] is Writeback);
                }
            }
        };

        assert(post.outstanding_reqs_requests_ok());

        assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id) implies {
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
            assert(!disk_responses.dom().contains(id));
            let addr = pre.outstanding_cache_reqs[id];
            let resp = pre.disk.responses[id];
            let slot = pre.cache.lookup_map[addr];
            assert(!cache_responses.contains_key(addr)) by {
                if cache_responses.contains_key(addr) {
                    let resp_id = choose |resp_id: ID|
                        #[trigger] disk_responses.contains_key(resp_id) && pre.outstanding_cache_reqs[resp_id] == addr;
                    assert(pre.outstanding_cache_reqs.contains_key(resp_id));
                    assert(pre.outstanding_cache_reqs.is_injective());
                    assert(resp_id == id);
                    assert(disk_responses.contains_key(id));
                    assert(false);
                }
            };
            assert forall |req2: DiskRequest| #[trigger] cache_requests.contains(req2) implies req2.addr() != addr by {
                assert(cache_requests.contains(req2));
                let req_id = choose |req_id: ID|
                    #![trigger disk_requests[req_id]]
                    disk_requests.contains_key(req_id) && disk_requests[req_id] == req2;
                let request_addr_map = Map::new(
                    |id: ID| disk_requests.contains_key(id),
                    |id: ID| disk_requests[id].addr(),
                );
                assert(request_addr_map.contains_key(req_id));
                assert(request_addr_map[req_id] == req2.addr());
                assert(request_addr_map.values().contains(req2.addr()));
                assert(pre.outstanding_cache_reqs.values().contains(addr));
                assert(request_addr_map.values().disjoint(pre.outstanding_cache_reqs.values()));
            };
            Self::cache_disk_ops_preserves_unaffected_lookup_slot(pre, post, cache_requests, cache_responses, addr);
            remove_keys_preserves_unremoved(pre.outstanding_cache_reqs, disk_responses.dom(), id);
            union_prefer_right_uses_left(remaining_outstanding, new_request_addr_map, id);
            assert(post.outstanding_cache_reqs[id] == addr);
            remove_keys_preserves_unremoved(pre.disk.responses, disk_responses.dom(), id);
            assert(post.disk.responses[id] == resp);
            assert(post.disk.content == pre.disk.content);
            if resp is ReadResp {
                assert(resp->data == pre.disk.content[addr]);
                assert(post.cache.entries[slot] is Loading);
            } else {
                assert(post.cache.entries[slot] == Entry::Filled{addr, data: pre.disk.content[addr]});
                assert(post.cache.status_map[slot] is Writeback);
            }
        };

        assert(post.outstanding_reqs_responses_ok());

        assert forall |id: ID|
            #![trigger post.disk.requests.contains_key(id)]
            #![trigger post.disk.responses.contains_key(id)]
            (post.disk.requests.contains_key(id) || post.disk.responses.contains_key(id))
            implies post.io_id_valid(id) by {
            if post.disk.requests.contains_key(id) {
                let req = post.disk.requests[id];
                if disk_requests.contains_key(id) {
                    let addr = disk_requests[id].addr();
                    assert(post.outstanding_cache_reqs.contains_key(id));
                    assert(post.outstanding_cache_reqs[id] == addr);
                    assert(req == disk_requests[id]);
                    assert(req.addr() == addr);
                    match cache_step {
                        Cache::Step::load_initiate(new_slots_mapping) => {
                            assert(Cache::State::valid_load_requests(cache_requests, new_slots_mapping));
                            assert(cache_requests.contains(req));
                            assert(req is ReadReq);
                            assert(crate::implementation::Cache_v::addr_maps_to_req(cache_requests, req, addr));
                            assert(new_slots_mapping.contains_value(addr));
                            invert_contains_pair(new_slots_mapping, addr);
                            let slot = new_slots_mapping.invert()[addr];
                            assert(!pre.cache.lookup_map.contains_key(addr));
                            assert(post.cache.lookup_map == pre.cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                            union_prefer_right_uses_right(pre.cache.lookup_map, new_slots_mapping.invert(), addr);
                            assert(post.cache.lookup_map[addr] == slot);
                            assert(post.cache.entries == pre.cache.entries.union_prefer_right(Map::new(
                                |slot| new_slots_mapping.contains_key(slot),
                                |slot| Entry::Loading{addr: new_slots_mapping[slot]}
                            )));
                            union_prefer_right_uses_right(
                                pre.cache.entries,
                                Map::new(
                                    |slot| new_slots_mapping.contains_key(slot),
                                    |slot| Entry::Loading{addr: new_slots_mapping[slot]}
                                ),
                                slot,
                            );
                            assert(post.cache.entries.contains_key(slot));
                            assert(post.cache.status_map.contains_key(slot));
                            assert(post.disk.content == pre.disk.content);
                            assert(pre.disk.content.contains_key(addr));
                            assert(post.disk.content.contains_key(addr));
                        }
                        Cache::Step::writeback_initiate() => {
                            let slot = pre.cache.lookup_map[addr];
                            assert(pre.cache.valid_writeback_requests(cache_requests));
                            assert(cache_requests.contains(req));
                            assert(req is WriteReq);
                            Self::cache_lookup_slot_gets_addr(pre.cache, addr);
                            assert(post.cache.lookup_map == pre.cache.lookup_map);
                            assert(post.cache.entries == pre.cache.entries);
                            assert(post.cache.lookup_map.contains_key(addr));
                            assert(post.cache.lookup_map[addr] == slot);
                            assert(post.cache.entries.contains_key(slot));
                            assert(post.cache.status_map.contains_key(slot));
                        }
                        Cache::Step::load_complete() => {
                            assert(cache_requests.is_empty());
                            assert(disk_requests.values() =~= cache_requests);
                            assert(disk_requests.values().contains(req));
                            assert(false);
                        }
                        Cache::Step::writeback_complete() => {
                            assert(cache_requests.is_empty());
                            assert(disk_requests.values() =~= cache_requests);
                            assert(disk_requests.values().contains(req));
                            assert(false);
                        }
                        _ => { assert(false); }
                    }
                } else {
                    assert(pre.disk.requests.contains_key(id));
                    assert(pre.io_id_valid(id));
                    let addr = pre.outstanding_cache_reqs[id];
                    assert(post.outstanding_cache_reqs.contains_key(id));
                    assert(post.outstanding_cache_reqs[id] == addr);
                    assert(!cache_responses.contains_key(addr)) by {
                        if cache_responses.contains_key(addr) {
                            let resp_id = choose |resp_id: ID|
                                #[trigger] disk_responses.contains_key(resp_id) && pre.outstanding_cache_reqs[resp_id] == addr;
                            assert(pre.outstanding_cache_reqs.contains_key(resp_id));
                            assert(pre.outstanding_cache_reqs.is_injective());
                            assert(resp_id == id);
                            assert(pre.disk.responses.contains_key(id));
                            assert(false);
                        }
                    };
                    assert forall |req2: DiskRequest| #[trigger] cache_requests.contains(req2) implies req2.addr() != addr by {
                        if cache_requests.contains(req2) {
                            let req_id = choose |req_id: ID|
                                #![trigger disk_requests[req_id]]
                                disk_requests.contains_key(req_id) && disk_requests[req_id] == req2;
                            let request_addr_map = Map::new(
                                |id: ID| disk_requests.contains_key(id),
                                |id: ID| disk_requests[id].addr(),
                            );
                            assert(request_addr_map.contains_key(req_id));
                            assert(request_addr_map[req_id] == req2.addr());
                            assert(request_addr_map.values().contains(req2.addr()));
                            assert(pre.outstanding_cache_reqs.values().contains(addr));
                            assert(request_addr_map.values().disjoint(pre.outstanding_cache_reqs.values()));
                        }
                    };
                    Self::cache_disk_ops_preserves_unaffected_lookup_slot(pre, post, cache_requests, cache_responses, addr);
                    assert(post.cache.lookup_map.contains_key(addr));
                    assert(post.cache.entries.contains_key(post.cache.lookup_map[addr]));
                    assert(post.cache.status_map.contains_key(post.cache.lookup_map[addr]));
                    if req is ReadReq {
                        assert(post.disk.content == pre.disk.content);
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                }
            } else {
                let addr = post.outstanding_cache_reqs[id];
                assert(pre.disk.responses.contains_key(id));
                assert(pre.io_id_valid(id));
                assert(post.outstanding_cache_reqs.contains_key(id));
                assert(!disk_responses.dom().contains(id));
                assert(!cache_responses.contains_key(addr)) by {
                    if cache_responses.contains_key(addr) {
                        let resp_id = choose |resp_id: ID|
                            #[trigger] disk_responses.contains_key(resp_id) && pre.outstanding_cache_reqs[resp_id] == addr;
                        assert(pre.outstanding_cache_reqs.contains_key(resp_id));
                        assert(pre.outstanding_cache_reqs.is_injective());
                        assert(resp_id == id);
                        assert(disk_responses.contains_key(id));
                        assert(false);
                    }
                };
                assert forall |req2: DiskRequest| #[trigger] cache_requests.contains(req2) implies req2.addr() != addr by {
                    if cache_requests.contains(req2) {
                        let req_id = choose |req_id: ID|
                            #![trigger disk_requests[req_id]]
                            disk_requests.contains_key(req_id) && disk_requests[req_id] == req2;
                        let request_addr_map = Map::new(
                            |id: ID| disk_requests.contains_key(id),
                            |id: ID| disk_requests[id].addr(),
                        );
                        assert(request_addr_map.contains_key(req_id));
                        assert(request_addr_map[req_id] == req2.addr());
                        assert(request_addr_map.values().contains(req2.addr()));
                        assert(pre.outstanding_cache_reqs.values().contains(addr));
                        assert(request_addr_map.values().disjoint(pre.outstanding_cache_reqs.values()));
                    }
                };
                Self::cache_disk_ops_preserves_unaffected_lookup_slot(pre, post, cache_requests, cache_responses, addr);
                assert(post.cache.lookup_map.contains_key(addr));
                assert(post.cache.entries.contains_key(post.cache.lookup_map[addr]));
                assert(post.cache.status_map.contains_key(post.cache.lookup_map[addr]));
                if post.disk.responses[id] is ReadResp {
                    assert(post.disk.content == pre.disk.content);
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                }
            }
        };
    }

    proof fn cache_disk_ops_preserves_wf(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        new_cache: Cache::State,
        new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::cache_disk_ops(
                pre,
                post,
                lbl,
                new_cache,
                new_disk,
                cache_requests,
                cache_responses,
                disk_requests,
                disk_responses,
            ),
        ensures
            post.wf(),
    {
        Self::cache_diskops_preserves_inv(pre, post.cache, cache_requests, cache_responses);
        Self::disk_diskops_preserves_inv(pre, post.disk, disk_requests, disk_responses);
        Self::cache_disk_ops_preserves_clean_pages_match_disk(
            pre, post, cache_requests, cache_responses, disk_requests, disk_responses,
        );
        Self::cache_disk_ops_preserves_outstanding_reqs_consistent(
            pre, post, cache_requests, cache_responses, disk_requests, disk_responses,
        );
        assert(post.cache_agrees_with_disk());
        assert(post.wf());
    }

    proof fn query_preserves_wf(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        needed: Set<Address>,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::query(pre, post, lbl, reads, needed),
        ensures
            post.wf(),
    {
        reveal(ConcreteBranch::State::query);
        assert(post.cached_branch == pre.cached_branch);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.wf());
    }

    proof fn append_preserves_wf(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        needed: Set<Address>,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::append(pre, post, lbl, reads, writes, needed, new_cache),
        ensures
            post.wf(),
    {
        reveal(ConcreteBranch::State::append);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        match lbl {
            ConcreteBranch::Label::Append{keys, msgs, depth} => {
                assert(post.cached_branch == pre.cached_branch.append(
                    keys, msgs, depth, read_nodes, write_nodes, needed,
                ));
                assert(post.cached_branch.wf());
                assert(post.cached_branch.valid_allocator(post.mini_allocator));
                assert(post.mini_allocator == pre.mini_allocator);
                assert(post.mini_allocator.wf());
                assert(post.cache == new_cache);
                Self::cache_access_preserves_inv(pre, post.cache, reads, writes);
                assert(post.cache.inv());
                assert(post.disk == pre.disk);
                assert(post.disk.inv());
                assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
                Self::access_preserves_outstanding_reqs_consistent(pre, post, reads, writes);
                Self::access_preserves_cache_agrees_with_disk(pre, post, reads, writes);
                assert(!post.cached_branch.sealed);
                assert(post.cache_agrees_with_disk());
                assert(post.wf());
            }
            _ => { assert(false); }
        }
    }

    proof fn grow_preserves_wf(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::grow(pre, post, lbl, reads, writes, new_cache),
        ensures
            post.wf(),
    {
        reveal(ConcreteBranch::State::grow);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        match lbl {
            ConcreteBranch::Label::Grow{new_root_addr} => {
                assert(post.cached_branch == pre.cached_branch.grow(
                    pre.mini_allocator, new_root_addr, read_nodes, write_nodes,
                ));
                assert(post.cached_branch.wf());
                assert(post.mini_allocator == pre.mini_allocator.allocate(new_root_addr));
                Self::mini_allocator_allocate_preserves_wf_and_aus(pre.mini_allocator, new_root_addr);
                assert(post.cached_branch.valid_allocator(post.mini_allocator));
                assert(post.mini_allocator.wf());
                assert(post.cache == new_cache);
                Self::cache_access_preserves_inv(pre, post.cache, reads, writes);
                assert(post.cache.inv());
                assert(post.disk == pre.disk);
                assert(post.disk.inv());
                assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
                Self::access_preserves_outstanding_reqs_consistent(pre, post, reads, writes);
                Self::access_preserves_cache_agrees_with_disk(pre, post, reads, writes);
                assert(!post.cached_branch.sealed);
                assert(post.cache_agrees_with_disk());
                assert(post.wf());
            }
            _ => { assert(false); }
        }
    }

    proof fn split_preserves_wf(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        needed: Set<Address>,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::split(pre, post, lbl, reads, writes, needed, new_cache),
        ensures
            post.wf(),
    {
        reveal(ConcreteBranch::State::split);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        match lbl {
            ConcreteBranch::Label::Split{new_child_addr, pivot, depth, split_arg} => {
                assert(post.cached_branch == pre.cached_branch.split(
                    pre.mini_allocator, new_child_addr, pivot, depth, split_arg, read_nodes, write_nodes, needed,
                ));
                assert(post.cached_branch.wf());
                assert(post.mini_allocator == pre.mini_allocator.allocate(new_child_addr));
                Self::mini_allocator_allocate_preserves_wf_and_aus(pre.mini_allocator, new_child_addr);
                assert(post.cached_branch.valid_allocator(post.mini_allocator));
                assert(post.mini_allocator.wf());
                assert(post.cache == new_cache);
                Self::cache_access_preserves_inv(pre, post.cache, reads, writes);
                assert(post.cache.inv());
                assert(post.disk == pre.disk);
                assert(post.disk.inv());
                assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
                Self::access_preserves_outstanding_reqs_consistent(pre, post, reads, writes);
                Self::access_preserves_cache_agrees_with_disk(pre, post, reads, writes);
                assert(!post.cached_branch.sealed);
                assert(post.cache_agrees_with_disk());
                assert(post.wf());
            }
            _ => { assert(false); }
        }
    }

    proof fn seal_preserves_wf(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::seal(pre, post, lbl, reads, writes, new_cache),
        ensures
            post.wf(),
    {
        reveal(ConcreteBranch::State::seal);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        match lbl {
            ConcreteBranch::Label::Seal{aux_ptr} => {
                assert(post.cached_branch == pre.cached_branch.seal(
                    pre.mini_allocator, aux_ptr, read_nodes, write_nodes,
                ));
                assert(post.cached_branch.wf());
                if aux_ptr is Some {
                    Self::mini_allocator_allocate_preserves_wf_and_aus(pre.mini_allocator, aux_ptr.unwrap());
                    Self::mini_allocator_prune_empty_preserves_wf_and_aus(pre.mini_allocator.allocate(aux_ptr.unwrap()));
                    assert(post.mini_allocator == pre.mini_allocator.allocate(aux_ptr.unwrap()).prune(Set::<AU>::empty()));
                } else {
                    Self::mini_allocator_prune_empty_preserves_wf_and_aus(pre.mini_allocator);
                    assert(post.mini_allocator == pre.mini_allocator.prune(Set::<AU>::empty()));
                }
                assert(post.cached_branch.valid_allocator(post.mini_allocator));
                assert(post.mini_allocator.wf());
                assert(post.cache == new_cache);
                Self::cache_access_preserves_inv(pre, post.cache, reads, writes);
                assert(post.cache.inv());
                assert(post.disk == pre.disk);
                assert(post.disk.inv());
                assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
                Self::access_preserves_outstanding_reqs_consistent(pre, post, reads, writes);
                Self::access_preserves_cache_agrees_with_disk(pre, post, reads, writes);
                assert(post.wf());
            }
            _ => { assert(false); }
        }
    }

    proof fn internal_cache_preserves_wf(
        pre: Self,
        post: Self,
        lbl: ConcreteBranch::Label,
        new_cache: Cache::State,
    )
        requires
            pre.wf(),
            ConcreteBranch::State::internal_cache(pre, post, lbl, new_cache),
        ensures
            post.wf(),
    {
        reveal(ConcreteBranch::State::internal_cache);
        assert(lbl is Internal);
        assert(post.cached_branch == pre.cached_branch);
        assert(post.mini_allocator == pre.mini_allocator);
        assert(post.cache == new_cache);
        Self::cache_internal_preserves_inv(pre, post.cache);
        assert(post.cache.inv());
        assert(post.disk == pre.disk);
        assert(post.disk.inv());
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        Self::internal_cache_preserves_outstanding_reqs_consistent(pre, post, new_cache);
        Self::internal_cache_preserves_cache_agrees_with_disk(pre, post, new_cache);
        assert(post.cache_agrees_with_disk());
        assert(post.wf());
    }
}

} // verus!
