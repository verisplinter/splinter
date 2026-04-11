// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::{map::*, set::*};

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranch_v::{BranchNode as AllocationBranchNode, Summary};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::{LinkedBranch, SplitArg};
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::Cache_v::{Cache, Entry};
use crate::implementation::CachedBranch_v::{init_mini_allocator, CachedBranch, LoadedPathReceipt};
use crate::implementation::IBranchNode_v::branch_node_image;
use crate::marshalling::IBranchNodeFormat_v::{raw_page_to_branch_node, BranchNodePageFmt};
use crate::marshalling::Marshalling_v::Marshal;
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::spec::Messages_t::{nop_delta, Message};

verus! {

pub open spec fn encode_branch_page(node: AllocationBranchNode) -> RawPage
{
    let fmt = BranchNodePageFmt::spec_new();
    if fmt.marshallable(branch_node_image(node)) {
        choose |raw_page: RawPage|
            fmt.parsable(raw_page) && fmt.parse(raw_page) == branch_node_image(node)
    } else {
        arbitrary()
    }
}

pub open spec fn decode_branch_page(raw_page: RawPage) -> AllocationBranchNode
{
    raw_page_to_branch_node(raw_page)
}

pub open spec fn to_branch_nodes(raw_pages: Map<Address, RawPage>) -> Map<Address, AllocationBranchNode>
{
    Map::new(
        |addr: Address| raw_pages.contains_key(addr),
        |addr: Address| decode_branch_page(raw_pages[addr]),
    )
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
        cached_branch.is_empty_active()
    }
}

state_machine!{ ConcreteBranch {
    fields {
        pub cached_branches: Seq<CachedBranch>,
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

    init!{ initialize(cached_branch: CachedBranch, seq_end: nat, init_aus: Set<AU>, cache: Cache::State, cache_slots: nat, disk: AsyncDisk::State) {
        require Cache::State::initialize(cache, cache_slots);
        require disk.inv();
        require disk.requests.is_empty();
        require disk.responses.is_empty();
        require init_projection_valid(cached_branch, disk);
        require init_mini_allocator(init_aus).all_aus() == init_aus;
        require if cached_branch.sealed {
            &&& cached_branch.wf()
            &&& cached_branch.root is Some
            &&& init_projected_branch(cached_branch, disk).get_summary().disjoint(init_aus)
        } else {
            &&& cached_branch.is_empty_active()
            &&& seq_end == 0
        };

        init cached_branches =
            if cached_branch.sealed {
                Seq::<CachedBranch>::empty().push(cached_branch).push(CachedBranch::empty_active())
            } else {
                Seq::<CachedBranch>::empty().push(CachedBranch::empty_active())
            };
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
        let new_active = pre.active_cached_branch().append(receipt, keys, msgs, read_nodes, write_nodes);

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branches = pre.cached_branches.update(pre.active_idx(), new_active);
        update seq_end = pre.seq_end + keys.len();
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
        require !pre.available_branch_nodes().contains_key(new_root_addr);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pre.active_cached_branch().can_grow(pre.mini_allocator, new_root_addr, read_nodes, write_nodes);
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
        require !pre.available_branch_nodes().contains_key(new_child_addr);
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pivot == split_arg.get_pivot();
        require pre.active_cached_branch().can_split(pre.mini_allocator, new_child_addr, receipt, split_arg, read_nodes, write_nodes);
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
        require aux_ptr is Some ==> !pre.available_branch_nodes().contains_key(aux_ptr.unwrap());
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        require pre.active_cached_branch().can_seal(pre.mini_allocator, aux_ptr, read_nodes, write_nodes);
        let sealed_active = pre.active_cached_branch().seal(pre.mini_allocator, aux_ptr, read_nodes, write_nodes);
        let sealed_allocator =
            if aux_ptr is Some {
                pre.mini_allocator.allocate(aux_ptr.unwrap())
            } else {
                pre.mini_allocator
            };
        let new_mini_allocator = sealed_allocator.prune(sealed_allocator.reserved_aus());

        let cache_lbl = Self::cache_access_label(reads, writes);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cached_branches = pre.cached_branches.update(pre.active_idx(), sealed_active).push(CachedBranch::empty_active());
        update mini_allocator = new_mini_allocator;
        update cache = new_cache;
    }}

    transition!{ fill_au(lbl: Label) {
        require let Label::FillAU{aus} = lbl;
        require pre.wf();
        require pre.fresh_aus_for_active(aus);

        update mini_allocator = pre.mini_allocator.add_aus(aus);
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
    fn initialize_inductive(post: Self, cached_branch: CachedBranch, seq_end: nat, init_aus: Set<AU>, cache: Cache::State, cache_slots: nat, disk: AsyncDisk::State) {
        assume(post.wf());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>, query_receipts: Seq<Option<LoadedPathReceipt>>) {
        assume(post.wf());
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
        assume(post.wf());
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
        assume(post.wf());
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
        assume(post.wf());
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
        assume(post.wf());
    }

    #[inductive(fill_au)]
    fn fill_au_inductive(pre: Self, post: Self, lbl: Label) {
        assume(post.wf());
    }

    #[inductive(internal_cache)]
    fn internal_cache_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State) {
        assume(post.wf());
    }

    #[inductive(internal_disk)]
    fn internal_disk_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State) {
        assume(post.wf());
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
        assume(post.wf());
    }
}}

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

    pub open spec fn cache_access_label(
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
    ) -> Cache::Label
    {
        Cache::Label::Access{reads, writes}
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

    pub open spec fn available_raw_pages(self) -> Map<Address, RawPage>
    {
        Map::new(
            |addr: Address| self.has_cached_page(addr) || self.disk.content.contains_key(addr),
            |addr: Address| if self.has_cached_page(addr) { self.cache_raw_page(addr) } else { self.disk.content[addr] },
        )
    }

    pub open spec fn available_branch_nodes(self) -> Map<Address, AllocationBranchNode>
    {
        to_branch_nodes(self.available_raw_pages())
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

    pub open spec fn overlay_branch_addrs(self) -> Set<Address>
        recommends self.cached_branches.len() > 0
    {
        self.overlay_branch_addrs_at(self.active_idx() as nat)
    }

    pub open spec fn has_overlay_page(self, addr: Address) -> bool
        recommends self.cached_branches.len() > 0
    {
        self.has_overlay_page_at(self.active_idx() as nat, addr)
    }

    pub open spec fn overlay_raw_page(self, addr: Address) -> RawPage
        recommends self.cached_branches.len() > 0, self.has_overlay_page(addr)
    {
        self.overlay_raw_page_at(self.active_idx() as nat, addr)
    }

    pub open spec fn overlay_branch_entries(self) -> Map<Address, AllocationBranchNode>
        recommends self.cached_branches.len() > 0
    {
        self.overlay_branch_entries_at(self.active_idx() as nat)
    }

    pub open spec fn overlay_branch(self) -> Option<LinkedBranch<Summary>>
        recommends self.cached_branches.len() > 0
    {
        self.overlay_branch_at(self.active_idx() as nat)
    }

    pub open spec fn sealed_branch_aus_at(self, branch_idx: nat) -> Set<AU>
        recommends
            branch_idx < self.cached_branches.len(),
            self.cached_branches[branch_idx as int].sealed,
            self.overlay_branch_at(branch_idx) is Some,
    {
        self.overlay_branch_at(branch_idx).unwrap().get_summary()
    }

    pub open spec fn active_branch_pages_in_allocator(self) -> bool
        recommends self.cached_branches.len() > 0
    {
        forall |addr: Address|
            #[trigger] self.overlay_branch_entries().contains_key(addr)
            ==> self.mini_allocator.all_aus().contains(addr.au)
    }

    pub open spec fn sealed_branches_disjoint(self) -> bool
        recommends self.cached_branches.len() > 0
    {
        forall |i: int, j: int|
            0 <= i < j < self.cached_branches.len() - 1
            ==> #[trigger] self.sealed_branches_disjoint_at(i as nat, j as nat)
    }

    pub open spec fn sealed_branches_disjoint_at(self, i: nat, j: nat) -> bool
        recommends
            self.cached_branches.len() > 0,
            i < j < self.cached_branches.len() - 1,
    {
        let left = self.overlay_branch_at(i);
        let right = self.overlay_branch_at(j);
        &&& left is Some
        &&& right is Some
        &&& left.unwrap().get_summary().disjoint(right.unwrap().get_summary())
    }

    pub open spec fn sealed_branches_disjoint_from_active_allocator(self) -> bool
        recommends self.cached_branches.len() > 0
    {
        forall |i: int|
            0 <= i < self.cached_branches.len() - 1
            ==> #[trigger] self.sealed_branch_disjoint_from_active_allocator_at(i as nat)
    }

    pub open spec fn sealed_branch_disjoint_from_active_allocator_at(self, i: nat) -> bool
        recommends
            self.cached_branches.len() > 0,
            i < self.cached_branches.len() - 1,
    {
        let branch = self.overlay_branch_at(i);
        &&& branch is Some
        &&& branch.unwrap().get_summary().disjoint(self.mini_allocator.all_aus())
    }

    pub open spec fn fresh_aus_for_active(self, aus: Set<AU>) -> bool
        recommends self.cached_branches.len() > 0
    {
        &&& aus.disjoint(self.mini_allocator.all_aus())
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
                &&& self.overlay_branch_at(i as nat) is Some
                &&& self.overlay_branch_at(i as nat).unwrap().valid_sealed_branch()
            }
        &&& self.active_cached_branch().wf()
        &&& !self.active_cached_branch().sealed
        &&& self.active_cached_branch().valid_allocator(self.mini_allocator)
        &&& self.active_branch_pages_in_allocator()
        &&& self.sealed_branches_disjoint()
        &&& self.sealed_branches_disjoint_from_active_allocator()
        &&& self.mini_allocator.wf()
        &&& self.cache.inv()
        &&& self.disk.inv()
        &&& self.outstanding_reqs_consistent()
        &&& self.cache_agrees_with_disk()
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
        assert forall |addr: Address| #[trigger] pre_entries.contains_key(addr) implies pre_entries[addr] == post_entries[addr] by { };
        assert_maps_equal!(pre_entries, post_entries);

        assert(pre.overlay_branch_at(branch_idx) == post.overlay_branch_at(branch_idx));
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
            == crate::implementation::ConcreteBranch_v::decode_branch_page(self.available_raw_pages()[addr]));
        assert(self.overlay_branch_entries_at(branch_idx)[addr]
            == crate::implementation::ConcreteBranch_v::decode_branch_page(self.overlay_raw_page_at(branch_idx, addr)));
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
