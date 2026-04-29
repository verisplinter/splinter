// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

use vstd::prelude::*;
use vstd::map::*;

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranchBetree_v::{map_with_disjoint_values, summary_aus};
use crate::allocation_layer::AllocationBranch_v::BranchNode;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{addrs_closed, set_addrs_disjoint_aus, AU, Address, Pointer};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::{init_mini_allocator, CachedBranch, LoadedPathReceipt};
use crate::implementation::ConcreteBranch_v::ConcreteBranch;
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::spec::Messages_t::Message;

verus! {

pub struct ConcreteSealedBranchStackImage {
    pub sealed_roots: Seq<Address>,
    pub sealed_disk: BufferDisk<BranchNode>,
}

impl ConcreteSealedBranchStackImage {
    pub open spec fn wf(self) -> bool
    {
        let branch_summary = self.sealed_disk.build_branch_summary(self.sealed_roots.to_set());
        &&& self.sealed_disk.sealed_branch_roots(self.sealed_roots.to_set())
        &&& set_addrs_disjoint_aus(self.sealed_roots.to_set())
        &&& map_with_disjoint_values(branch_summary)
        &&& addrs_closed(self.sealed_disk.entries.dom(), summary_aus(branch_summary))
    }
}

pub open spec fn empty_concrete_sealed_branch_stack_image() -> ConcreteSealedBranchStackImage
{
    ConcreteSealedBranchStackImage{
        sealed_roots: Seq::empty(),
        sealed_disk: BufferDisk{ entries: Map::empty() },
    }
}

pub struct InFlightConcreteSealedBranchStackImage {
    pub image: ConcreteSealedBranchStackImage,
    pub seq_end: nat,
}

pub enum EphemeralConcreteBranch {
    Unknown,
    Known{ v: ConcreteBranch::State },
}

impl ConcreteBranch::State {
    pub open spec fn sealed_image(self) -> ConcreteSealedBranchStackImage
    {
        ConcreteSealedBranchStackImage{
            sealed_roots: self.sealed_roots_i(),
            sealed_disk: self.sealed_disk_i(),
        }
    }

    pub open spec fn loads_from_image(
        self,
        image: ConcreteSealedBranchStackImage,
        image_seq_end: nat,
        init_aus: Set<AU>,
    ) -> bool
    {
        &&& self.wf()
        &&& self.sealed_image() == image
        &&& self.seq_end == image_seq_end
        &&& self.active_cached_branch() == CachedBranch::empty_active()
        &&& self.mini_allocator == init_mini_allocator(init_aus)
    }
}

state_machine!{ CrashAwareConcreteBranch {
    fields {
        pub persistent: ConcreteSealedBranchStackImage,
        pub persistent_seq_end: nat,
        pub ephemeral: EphemeralConcreteBranch,
        pub in_flight: Option<InFlightConcreteSealedBranchStackImage>,
    }

    pub enum Label {
        LoadEphemeral{ init_aus: Set<AU> },
        Query{ branch_idx: nat, key: Key, msg: Message },
        Append{ keys: Seq<Key>, msgs: Seq<Message> },
        Internal,
        CommitStart{ new_boundary_lsn: nat },
        CommitComplete,
        Crash{ keep_in_flight: bool },
    }

    init!{ initialize() {
        init persistent = empty_concrete_sealed_branch_stack_image();
        init persistent_seq_end = 0;
        init ephemeral = EphemeralConcreteBranch::Unknown;
        init in_flight = Option::None;
    }}

    transition!{ load_ephemeral(lbl: Label, new_concrete: ConcreteBranch::State) {
        require pre.inv();
        require let Label::LoadEphemeral{init_aus} = lbl;
        require pre.ephemeral is Unknown;
        require pre.in_flight is None;
        require new_concrete.loads_from_image(pre.persistent, pre.persistent_seq_end, init_aus);
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ query(
        lbl: Label,
        new_concrete: ConcreteBranch::State,
        reads: Map<Address, RawPage>,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
    ) {
        require pre.inv();
        require let Label::Query{branch_idx, key, msg} = lbl;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        let concrete_lbl = ConcreteBranch::Label::Query{branch_idx, key, msg};
        require ConcreteBranch::State::query(old_concrete, new_concrete, concrete_lbl, reads, query_receipts);
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ append_to_active(
        lbl: Label,
        new_concrete: ConcreteBranch::State,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: Cache::State,
    ) {
        require pre.inv();
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        let concrete_lbl = ConcreteBranch::Label::Append{keys, msgs};
        require ConcreteBranch::State::append(
            old_concrete,
            new_concrete,
            concrete_lbl,
            reads,
            writes,
            receipt,
            new_cache,
        );
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ append_to_empty(
        lbl: Label,
        new_concrete: ConcreteBranch::State,
        writes: Map<Address, RawPage>,
        init_root: Address,
        new_cache: Cache::State,
    ) {
        require pre.inv();
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        let concrete_lbl = ConcreteBranch::Label::Append{keys, msgs};
        require ConcreteBranch::State::append_to_empty(
            old_concrete,
            new_concrete,
            concrete_lbl,
            writes,
            init_root,
            new_cache,
        );
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ grow(
        lbl: Label,
        new_concrete: ConcreteBranch::State,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_root_addr: Address,
        new_cache: Cache::State,
    ) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        let concrete_lbl = ConcreteBranch::Label::Grow{new_root_addr};
        require ConcreteBranch::State::grow(
            old_concrete,
            new_concrete,
            concrete_lbl,
            reads,
            writes,
            new_cache,
        );
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ split(
        lbl: Label,
        new_concrete: ConcreteBranch::State,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_child_addr: Address,
        pivot: Key,
        split_arg: SplitArg,
        new_cache: Cache::State,
    ) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        let concrete_lbl = ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg};
        require ConcreteBranch::State::split(
            old_concrete,
            new_concrete,
            concrete_lbl,
            reads,
            writes,
            receipt,
            new_cache,
        );
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ seal(
        lbl: Label,
        new_concrete: ConcreteBranch::State,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        aux_ptr: Pointer,
        new_cache: Cache::State,
    ) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        let concrete_lbl = ConcreteBranch::Label::Seal{aux_ptr};
        require ConcreteBranch::State::seal(
            old_concrete,
            new_concrete,
            concrete_lbl,
            reads,
            writes,
            new_cache,
        );
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ fill_au(lbl: Label, new_concrete: ConcreteBranch::State, aus: Set<AU>) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        let concrete_lbl = ConcreteBranch::Label::FillAU{aus};
        require ConcreteBranch::State::fill_au(old_concrete, new_concrete, concrete_lbl);
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ internal_cache(lbl: Label, new_concrete: ConcreteBranch::State, new_cache: Cache::State) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        require ConcreteBranch::State::internal_cache(
            old_concrete,
            new_concrete,
            ConcreteBranch::Label::Internal{},
            new_cache,
        );
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ internal_disk(lbl: Label, new_concrete: ConcreteBranch::State, new_disk: AsyncDisk::State) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        require ConcreteBranch::State::internal_disk(
            old_concrete,
            new_concrete,
            ConcreteBranch::Label::Internal{},
            new_disk,
        );
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ cache_disk_ops(
        lbl: Label,
        new_concrete: ConcreteBranch::State,
        new_cache: Cache::State,
        new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    ) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v;
        require ConcreteBranch::State::cache_disk_ops(
            old_concrete,
            new_concrete,
            ConcreteBranch::Label::Internal{},
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        );
        require new_concrete.wf();
        update ephemeral = EphemeralConcreteBranch::Known{ v: new_concrete };
    }}

    transition!{ freeze_map_internal(lbl: Label) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        require pre.in_flight is None;
        let concrete = pre.ephemeral->v;
        require concrete.active_cached_branch().root is None;
        require concrete.sealed_image().wf();
        update in_flight = Option::Some(InFlightConcreteSealedBranchStackImage{
            image: concrete.sealed_image(),
            seq_end: concrete.seq_end,
        });
    }}

    transition!{ freeze_persistent_internal(lbl: Label) {
        require pre.inv();
        require lbl is Internal;
        require pre.ephemeral is Known;
        require pre.in_flight is None;
        update in_flight = Option::Some(InFlightConcreteSealedBranchStackImage{
            image: pre.persistent,
            seq_end: pre.persistent_seq_end,
        });
    }}

    transition!{ commit_start(lbl: Label) {
        require pre.inv();
        require let Label::CommitStart{new_boundary_lsn} = lbl;
        require pre.ephemeral is Known;
        require pre.in_flight is Some;
        require new_boundary_lsn == pre.in_flight.unwrap().seq_end;
    }}

    transition!{ commit_complete(lbl: Label) {
        require pre.inv();
        require lbl is CommitComplete;
        require pre.in_flight is Some;
        update persistent = pre.in_flight.unwrap().image;
        update persistent_seq_end = pre.in_flight.unwrap().seq_end;
        update in_flight = Option::None;
    }}

    transition!{ crash(lbl: Label) {
        require pre.inv();
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.in_flight is Some;
        update ephemeral = EphemeralConcreteBranch::Unknown;
        update in_flight = Option::None;
        update persistent = if keep_in_flight {
            pre.in_flight.unwrap().image
        } else {
            pre.persistent
        };
        update persistent_seq_end = if keep_in_flight {
            pre.in_flight.unwrap().seq_end
        } else {
            pre.persistent_seq_end
        };
    }}

    pub open spec(checked) fn image_compatible(self) -> bool
    {
        &&& self.in_flight is Some ==> self.persistent_seq_end <= self.in_flight.unwrap().seq_end
        &&& self.ephemeral is Known ==> self.persistent_seq_end <= self.ephemeral->v.seq_end
        &&& self.ephemeral is Known && self.in_flight is Some
            ==> self.in_flight.unwrap().seq_end <= self.ephemeral->v.seq_end
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& self.image_compatible()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State) {
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, reads: Map<Address, RawPage>, query_receipts: Seq<Option<LoadedPathReceipt>>) {
        reveal(ConcreteBranch::State::query);
        assert(new_concrete == pre.ephemeral->v);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(append_to_active)]
    fn append_to_active_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, receipt: LoadedPathReceipt, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::append);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(append_to_empty)]
    fn append_to_empty_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, writes: Map<Address, RawPage>, init_root: Address, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::append_to_empty);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(grow)]
    fn grow_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, new_root_addr: Address, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::grow);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(split)]
    fn split_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, receipt: LoadedPathReceipt, new_child_addr: Address, pivot: Key, split_arg: SplitArg, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::split);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(seal)]
    fn seal_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, aux_ptr: Pointer, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::seal);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(fill_au)]
    fn fill_au_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, aus: Set<AU>) {
        reveal(ConcreteBranch::State::fill_au);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(internal_cache)]
    fn internal_cache_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::internal_cache);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(internal_disk)]
    fn internal_disk_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, new_disk: AsyncDisk::State) {
        reveal(ConcreteBranch::State::internal_disk);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(cache_disk_ops)]
    fn cache_disk_ops_inductive(pre: Self, post: Self, lbl: Label, new_concrete: ConcreteBranch::State, new_cache: Cache::State, new_disk: AsyncDisk::State, cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>, disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>) {
        reveal(ConcreteBranch::State::cache_disk_ops);
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(freeze_map_internal)]
    fn freeze_map_internal_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(freeze_persistent_internal)]
    fn freeze_persistent_internal_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.image_compatible());
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.image_compatible());
    }
}}

impl CrashAwareConcreteBranch::State {
    pub open spec fn wf(self) -> bool
    {
        &&& self.persistent.wf()
        &&& self.in_flight is Some ==> self.in_flight.unwrap().image.wf()
        &&& self.ephemeral is Unknown ==> self.in_flight is None
        &&& self.ephemeral is Known ==> self.ephemeral->v.wf()
    }
}

// Future layer note: a unified raw-disk crash-aware branch machine should own
// the shared disk/cache state and refine to this image-based layer by proving
// raw page projections produce these ConcreteSealedBranchStackImage values.

}
