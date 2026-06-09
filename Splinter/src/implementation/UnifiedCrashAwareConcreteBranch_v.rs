// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;

use verus_state_machines_macros::state_machine;

use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
use crate::allocation_layer::Likes_v::restrict_domain_au;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::{CachedBranch, LoadedPathReceipt};
use crate::implementation::ConcreteBranch_v::{ConcreteBranch, to_branch_nodes};
use crate::implementation::CrashAwareConcreteBranch_v::{
    ConcreteSealedBranchStackImage, EphemeralConcreteBranch,
};
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::spec::Messages_t::Message;

verus! {

pub struct UnifiedSealedBranchStackImage {
    pub sealed_roots: Seq<Address>,
}

pub open spec fn empty_unified_sealed_branch_stack_image() -> UnifiedSealedBranchStackImage
{
    UnifiedSealedBranchStackImage{
        sealed_roots: Seq::empty(),
    }
}

pub struct FrozenUnifiedSealedBranchStackImage {
    pub image: UnifiedSealedBranchStackImage,
    pub seq_end: nat,
}

pub open spec fn empty_unified_disk() -> AsyncDisk::State
{
    AsyncDisk::State{
        requests: Map::empty(),
        responses: Map::empty(),
        content: Map::empty(),
    }
}

pub open spec fn projected_raw_pages(cache: Cache::State, disk: AsyncDisk::State) -> Map<Address, RawPage>
{
    ConcreteBranch::State::available_raw_pages_from(cache, disk)
}

pub open spec fn projected_branch_nodes(cache: Cache::State, disk: AsyncDisk::State) -> Map<Address, BranchNode>
{
    to_branch_nodes(projected_raw_pages(cache, disk))
}

pub open spec fn projected_branch_nodes_from_disk(disk: AsyncDisk::State) -> Map<Address, BranchNode>
{
    to_branch_nodes(disk.content)
}

pub open spec fn projected_sealed_disk(
    sealed_roots: Seq<Address>,
    cache: Cache::State,
    disk: AsyncDisk::State,
) -> BufferDisk<BranchNode>
{
    let nodes = projected_branch_nodes(cache, disk);
    let full_disk = BufferDisk{ entries: nodes };
    let branch_summary = full_disk.build_branch_summary(sealed_roots.to_set());
    let sealed_domain = restrict_domain_au(nodes, summary_aus(branch_summary));
    BufferDisk{ entries: nodes.restrict(sealed_domain) }
}

pub open spec fn projected_sealed_disk_from_disk(
    sealed_roots: Seq<Address>,
    disk: AsyncDisk::State,
) -> BufferDisk<BranchNode>
{
    let nodes = projected_branch_nodes_from_disk(disk);
    let full_disk = BufferDisk{ entries: nodes };
    let branch_summary = full_disk.build_branch_summary(sealed_roots.to_set());
    let sealed_domain = restrict_domain_au(nodes, summary_aus(branch_summary));
    BufferDisk{ entries: nodes.restrict(sealed_domain) }
}

impl UnifiedSealedBranchStackImage {
    pub open spec fn i(self, cache: Cache::State, disk: AsyncDisk::State) -> ConcreteSealedBranchStackImage
    {
        ConcreteSealedBranchStackImage{
            sealed_roots: self.sealed_roots,
            sealed_disk: projected_sealed_disk(self.sealed_roots, cache, disk),
        }
    }

    pub open spec fn wf(self, cache: Cache::State, disk: AsyncDisk::State) -> bool
    {
        self.i(cache, disk).wf()
    }

    pub open spec fn i_disk(self, disk: AsyncDisk::State) -> ConcreteSealedBranchStackImage
    {
        ConcreteSealedBranchStackImage{
            sealed_roots: self.sealed_roots,
            sealed_disk: projected_sealed_disk_from_disk(self.sealed_roots, disk),
        }
    }

    pub open spec fn wf_disk(self, disk: AsyncDisk::State) -> bool
    {
        self.i_disk(disk).wf()
    }
}

pub struct UnifiedConcreteBranchState {
    pub cached_branches: Seq<CachedBranch::State>,
    pub branch_summary: Map<AU, Summary>,
    pub seq_end: nat,
    pub mini_allocator: MiniAllocator,
    pub outstanding_cache_reqs: Map<ID, Address>,
}

impl UnifiedConcreteBranchState {
    pub open spec fn to_concrete(self, cache: Cache::State, disk: AsyncDisk::State) -> ConcreteBranch::State
    {
        ConcreteBranch::State{
            cached_branches: self.cached_branches,
            branch_summary: self.branch_summary,
            seq_end: self.seq_end,
            mini_allocator: self.mini_allocator,
            cache,
            disk,
            outstanding_cache_reqs: self.outstanding_cache_reqs,
        }
    }

    pub open spec fn wf(self, cache: Cache::State, disk: AsyncDisk::State) -> bool
    {
        self.to_concrete(cache, disk).wf()
    }

    pub open spec fn unified_sealed_image(self) -> UnifiedSealedBranchStackImage
    {
        UnifiedSealedBranchStackImage{
            sealed_roots: Seq::new(
                if self.cached_branches.len() == 0 {
                    0
                } else {
                    (self.cached_branches.len() - 1) as nat
                },
                |i: int| {
                    if self.cached_branches[i].root is Some {
                        self.cached_branches[i].root.unwrap()
                    } else {
                        Address{au: 0, page: 0}
                    }
                },
            ),
        }
    }

    pub open spec fn unified_image_consistent(self, cache: Cache::State, disk: AsyncDisk::State) -> bool
    {
        self.to_concrete(cache, disk).unified_image_consistent()
    }
}

pub enum UnifiedEphemeralConcreteBranch {
    Unknown,
    Known{ v: UnifiedConcreteBranchState },
}

impl ConcreteBranch::State {
    pub open spec fn unified_sealed_image(self) -> UnifiedSealedBranchStackImage
    {
        UnifiedSealedBranchStackImage{
            sealed_roots: self.sealed_roots_i(),
        }
    }

    pub open spec fn unified_image_consistent(self) -> bool
    {
        self.sealed_image() == self.unified_sealed_image().i(self.cache, self.disk)
    }
}

state_machine!{ UnifiedCrashAwareConcreteBranch {
    fields {
        pub persistent: UnifiedSealedBranchStackImage,
        pub persistent_seq_end: nat,
        pub ephemeral: UnifiedEphemeralConcreteBranch,
        pub frozen: Option<FrozenUnifiedSealedBranchStackImage>,
        pub cache: Option<Cache::State>,
        pub disk: AsyncDisk::State,
    }

    pub enum Label {
        LoadEphemeral{ free_aus: Set<AU> },
        Query{ branch_idx: nat, key: Key, msg: Message },
        Append{ keys: Seq<Key>, msgs: Seq<Message> },
        Internal{allocs: Set<AU>, deallocs: Set<AU>},
        CommitStart{ new_boundary_lsn: nat, frozen_image: FrozenUnifiedSealedBranchStackImage },
        CommitComplete,
        Crash{ keep_in_flight: bool },
    }

    init!{ initialize(cache: Cache::State, disk: AsyncDisk::State) {
        require cache.inv();
        require disk.inv();
        require disk.requests.is_empty();
        require disk.responses.is_empty();
        require empty_unified_sealed_branch_stack_image().wf_disk(disk);
        require empty_unified_sealed_branch_stack_image().i_disk(disk)
            == ConcreteSealedBranchStackImage{
                sealed_roots: Seq::empty(),
                sealed_disk: BufferDisk{ entries: Map::empty() },
            };
        require empty_unified_sealed_branch_stack_image().wf(cache, disk);
        require empty_unified_sealed_branch_stack_image().i(cache, disk)
            == ConcreteSealedBranchStackImage{
                sealed_roots: Seq::empty(),
                sealed_disk: BufferDisk{ entries: Map::empty() },
            };

        init persistent = empty_unified_sealed_branch_stack_image();
        init persistent_seq_end = 0;
        init ephemeral = UnifiedEphemeralConcreteBranch::Unknown;
        init frozen = Option::None;
        init cache = Option::None;
        init disk = disk;
    }}

    transition!{ load_ephemeral(lbl: Label, new_ephemeral: UnifiedConcreteBranchState, new_cache: Cache::State, cache_slots: nat) {
        require let Label::LoadEphemeral{free_aus} = lbl;
        require pre.ephemeral is Unknown;
        require pre.cache is None;
        require pre.frozen is None;
        require Cache::State::initialize(new_cache, cache_slots);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
        require new_concrete.loads_from_image(pre.persistent.i_disk(pre.disk), pre.persistent_seq_end, free_aus);
        require new_concrete.unified_image_consistent();

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update cache = Option::Some(new_cache);
    }}

    transition!{ query(
        lbl: Label,
        reads: Map<Address, RawPage>,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
    ) {
        require let Label::Query{branch_idx, key, msg} = lbl;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let concrete_lbl = ConcreteBranch::Label::Query{branch_idx, key, msg};
        require ConcreteBranch::State::query(old_concrete, old_concrete, concrete_lbl, reads, query_receipts);
    }}

    transition!{ append_to_active(
        lbl: Label,
        new_ephemeral: UnifiedConcreteBranchState,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: Cache::State,
    ) {
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
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
        require new_concrete.unified_image_consistent();
        require pre.images_wf_with(new_cache, pre.disk);
        require pre.images_stable_with(new_cache, pre.disk);

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update cache = Option::Some(new_cache);
    }}

    transition!{ append_to_empty(
        lbl: Label,
        new_ephemeral: UnifiedConcreteBranchState,
        writes: Map<Address, RawPage>,
        init_root: Address,
        new_cache: Cache::State,
    ) {
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
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
        require new_concrete.unified_image_consistent();
        require pre.images_wf_with(new_cache, pre.disk);
        require pre.images_stable_with(new_cache, pre.disk);

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update cache = Option::Some(new_cache);
    }}

    transition!{ grow(
        lbl: Label,
        new_ephemeral: UnifiedConcreteBranchState,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_root_addr: Address,
        new_cache: Cache::State,
    ) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
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
        require new_concrete.unified_image_consistent();
        require pre.images_wf_with(new_cache, pre.disk);
        require pre.images_stable_with(new_cache, pre.disk);

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update cache = Option::Some(new_cache);
    }}

    transition!{ split(
        lbl: Label,
        new_ephemeral: UnifiedConcreteBranchState,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_child_addr: Address,
        pivot: Key,
        split_arg: SplitArg,
        new_cache: Cache::State,
    ) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
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
        require new_concrete.unified_image_consistent();
        require pre.images_wf_with(new_cache, pre.disk);
        require pre.images_stable_with(new_cache, pre.disk);

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update cache = Option::Some(new_cache);
    }}

    transition!{ seal(
        lbl: Label,
        new_ephemeral: UnifiedConcreteBranchState,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        aux_ptr: Pointer,
        new_cache: Cache::State,
    ) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require pre.ephemeral is Known;
        require deallocs == pre.ephemeral->v.mini_allocator.removable_aus();
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
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
        require new_concrete.unified_image_consistent();
        require pre.images_wf_with(new_cache, pre.disk);
        require pre.images_stable_with(new_cache, pre.disk);

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update cache = Option::Some(new_cache);
    }}

    transition!{ fill_au(lbl: Label, new_ephemeral: UnifiedConcreteBranchState, aus: Set<AU>) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == aus;
        require deallocs == Set::<AU>::empty();
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(pre.cache.unwrap(), pre.disk);
        let concrete_lbl = ConcreteBranch::Label::FillAU{aus};
        require ConcreteBranch::State::fill_au(old_concrete, new_concrete, concrete_lbl);
        require new_concrete.wf();
        require new_concrete.unified_image_consistent();

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
    }}

    transition!{ internal_cache(lbl: Label, new_ephemeral: UnifiedConcreteBranchState, new_cache: Cache::State) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
        require ConcreteBranch::State::internal_cache(
            old_concrete,
            new_concrete,
            ConcreteBranch::Label::Internal{},
            new_cache,
        );
        require new_concrete.wf();
        require new_concrete.unified_image_consistent();
        require pre.images_wf_with(new_cache, pre.disk);
        require pre.images_stable_with(new_cache, pre.disk);

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update cache = Option::Some(new_cache);
    }}

    transition!{ internal_disk(lbl: Label, new_ephemeral: UnifiedConcreteBranchState, new_disk: AsyncDisk::State) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(pre.cache.unwrap(), new_disk);
        require ConcreteBranch::State::internal_disk(
            old_concrete,
            new_concrete,
            ConcreteBranch::Label::Internal{},
            new_disk,
        );
        require new_concrete.wf();
        require new_concrete.unified_image_consistent();
        require pre.images_wf_with(pre.cache.unwrap(), new_disk);
        require pre.images_stable_with(pre.cache.unwrap(), new_disk);

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update disk = new_disk;
    }}

    transition!{ cache_disk_ops(
        lbl: Label,
        new_ephemeral: UnifiedConcreteBranchState,
        new_cache: Cache::State,
        new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    ) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require pre.ephemeral is Known;
        let old_concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        let new_concrete = new_ephemeral.to_concrete(new_cache, new_disk);
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
        require new_concrete.unified_image_consistent();
        require pre.images_wf_with(new_cache, new_disk);
        require pre.images_stable_with(new_cache, new_disk);

        update ephemeral = UnifiedEphemeralConcreteBranch::Known{ v: new_ephemeral };
        update cache = Option::Some(new_cache);
        update disk = new_disk;
    }}

    transition!{ freeze_map_internal(lbl: Label) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require pre.ephemeral is Known;
        let concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        require concrete.active_cached_branch().root is None;
        require concrete.sealed_image().wf();
        require concrete.unified_sealed_image().wf_disk(pre.disk);
        require concrete.unified_sealed_image().i(pre.cache.unwrap(), pre.disk)
            == concrete.unified_sealed_image().i_disk(pre.disk);
    }}

    transition!{ commit_start_ephemeral(lbl: Label) {
        require let Label::CommitStart{new_boundary_lsn, frozen_image} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        let concrete = pre.ephemeral->v.to_concrete(pre.cache.unwrap(), pre.disk);
        require new_boundary_lsn == frozen_image.seq_end;
        require concrete.active_cached_branch().root is None;
        require concrete.sealed_image().wf();
        require concrete.unified_sealed_image().wf_disk(pre.disk);
        require concrete.unified_sealed_image().i(pre.cache.unwrap(), pre.disk)
            == concrete.unified_sealed_image().i_disk(pre.disk);
        require frozen_image.image == concrete.unified_sealed_image();
        require frozen_image.seq_end == concrete.seq_end;
        update frozen = Option::Some(frozen_image);
    }}

    transition!{ commit_start_persistent(lbl: Label) {
        require let Label::CommitStart{new_boundary_lsn, frozen_image} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        require new_boundary_lsn == frozen_image.seq_end;
        require frozen_image.image == pre.persistent;
        require frozen_image.seq_end == pre.persistent_seq_end;
        update frozen = Option::Some(frozen_image);
    }}

    transition!{ commit_complete(lbl: Label) {
        require lbl is CommitComplete;
        require pre.frozen is Some;

        update persistent = pre.frozen.unwrap().image;
        update persistent_seq_end = pre.frozen.unwrap().seq_end;
        update frozen = Option::None;
    }}

    transition!{ crash(
        lbl: Label,
        new_disk: AsyncDisk::State,
    ) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.frozen is Some;
        require AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Crash{});
        let new_persistent = if keep_in_flight {
            pre.frozen.unwrap().image
        } else {
            pre.persistent
        };
        require new_persistent.wf_disk(new_disk);
        require if keep_in_flight {
            pre.frozen.unwrap().image.i_disk(pre.disk)
                == pre.frozen.unwrap().image.i_disk(new_disk)
        } else {
            pre.persistent.i_disk(pre.disk) == pre.persistent.i_disk(new_disk)
        };

        update ephemeral = UnifiedEphemeralConcreteBranch::Unknown;
        update frozen = Option::None;
        update persistent = new_persistent;
        update persistent_seq_end = if keep_in_flight {
            pre.frozen.unwrap().seq_end
        } else {
            pre.persistent_seq_end
        };
        update cache = Option::None;
        update disk = new_disk;
    }}

    pub open spec(checked) fn images_wf_with(self, cache: Cache::State, disk: AsyncDisk::State) -> bool
    {
        &&& self.persistent.wf_disk(disk)
        &&& self.frozen is Some ==> self.frozen.unwrap().image.wf_disk(disk)
    }

    pub open spec(checked) fn images_stable_with(self, cache: Cache::State, disk: AsyncDisk::State) -> bool
    {
        &&& self.persistent.i_disk(self.disk) == self.persistent.i_disk(disk)
        &&& self.frozen is Some ==> self.frozen.unwrap().image.i_disk(self.disk)
            == self.frozen.unwrap().image.i_disk(disk)
    }

    pub open spec(checked) fn known_stack_compatible(self) -> bool
    {
        self.ephemeral is Known ==> self.cache is Some && {
            let concrete = self.ephemeral->v.to_concrete(self.cache.unwrap(), self.disk);
            &&& concrete.wf()
            &&& concrete.unified_image_consistent()
        }
    }

    pub open spec(checked) fn image_compatible(self) -> bool
    {
        &&& self.frozen is Some ==> self.persistent_seq_end <= self.frozen.unwrap().seq_end
        &&& self.ephemeral is Known ==> self.persistent_seq_end <= self.ephemeral->v.seq_end
        &&& self.ephemeral is Known && self.frozen is Some
            ==> self.frozen.unwrap().seq_end <= self.ephemeral->v.seq_end
    }

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& self.known_stack_compatible()
        &&& self.image_compatible()
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, cache: Cache::State, disk: AsyncDisk::State) {
        assert(empty_unified_sealed_branch_stack_image().i_disk(disk)
            == ConcreteSealedBranchStackImage{
                sealed_roots: Seq::empty(),
                sealed_disk: BufferDisk{ entries: Map::empty() },
            });
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, new_cache: Cache::State, cache_slots: nat) {
        Cache::State::initialize_inductive(new_cache, cache_slots);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>, query_receipts: Seq<Option<LoadedPathReceipt>>) {
        reveal(ConcreteBranch::State::query);
        assert(post == pre);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(append_to_active)]
    fn append_to_active_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, receipt: LoadedPathReceipt, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::append);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(append_to_empty)]
    fn append_to_empty_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, writes: Map<Address, RawPage>, init_root: Address, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::append_to_empty);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(grow)]
    fn grow_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, new_root_addr: Address, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::grow);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(split)]
    fn split_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, receipt: LoadedPathReceipt, new_child_addr: Address, pivot: Key, split_arg: SplitArg, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::split);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(seal)]
    fn seal_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, reads: Map<Address, RawPage>, writes: Map<Address, RawPage>, aux_ptr: Pointer, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::seal);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(fill_au)]
    fn fill_au_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, aus: Set<AU>) {
        reveal(ConcreteBranch::State::fill_au);
        let new_concrete = new_ephemeral.to_concrete(pre.cache.unwrap(), pre.disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(internal_cache)]
    fn internal_cache_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, new_cache: Cache::State) {
        reveal(ConcreteBranch::State::internal_cache);
        let new_concrete = new_ephemeral.to_concrete(new_cache, pre.disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(internal_disk)]
    fn internal_disk_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, new_disk: AsyncDisk::State) {
        reveal(ConcreteBranch::State::internal_disk);
        let new_concrete = new_ephemeral.to_concrete(pre.cache.unwrap(), new_disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(cache_disk_ops)]
    fn cache_disk_ops_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: UnifiedConcreteBranchState, new_cache: Cache::State, new_disk: AsyncDisk::State, cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>, disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>) {
        reveal(ConcreteBranch::State::cache_disk_ops);
        let new_concrete = new_ephemeral.to_concrete(new_cache, new_disk);
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(freeze_map_internal)]
    fn freeze_map_internal_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(commit_start_ephemeral)]
    fn commit_start_ephemeral_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(commit_start_persistent)]
    fn commit_start_persistent_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label) {
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State) {
        crate::spec::AsyncDisk_t::inv_next(pre.disk, new_disk, AsyncDisk::Label::Crash{});
        assert(post.wf());
        assert(post.known_stack_compatible());
        assert(post.image_compatible());
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            Self::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        let step = choose |step| UnifiedCrashAwareConcreteBranch::State::next_by(pre, post, lbl, step);
        match step {
            Step::load_ephemeral(new_ephemeral, new_cache, cache_slots) => {
                Self::load_ephemeral_inductive(pre, post, lbl, new_ephemeral, new_cache, cache_slots);
            }
            Step::query(reads, query_receipts) => {
                Self::query_inductive(pre, post, lbl, reads, query_receipts);
            }
            Step::append_to_active(new_ephemeral, reads, writes, receipt, new_cache) => {
                Self::append_to_active_inductive(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                    reads,
                    writes,
                    receipt,
                    new_cache,
                );
            }
            Step::append_to_empty(new_ephemeral, writes, init_root, new_cache) => {
                Self::append_to_empty_inductive(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                    writes,
                    init_root,
                    new_cache,
                );
            }
            Step::grow(new_ephemeral, reads, writes, new_root_addr, new_cache) => {
                Self::grow_inductive(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                    reads,
                    writes,
                    new_root_addr,
                    new_cache,
                );
            }
            Step::split(
                new_ephemeral,
                reads,
                writes,
                receipt,
                new_child_addr,
                pivot,
                split_arg,
                new_cache,
            ) => {
                Self::split_inductive(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                    reads,
                    writes,
                    receipt,
                    new_child_addr,
                    pivot,
                    split_arg,
                    new_cache,
                );
            }
            Step::seal(new_ephemeral, reads, writes, aux_ptr, new_cache) => {
                Self::seal_inductive(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                    reads,
                    writes,
                    aux_ptr,
                    new_cache,
                );
            }
            Step::fill_au(new_ephemeral, aus) => {
                Self::fill_au_inductive(pre, post, lbl, new_ephemeral, aus);
            }
            Step::internal_cache(new_ephemeral, new_cache) => {
                Self::internal_cache_inductive(pre, post, lbl, new_ephemeral, new_cache);
            }
            Step::internal_disk(new_ephemeral, new_disk) => {
                Self::internal_disk_inductive(pre, post, lbl, new_ephemeral, new_disk);
            }
            Step::cache_disk_ops(
                new_ephemeral,
                new_cache,
                new_disk,
                cache_requests,
                cache_responses,
                disk_requests,
                disk_responses,
            ) => {
                Self::cache_disk_ops_inductive(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                    new_cache,
                    new_disk,
                    cache_requests,
                    cache_responses,
                    disk_requests,
                    disk_responses,
                );
            }
            Step::freeze_map_internal() => {
                Self::freeze_map_internal_inductive(pre, post, lbl);
            }
            Step::commit_start_ephemeral() => {
                Self::commit_start_ephemeral_inductive(pre, post, lbl);
            }
            Step::commit_start_persistent() => {
                Self::commit_start_persistent_inductive(pre, post, lbl);
            }
            Step::commit_complete() => {
                Self::commit_complete_inductive(pre, post, lbl);
            }
            Step::crash(new_disk) => {
                Self::crash_inductive(pre, post, lbl, new_disk);
            }
            Step::dummy_to_use_type_params(_) => {
                assert(false);
            }
        }
    }
}}

impl UnifiedCrashAwareConcreteBranch::State {
    pub open spec fn concrete_cache(self) -> Cache::State
    {
        if self.cache is Some {
            self.cache.unwrap()
        } else {
            arbitrary()
        }
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.cache is Some ==> self.cache.unwrap().inv()
        &&& self.disk.inv()
        &&& self.images_wf_with(if self.cache is Some { self.cache.unwrap() } else { arbitrary() }, self.disk)
        &&& self.ephemeral is Unknown ==> self.cache is None && self.frozen is None
        &&& self.ephemeral is Known ==> self.cache is Some
    }
}

}
