// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;

use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::LoadedPathReceipt;
use crate::implementation::ConcreteBranch_v::ConcreteBranch;
use crate::implementation::CrashAwareConcreteBranch_v::{
    empty_concrete_sealed_branch_stack_image, ConcreteSealedBranchStackImage,
    CrashAwareConcreteBranch, EphemeralConcreteBranch,
};
use crate::implementation::CrashAwareConcreteBranchRefinement_v::*;
use crate::implementation::CrashAwareAllocationBranchStackRefinement_v::*;
use crate::implementation::UnifiedCrashAwareConcreteBranch_v::{
    empty_unified_sealed_branch_stack_image, UnifiedCrashAwareConcreteBranch,
    FrozenUnifiedSealedBranchStackImage, UnifiedConcreteBranchState,
    UnifiedEphemeralConcreteBranch, UnifiedSealedBranchStackImage,
};
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::spec::Messages_t::Message;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;

verus! {

impl UnifiedEphemeralConcreteBranch {
    pub open spec fn i(self, cache: Cache::State, disk: AsyncDisk::State) -> EphemeralConcreteBranch
    {
        match self {
            UnifiedEphemeralConcreteBranch::Unknown => EphemeralConcreteBranch::Unknown,
            UnifiedEphemeralConcreteBranch::Known{v} =>
                EphemeralConcreteBranch::Known{ v: v.to_concrete(cache, disk) },
        }
    }
}

pub open spec fn option_unified_image_i(
    image: Option<FrozenUnifiedSealedBranchStackImage>,
    cache: Cache::State,
    disk: AsyncDisk::State,
) -> Option<crate::implementation::CrashAwareConcreteBranch_v::FrozenConcreteSealedBranchStackImage>
{
    match image {
        Option::None => Option::None,
        Option::Some{0: img} => Option::Some(
            crate::implementation::CrashAwareConcreteBranch_v::FrozenConcreteSealedBranchStackImage{
                image: img.image.i_disk(disk),
                seq_end: img.seq_end,
            },
        ),
    }
}

impl UnifiedCrashAwareConcreteBranch::State {
    pub open spec fn refinement_wf(self) -> bool
    {
        &&& self.inv()
        &&& self.i().refinement_wf()
    }

    pub open spec fn i(self) -> CrashAwareConcreteBranch::State
    {
        CrashAwareConcreteBranch::State{
            persistent: self.persistent.i_disk(self.disk),
            persistent_seq_end: self.persistent_seq_end,
            ephemeral: self.ephemeral.i(self.concrete_cache(), self.disk),
            frozen: option_unified_image_i(self.frozen, self.concrete_cache(), self.disk),
        }
    }

    pub open spec fn abstract_i(self) -> AbstractCrashAwareMap::State
    {
        self.i().i().abstract_i()
    }

    pub open spec fn label_to_abstract_map(self, lbl: UnifiedCrashAwareConcreteBranch::Label)
        -> AbstractCrashAwareMap::Label
    {
        self.i().i().label_to_abstract_map(self.i().label_to_stack(self.label_to_concrete(lbl)))
    }

    pub open spec fn label_to_concrete(self, lbl: UnifiedCrashAwareConcreteBranch::Label)
        -> CrashAwareConcreteBranch::Label
    {
        match lbl {
            UnifiedCrashAwareConcreteBranch::Label::LoadEphemeral{free_aus} =>
                CrashAwareConcreteBranch::Label::LoadEphemeral{free_aus},
            UnifiedCrashAwareConcreteBranch::Label::Query{branch_idx, key, msg} =>
                CrashAwareConcreteBranch::Label::Query{branch_idx, key, msg},
            UnifiedCrashAwareConcreteBranch::Label::Append{keys, msgs} =>
                CrashAwareConcreteBranch::Label::Append{keys, msgs},
            UnifiedCrashAwareConcreteBranch::Label::Internal{allocs, deallocs} =>
                CrashAwareConcreteBranch::Label::Internal,
            UnifiedCrashAwareConcreteBranch::Label::CommitStart{new_boundary_lsn, frozen_image} =>
                CrashAwareConcreteBranch::Label::CommitStart{
                    new_boundary_lsn,
                    frozen_image: crate::implementation::CrashAwareConcreteBranch_v::FrozenConcreteSealedBranchStackImage{
                        image: frozen_image.image.i_disk(self.disk),
                        seq_end: frozen_image.seq_end,
                    },
                },
            UnifiedCrashAwareConcreteBranch::Label::CommitComplete =>
                CrashAwareConcreteBranch::Label::CommitComplete,
            UnifiedCrashAwareConcreteBranch::Label::Crash{keep_in_flight} =>
                CrashAwareConcreteBranch::Label::Crash{keep_in_flight},
        }
    }

    pub proof fn state_wf_refines(self)
        requires
            self.inv(),
        ensures
            self.i().inv(),
    {
        if self.ephemeral is Known {
            let concrete = self.ephemeral->v.to_concrete(self.concrete_cache(), self.disk);
            assert(concrete.sealed_image()
                == self.ephemeral->v.unified_sealed_image().i(self.concrete_cache(), self.disk));
        }
        assert(self.i().wf());
        assert(self.i().image_compatible());
        assert(self.i().inv());
    }

    proof fn interpreted_images_stable_with(self, cache: Cache::State, disk: AsyncDisk::State)
        requires
            self.images_stable_with(cache, disk),
        ensures
            self.persistent.i_disk(self.disk) == self.persistent.i_disk(disk),
            option_unified_image_i(self.frozen, self.concrete_cache(), self.disk)
                == option_unified_image_i(self.frozen, cache, disk),
    {
        if self.frozen is Some {
            assert(self.frozen.unwrap().image.i_disk(self.disk)
                == self.frozen.unwrap().image.i_disk(disk));
        }
    }

    pub proof fn init_refines(self, cache: Cache::State, disk: AsyncDisk::State)
        requires
            UnifiedCrashAwareConcreteBranch::State::initialize(self, cache, disk),
        ensures
            CrashAwareConcreteBranch::State::initialize(self.i()),
    {
        reveal(CrashAwareConcreteBranch::State::init_by);
        assert(empty_unified_sealed_branch_stack_image().i_disk(self.disk)
            == empty_concrete_sealed_branch_stack_image());
        assert(CrashAwareConcreteBranch::State::init_by(
            self.i(),
            CrashAwareConcreteBranch::Config::initialize(),
        ));
    }

    pub proof fn load_ephemeral_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareConcreteBranch::Label,
        new_ephemeral: UnifiedConcreteBranchState,
        new_cache: Cache::State,
        cache_slots: nat,
    )
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::load_ephemeral(self, post, lbl, new_ephemeral, new_cache, cache_slots),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(UnifiedCrashAwareConcreteBranch::State::load_ephemeral);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        match lbl {
            UnifiedCrashAwareConcreteBranch::Label::LoadEphemeral{free_aus} => {
                let new_concrete = new_ephemeral.to_concrete(new_cache, self.disk);
                self.state_wf_refines();
                assert(CrashAwareConcreteBranch::State::load_ephemeral(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::load_ephemeral(new_concrete),
                ));
            }
            _ => { assert(false); }
        }
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn query_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareConcreteBranch::Label,
        reads: Map<Address, RawPage>,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
    )
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::query(self, post, lbl, reads, query_receipts),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(UnifiedCrashAwareConcreteBranch::State::query);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        match lbl {
            UnifiedCrashAwareConcreteBranch::Label::Query{branch_idx, key, msg} => {
                let old_concrete = self.ephemeral->v.to_concrete(self.concrete_cache(), self.disk);
                let concrete_lbl = ConcreteBranch::Label::Query{branch_idx, key, msg};
                assert(ConcreteBranch::State::query(
                    old_concrete,
                    old_concrete,
                    concrete_lbl,
                    reads,
                    query_receipts,
                ));
                assert(post == self);
                assert(CrashAwareConcreteBranch::State::query(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    old_concrete,
                    reads,
                    query_receipts,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::query(old_concrete, reads, query_receipts),
                ));
            }
            _ => { assert(false); }
        }
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn append_to_active_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareConcreteBranch::Label,
        new_ephemeral: UnifiedConcreteBranchState,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: Cache::State,
    )
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::append_to_active(
                self, post, lbl, new_ephemeral, reads, writes, receipt, new_cache,
            ),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(UnifiedCrashAwareConcreteBranch::State::append_to_active);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        match lbl {
            UnifiedCrashAwareConcreteBranch::Label::Append{keys, msgs} => {
                let old_concrete = self.ephemeral->v.to_concrete(self.concrete_cache(), self.disk);
                let new_concrete = new_ephemeral.to_concrete(new_cache, self.disk);
                let concrete_lbl = ConcreteBranch::Label::Append{keys, msgs};
                self.interpreted_images_stable_with(new_cache, self.disk);
                assert(CrashAwareConcreteBranch::State::append_to_active(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    reads,
                    writes,
                    receipt,
                    new_cache,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::append_to_active(
                        new_concrete,
                        reads,
                        writes,
                        receipt,
                        new_cache,
                    ),
                ));
            }
            _ => { assert(false); }
        }
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn append_to_empty_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareConcreteBranch::Label,
        new_ephemeral: UnifiedConcreteBranchState,
        writes: Map<Address, RawPage>,
        init_root: Address,
        new_cache: Cache::State,
    )
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::append_to_empty(
                self, post, lbl, new_ephemeral, writes, init_root, new_cache,
            ),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(UnifiedCrashAwareConcreteBranch::State::append_to_empty);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        match lbl {
            UnifiedCrashAwareConcreteBranch::Label::Append{keys, msgs} => {
                let new_concrete = new_ephemeral.to_concrete(new_cache, self.disk);
                self.interpreted_images_stable_with(new_cache, self.disk);
                assert(CrashAwareConcreteBranch::State::append_to_empty(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    writes,
                    init_root,
                    new_cache,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::append_to_empty(
                        new_concrete,
                        writes,
                        init_root,
                        new_cache,
                    ),
                ));
            }
            _ => { assert(false); }
        }
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn internal_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareConcreteBranch::Label,
    )
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::next(self, post, lbl),
            lbl is Internal,
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);

        let step = choose |step| UnifiedCrashAwareConcreteBranch::State::next_by(self, post, lbl, step);
        match step {
            UnifiedCrashAwareConcreteBranch::Step::grow(
                new_ephemeral,
                reads,
                writes,
                new_root_addr,
                new_cache,
            ) => {
                reveal(UnifiedCrashAwareConcreteBranch::State::grow);
                let new_concrete = new_ephemeral.to_concrete(new_cache, self.disk);
                self.interpreted_images_stable_with(new_cache, self.disk);
                assert(CrashAwareConcreteBranch::State::grow(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    reads,
                    writes,
                    new_root_addr,
                    new_cache,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::grow(
                        new_concrete,
                        reads,
                        writes,
                        new_root_addr,
                        new_cache,
                    ),
                ));
            }
            UnifiedCrashAwareConcreteBranch::Step::split(
                new_ephemeral,
                reads,
                writes,
                receipt,
                new_child_addr,
                pivot,
                split_arg,
                new_cache,
            ) => {
                reveal(UnifiedCrashAwareConcreteBranch::State::split);
                let new_concrete = new_ephemeral.to_concrete(new_cache, self.disk);
                self.interpreted_images_stable_with(new_cache, self.disk);
                assert(CrashAwareConcreteBranch::State::split(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    reads,
                    writes,
                    receipt,
                    new_child_addr,
                    pivot,
                    split_arg,
                    new_cache,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::split(
                        new_concrete,
                        reads,
                        writes,
                        receipt,
                        new_child_addr,
                        pivot,
                        split_arg,
                        new_cache,
                    ),
                ));
            }
            UnifiedCrashAwareConcreteBranch::Step::seal(
                new_ephemeral,
                reads,
                writes,
                aux_ptr,
                new_cache,
            ) => {
                reveal(UnifiedCrashAwareConcreteBranch::State::seal);
                let new_concrete = new_ephemeral.to_concrete(new_cache, self.disk);
                self.interpreted_images_stable_with(new_cache, self.disk);
                assert(CrashAwareConcreteBranch::State::seal(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    reads,
                    writes,
                    aux_ptr,
                    new_cache,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::seal(
                        new_concrete,
                        reads,
                        writes,
                        aux_ptr,
                        new_cache,
                    ),
                ));
            }
            UnifiedCrashAwareConcreteBranch::Step::fill_au(new_ephemeral, aus) => {
                reveal(UnifiedCrashAwareConcreteBranch::State::fill_au);
                let new_concrete = new_ephemeral.to_concrete(self.concrete_cache(), self.disk);
                assert(CrashAwareConcreteBranch::State::fill_au(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    aus,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::fill_au(new_concrete, aus),
                ));
            }
            UnifiedCrashAwareConcreteBranch::Step::internal_cache(new_ephemeral, new_cache) => {
                reveal(UnifiedCrashAwareConcreteBranch::State::internal_cache);
                let new_concrete = new_ephemeral.to_concrete(new_cache, self.disk);
                self.interpreted_images_stable_with(new_cache, self.disk);
                assert(CrashAwareConcreteBranch::State::internal_cache(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    new_cache,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::internal_cache(new_concrete, new_cache),
                ));
            }
            UnifiedCrashAwareConcreteBranch::Step::internal_disk(new_ephemeral, new_disk) => {
                reveal(UnifiedCrashAwareConcreteBranch::State::internal_disk);
                let new_concrete = new_ephemeral.to_concrete(self.concrete_cache(), new_disk);
                self.interpreted_images_stable_with(self.concrete_cache(), new_disk);
                assert(CrashAwareConcreteBranch::State::internal_disk(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    new_disk,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::internal_disk(new_concrete, new_disk),
                ));
            }
            UnifiedCrashAwareConcreteBranch::Step::cache_disk_ops(
                new_ephemeral,
                new_cache,
                new_disk,
                cache_requests,
                cache_responses,
                disk_requests,
                disk_responses,
            ) => {
                reveal(UnifiedCrashAwareConcreteBranch::State::cache_disk_ops);
                let new_concrete = new_ephemeral.to_concrete(new_cache, new_disk);
                self.interpreted_images_stable_with(new_cache, new_disk);
                assert(CrashAwareConcreteBranch::State::cache_disk_ops(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    new_concrete,
                    new_cache,
                    new_disk,
                    cache_requests,
                    cache_responses,
                    disk_requests,
                    disk_responses,
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::cache_disk_ops(
                        new_concrete,
                        new_cache,
                        new_disk,
                        cache_requests,
                        cache_responses,
                        disk_requests,
                        disk_responses,
                    ),
                ));
            }
            UnifiedCrashAwareConcreteBranch::Step::freeze_map_internal() => {
                reveal(UnifiedCrashAwareConcreteBranch::State::freeze_map_internal);
                let concrete = self.ephemeral->v.to_concrete(self.concrete_cache(), self.disk);
                assert(concrete.sealed_image()
                    == concrete.unified_sealed_image().i(self.concrete_cache(), self.disk));
                assert(concrete.unified_sealed_image().i(self.concrete_cache(), self.disk)
                    == concrete.unified_sealed_image().i_disk(self.disk));
                assert(concrete.sealed_image()
                    == concrete.unified_sealed_image().i_disk(self.disk));
                assert(CrashAwareConcreteBranch::State::freeze_map_internal(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::freeze_map_internal(),
                ));
            }
            _ => { assert(false); }
        }
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn commit_start_ephemeral_refines(self, post: Self, lbl: UnifiedCrashAwareConcreteBranch::Label)
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::commit_start_ephemeral(self, post, lbl),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(UnifiedCrashAwareConcreteBranch::State::commit_start_ephemeral);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        assert(CrashAwareConcreteBranch::State::commit_start_ephemeral(
            self.i(),
            post.i(),
            self.label_to_concrete(lbl),
        ));
        assert(CrashAwareConcreteBranch::State::next_by(
            self.i(),
            post.i(),
            self.label_to_concrete(lbl),
            CrashAwareConcreteBranch::Step::commit_start_ephemeral(),
        ));
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn commit_start_persistent_refines(self, post: Self, lbl: UnifiedCrashAwareConcreteBranch::Label)
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::commit_start_persistent(self, post, lbl),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(UnifiedCrashAwareConcreteBranch::State::commit_start_persistent);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        assert(CrashAwareConcreteBranch::State::commit_start_persistent(
            self.i(),
            post.i(),
            self.label_to_concrete(lbl),
        ));
        assert(CrashAwareConcreteBranch::State::next_by(
            self.i(),
            post.i(),
            self.label_to_concrete(lbl),
            CrashAwareConcreteBranch::Step::commit_start_persistent(),
        ));
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn commit_complete_refines(self, post: Self, lbl: UnifiedCrashAwareConcreteBranch::Label)
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::commit_complete(self, post, lbl),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(UnifiedCrashAwareConcreteBranch::State::commit_complete);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        assert(CrashAwareConcreteBranch::State::commit_complete(
            self.i(),
            post.i(),
            self.label_to_concrete(lbl),
        ));
        assert(CrashAwareConcreteBranch::State::next_by(
            self.i(),
            post.i(),
            self.label_to_concrete(lbl),
            CrashAwareConcreteBranch::Step::commit_complete(),
        ));
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn crash_refines(
        self,
        post: Self,
        lbl: UnifiedCrashAwareConcreteBranch::Label,
        new_disk: AsyncDisk::State,
    )
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::crash(self, post, lbl, new_disk),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);
        reveal(UnifiedCrashAwareConcreteBranch::State::crash);
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        match lbl {
            UnifiedCrashAwareConcreteBranch::Label::Crash{keep_in_flight} => {
                if keep_in_flight {
                    assert(self.frozen is Some);
                    assert(self.frozen.unwrap().image.i_disk(self.disk)
                        == self.frozen.unwrap().image.i_disk(new_disk));
                } else {
                    assert(self.persistent.i_disk(self.disk)
                        == self.persistent.i_disk(new_disk));
                }
                assert(CrashAwareConcreteBranch::State::crash(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                ));
                assert(CrashAwareConcreteBranch::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_concrete(lbl),
                    CrashAwareConcreteBranch::Step::crash(),
                ));
            }
            _ => { assert(false); }
        }
        assert(CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)));
    }

    pub proof fn next_refines(self, post: Self, lbl: UnifiedCrashAwareConcreteBranch::Label)
        requires
            self.inv(),
            post.inv(),
            UnifiedCrashAwareConcreteBranch::State::next(self, post, lbl),
        ensures
            CrashAwareConcreteBranch::State::next(self.i(), post.i(), self.label_to_concrete(lbl)),
    {
        reveal(UnifiedCrashAwareConcreteBranch::State::next);
        reveal(UnifiedCrashAwareConcreteBranch::State::next_by);

        let step = choose |step| UnifiedCrashAwareConcreteBranch::State::next_by(self, post, lbl, step);
        match step {
            UnifiedCrashAwareConcreteBranch::Step::load_ephemeral(new_ephemeral, new_cache, cache_slots) => {
                self.load_ephemeral_refines(post, lbl, new_ephemeral, new_cache, cache_slots);
            }
            UnifiedCrashAwareConcreteBranch::Step::query(reads, query_receipts) => {
                self.query_refines(post, lbl, reads, query_receipts);
            }
            UnifiedCrashAwareConcreteBranch::Step::append_to_active(new_ephemeral, reads, writes, receipt, new_cache) => {
                self.append_to_active_refines(post, lbl, new_ephemeral, reads, writes, receipt, new_cache);
            }
            UnifiedCrashAwareConcreteBranch::Step::append_to_empty(new_ephemeral, writes, init_root, new_cache) => {
                self.append_to_empty_refines(post, lbl, new_ephemeral, writes, init_root, new_cache);
            }
            UnifiedCrashAwareConcreteBranch::Step::commit_start_ephemeral() => {
                self.commit_start_ephemeral_refines(post, lbl);
            }
            UnifiedCrashAwareConcreteBranch::Step::commit_start_persistent() => {
                self.commit_start_persistent_refines(post, lbl);
            }
            UnifiedCrashAwareConcreteBranch::Step::commit_complete() => {
                self.commit_complete_refines(post, lbl);
            }
            UnifiedCrashAwareConcreteBranch::Step::crash(new_disk) => {
                self.crash_refines(post, lbl, new_disk);
            }
            _ => {
                self.internal_refines(post, lbl);
            }
        }
    }

    pub proof fn next_refines_abstract(self, post: Self, lbl: UnifiedCrashAwareConcreteBranch::Label)
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            UnifiedCrashAwareConcreteBranch::State::next(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(
                self.abstract_i(),
                post.abstract_i(),
                self.label_to_abstract_map(lbl),
            ),
    {
        self.next_refines(post, lbl);
        self.i().next_refines(post.i(), self.label_to_concrete(lbl));
        self.i().i().next_refines(post.i().i(), self.i().label_to_stack(self.label_to_concrete(lbl)));
    }
}

}
