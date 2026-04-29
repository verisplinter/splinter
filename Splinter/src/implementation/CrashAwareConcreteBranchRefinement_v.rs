// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::map::*;

use crate::allocation_layer::AllocationBranch_v::{AllocationBranch, BranchNode, Summary};
use crate::betree::BufferDisk_v::BufferDisk;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::LoadedPathReceipt;
use crate::implementation::ConcreteBranch_v::ConcreteBranch;
use crate::implementation::ConcreteBranchMapRefinement_v::*;
use crate::implementation::CrashAwareAllocationBranchStack_v::{
    load_stack, CrashAwareAllocationBranchStack, EphemeralAllocationBranchStack,
    InFlightAllocationBranchStack,
};
use crate::implementation::CrashAwareConcreteBranch_v::{
    empty_concrete_sealed_branch_stack_image, ConcreteSealedBranchStackImage,
    CrashAwareConcreteBranch, EphemeralConcreteBranch, InFlightConcreteSealedBranchStackImage,
};
use crate::implementation::AllocationBranchStack_v::{
    AllocationBranchStack, SealedAllocationBranchStack,
};
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::ID;
use crate::spec::Messages_t::Message;

verus! {

impl ConcreteSealedBranchStackImage {
    pub open spec fn i(self) -> SealedAllocationBranchStack
    {
        SealedAllocationBranchStack{
            sealed_roots: self.sealed_roots,
            sealed_disk: self.sealed_disk,
        }
    }

    pub proof fn image_i_wf(self)
        requires
            self.wf(),
        ensures
            self.i().wf(),
    {
        assert(self.i().sealed_roots == self.sealed_roots);
        assert(self.i().sealed_disk == self.sealed_disk);
        assert(self.i().branch_summary() == self.sealed_disk.build_branch_summary(self.sealed_roots.to_set()));
        assert(self.i().wf());
    }
}

impl ConcreteBranch::State {
    pub proof fn sealed_image_matches_i(self)
        requires
            self.refinement_wf(),
        ensures
            self.sealed_image().i() == self.i().sealed_stack,
    {
        assert(self.sealed_image().i() == self.i().sealed_stack);
    }

    pub proof fn load_from_image_matches_stack(
        self,
        image: ConcreteSealedBranchStackImage,
        image_seq_end: nat,
        init_aus: Set<AU>,
    )
        requires
            image.wf(),
            self.loads_from_image(image, image_seq_end, init_aus),
            self.refinement_wf(),
        ensures
            self.i() == load_stack(image.i(), image_seq_end, init_aus),
    {
        assert(self.sealed_image().i() == image.i());
        assert(self.i().sealed_stack == image.i());
        assert(self.i().wf());
        assert(self.branch_summary == self.i().sealed_stack.branch_summary());
        assert(self.active_cached_branch().root == Option::<Address>::None);
        assert(self.overlay_branch() == Option::<crate::betree::LinkedBranch_v::LinkedBranch<Summary>>::None);
        assert(self.active_branch_i() == AllocationBranch{
            sealed: false,
            branch: None,
            mini_allocator: self.mini_allocator,
        });
        assert(self.active_branch_i() == AllocationBranch::new(init_aus));
        assert(self.i() == load_stack(image.i(), image_seq_end, init_aus));
    }
}

impl EphemeralConcreteBranch {
    pub open spec fn i(self) -> EphemeralAllocationBranchStack
    {
        match self {
            EphemeralConcreteBranch::Unknown => EphemeralAllocationBranchStack::Unknown,
            EphemeralConcreteBranch::Known{v} =>
                EphemeralAllocationBranchStack::Known{ v: v.i() },
        }
    }
}

pub open spec fn option_image_i(
    image: Option<InFlightConcreteSealedBranchStackImage>,
) -> Option<InFlightAllocationBranchStack>
{
    match image {
        Option::None => Option::None,
        Option::Some{0: img} => Option::Some(InFlightAllocationBranchStack{
            sealed_stack: img.image.i(),
            seq_end: img.seq_end,
        }),
    }
}

impl CrashAwareConcreteBranch::State {
    pub open spec fn refinement_wf(self) -> bool
    {
        &&& self.inv()
        &&& self.ephemeral is Known ==> self.ephemeral->v.refinement_wf()
    }

    pub open spec fn i(self) -> CrashAwareAllocationBranchStack::State
    {
        CrashAwareAllocationBranchStack::State{
            persistent: self.persistent.i(),
            persistent_seq_end: self.persistent_seq_end,
            ephemeral: self.ephemeral.i(),
            in_flight: option_image_i(self.in_flight),
        }
    }

    pub open spec fn label_to_stack(self, lbl: CrashAwareConcreteBranch::Label)
        -> CrashAwareAllocationBranchStack::Label
    {
        match lbl {
            CrashAwareConcreteBranch::Label::LoadEphemeral{init_aus} =>
                CrashAwareAllocationBranchStack::Label::LoadEphemeral{init_aus},
            CrashAwareConcreteBranch::Label::Query{branch_idx, key, msg} =>
                CrashAwareAllocationBranchStack::Label::Query{key, msg},
            CrashAwareConcreteBranch::Label::Append{keys, msgs} =>
                CrashAwareAllocationBranchStack::Label::Append{keys, msgs},
            CrashAwareConcreteBranch::Label::Internal =>
                CrashAwareAllocationBranchStack::Label::Internal,
            CrashAwareConcreteBranch::Label::CommitStart{new_boundary_lsn} =>
                CrashAwareAllocationBranchStack::Label::CommitStart{new_boundary_lsn},
            CrashAwareConcreteBranch::Label::CommitComplete =>
                CrashAwareAllocationBranchStack::Label::CommitComplete,
            CrashAwareConcreteBranch::Label::Crash{keep_in_flight} =>
                CrashAwareAllocationBranchStack::Label::Crash{keep_in_flight},
        }
    }

    pub proof fn image_wf_refines_to_stack_wf(self)
        requires
            self.refinement_wf(),
        ensures
            self.i().wf(),
    {
        self.persistent.image_i_wf();
        if self.in_flight is Some {
            self.in_flight.unwrap().image.image_i_wf();
        }
        if self.ephemeral is Known {
            assert(self.ephemeral->v.i().wf());
        }
    }

    pub proof fn init_refines(self)
        requires
            CrashAwareConcreteBranch::State::initialize(self),
        ensures
            CrashAwareAllocationBranchStack::State::initialize(self.i()),
    {
        reveal(CrashAwareAllocationBranchStack::State::init_by);
        assert(empty_concrete_sealed_branch_stack_image().i()
            == crate::implementation::CrashAwareAllocationBranchStack_v::empty_sealed_stack());
        assert(CrashAwareAllocationBranchStack::State::init_by(
            self.i(),
            CrashAwareAllocationBranchStack::Config::initialize(),
        ));
    }

    pub proof fn load_ephemeral_refines(
        self,
        post: Self,
        lbl: CrashAwareConcreteBranch::Label,
        new_concrete: ConcreteBranch::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::load_ephemeral(self, post, lbl, new_concrete),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::load_ephemeral);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        match lbl {
            CrashAwareConcreteBranch::Label::LoadEphemeral{init_aus} => {
                self.image_wf_refines_to_stack_wf();
                post.image_wf_refines_to_stack_wf();
                new_concrete.load_from_image_matches_stack(
                    self.persistent,
                    self.persistent_seq_end,
                    init_aus,
                );
                assert(post.i().ephemeral == EphemeralAllocationBranchStack::Known{ v: new_concrete.i() });
                assert(new_concrete.i() == load_stack(self.persistent.i(), self.persistent_seq_end, init_aus));
                assert(CrashAwareAllocationBranchStack::State::load_ephemeral(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_to_stack(lbl),
                    CrashAwareAllocationBranchStack::Step::load_ephemeral(),
                ));
            }
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    pub proof fn query_refines(
        self,
        post: Self,
        lbl: CrashAwareConcreteBranch::Label,
        new_concrete: ConcreteBranch::State,
        reads: Map<Address, RawPage>,
        query_receipts: Seq<Option<LoadedPathReceipt>>,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::query(self, post, lbl, new_concrete, reads, query_receipts),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::query);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        match lbl {
            CrashAwareConcreteBranch::Label::Query{branch_idx, key, msg} => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Query{branch_idx, key, msg};
                old_concrete.query_refines(new_concrete, concrete_lbl, reads, query_receipts);
                assert(self.i().ephemeral->v == old_concrete.i());
                let stack_lbl = old_concrete.label_to_stack(concrete_lbl);
                assert(stack_lbl == AllocationBranchStack::Label::QueryLabel{key, msg});
                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                let stack_step = choose |step| AllocationBranchStack::State::next_by(
                    old_concrete.i(),
                    new_concrete.i(),
                    stack_lbl,
                    step,
                );
                match stack_step {
                    AllocationBranchStack::Step::query_step() => {
                        assert(CrashAwareAllocationBranchStack::State::query(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            new_concrete.i(),
                        ));
                        assert(CrashAwareAllocationBranchStack::State::next_by(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            CrashAwareAllocationBranchStack::Step::query(new_concrete.i()),
                        ));
                    }
                    _ => { assert(false); }
                }
            }
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    pub proof fn append_to_active_refines(
        self,
        post: Self,
        lbl: CrashAwareConcreteBranch::Label,
        new_concrete: ConcreteBranch::State,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        receipt: LoadedPathReceipt,
        new_cache: Cache::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::append_to_active(
                self, post, lbl, new_concrete, reads, writes, receipt, new_cache,
            ),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::append_to_active);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        match lbl {
            CrashAwareConcreteBranch::Label::Append{keys, msgs} => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Append{keys, msgs};
                old_concrete.append_to_active_refines(
                    new_concrete,
                    concrete_lbl,
                    reads,
                    writes,
                    receipt,
                    new_cache,
                );
                assert(self.i().ephemeral->v == old_concrete.i());
                let stack_lbl = old_concrete.label_to_stack(concrete_lbl);
                assert(stack_lbl == AllocationBranchStack::Label::AppendLabel{keys, msgs});
                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                let stack_step = choose |step| AllocationBranchStack::State::next_by(
                    old_concrete.i(),
                    new_concrete.i(),
                    stack_lbl,
                    step,
                );
                match stack_step {
                    AllocationBranchStack::Step::append_to_active(path) => {
                        assert(CrashAwareAllocationBranchStack::State::append_to_active(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            new_concrete.i(),
                            path,
                        ));
                        assert(CrashAwareAllocationBranchStack::State::next_by(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            CrashAwareAllocationBranchStack::Step::append_to_active(new_concrete.i(), path),
                        ));
                    }
                    AllocationBranchStack::Step::append_to_empty(init_root) => {
                        assert(CrashAwareAllocationBranchStack::State::append_to_empty(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            new_concrete.i(),
                            init_root,
                        ));
                        assert(CrashAwareAllocationBranchStack::State::next_by(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            CrashAwareAllocationBranchStack::Step::append_to_empty(new_concrete.i(), init_root),
                        ));
                    }
                    _ => { assert(false); }
                }
            }
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    pub proof fn append_to_empty_refines(
        self,
        post: Self,
        lbl: CrashAwareConcreteBranch::Label,
        new_concrete: ConcreteBranch::State,
        writes: Map<Address, RawPage>,
        init_root: Address,
        new_cache: Cache::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::append_to_empty(
                self, post, lbl, new_concrete, writes, init_root, new_cache,
            ),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::append_to_empty);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        match lbl {
            CrashAwareConcreteBranch::Label::Append{keys, msgs} => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Append{keys, msgs};
                old_concrete.append_to_empty_refines(
                    new_concrete,
                    concrete_lbl,
                    writes,
                    init_root,
                    new_cache,
                );
                assert(self.i().ephemeral->v == old_concrete.i());
                let stack_lbl = old_concrete.label_to_stack(concrete_lbl);
                assert(stack_lbl == AllocationBranchStack::Label::AppendLabel{keys, msgs});
                reveal(AllocationBranchStack::State::next);
                reveal(AllocationBranchStack::State::next_by);
                let stack_step = choose |step| AllocationBranchStack::State::next_by(
                    old_concrete.i(),
                    new_concrete.i(),
                    stack_lbl,
                    step,
                );
                match stack_step {
                    AllocationBranchStack::Step::append_to_active(path) => {
                        assert(CrashAwareAllocationBranchStack::State::append_to_active(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            new_concrete.i(),
                            path,
                        ));
                        assert(CrashAwareAllocationBranchStack::State::next_by(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            CrashAwareAllocationBranchStack::Step::append_to_active(new_concrete.i(), path),
                        ));
                    }
                    AllocationBranchStack::Step::append_to_empty(root) => {
                        assert(CrashAwareAllocationBranchStack::State::append_to_empty(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            new_concrete.i(),
                            root,
                        ));
                        assert(CrashAwareAllocationBranchStack::State::next_by(
                            self.i(),
                            post.i(),
                            self.label_to_stack(lbl),
                            CrashAwareAllocationBranchStack::Step::append_to_empty(new_concrete.i(), root),
                        ));
                    }
                    _ => { assert(false); }
                }
            }
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    proof fn lift_loaded_internal_stack_next(
        self,
        post: Self,
        old_concrete: ConcreteBranch::State,
        new_concrete: ConcreteBranch::State,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            self.ephemeral == (EphemeralConcreteBranch::Known{ v: old_concrete }),
            post.ephemeral == (EphemeralConcreteBranch::Known{ v: new_concrete }),
            post.persistent == self.persistent,
            post.persistent_seq_end == self.persistent_seq_end,
            post.in_flight == self.in_flight,
            AllocationBranchStack::State::next(
                old_concrete.i(),
                new_concrete.i(),
                AllocationBranchStack::Label::InternalLabel,
            ),
        ensures
            CrashAwareAllocationBranchStack::State::next(
                self.i(),
                post.i(),
                CrashAwareAllocationBranchStack::Label::Internal,
            ),
    {
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        assert(self.i().ephemeral->v == old_concrete.i());

        let stack_step = choose |step| AllocationBranchStack::State::next_by(
            old_concrete.i(),
            new_concrete.i(),
            AllocationBranchStack::Label::InternalLabel,
            step,
        );
        match stack_step {
            AllocationBranchStack::Step::internal_noop() => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_noop(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_concrete.i(),
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_noop(new_concrete.i()),
                ));
            }
            AllocationBranchStack::Step::internal_grow(new_root_addr) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_grow(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_concrete.i(),
                    new_root_addr,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_grow(
                        new_concrete.i(),
                        new_root_addr,
                    ),
                ));
            }
            AllocationBranchStack::Step::internal_split(new_child_addr, path, split_arg) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_split(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_concrete.i(),
                    new_child_addr,
                    path,
                    split_arg,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_split(
                        new_concrete.i(),
                        new_child_addr,
                        path,
                        split_arg,
                    ),
                ));
            }
            AllocationBranchStack::Step::internal_seal(aux_ptr) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_seal(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_concrete.i(),
                    aux_ptr,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_seal(
                        new_concrete.i(),
                        aux_ptr,
                    ),
                ));
            }
            AllocationBranchStack::Step::internal_fill_au(aus) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_fill_au(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_concrete.i(),
                    aus,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_fill_au(
                        new_concrete.i(),
                        aus,
                    ),
                ));
            }
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(
            self.i(),
            post.i(),
            CrashAwareAllocationBranchStack::Label::Internal,
        ));
    }

    proof fn freeze_map_internal_refines(self, post: Self, lbl: CrashAwareConcreteBranch::Label)
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::freeze_map_internal(self, post, lbl),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::freeze_map_internal);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        let concrete = self.ephemeral->v;
        concrete.sealed_image_matches_i();
        assert(concrete.active_cached_branch().root == Option::<Address>::None);
        assert(concrete.overlay_branch() == Option::<crate::betree::LinkedBranch_v::LinkedBranch<Summary>>::None);
        assert(concrete.i().active_branch.branch
            == Option::<crate::betree::LinkedBranch_v::LinkedBranch<Summary>>::None);
        assert(concrete.i().freeze_snapshot() == concrete.sealed_image().i());
        assert(AllocationBranchStack::State::freeze_as(
            concrete.i(),
            concrete.i(),
            AllocationBranchStack::Label::FreezeAsLabel{
                sealed_stack: concrete.sealed_image().i(),
            },
        ));
        assert(CrashAwareAllocationBranchStack::State::freeze_map_internal(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
        ));
        assert(CrashAwareAllocationBranchStack::State::next_by(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
            CrashAwareAllocationBranchStack::Step::freeze_map_internal(),
        ));
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    proof fn freeze_persistent_internal_refines(self, post: Self, lbl: CrashAwareConcreteBranch::Label)
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::freeze_persistent_internal(self, post, lbl),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::freeze_persistent_internal);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        assert(CrashAwareAllocationBranchStack::State::freeze_persistent_internal(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
        ));
        assert(CrashAwareAllocationBranchStack::State::next_by(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
            CrashAwareAllocationBranchStack::Step::freeze_persistent_internal(),
        ));
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    pub proof fn internal_refines(
        self,
        post: Self,
        lbl: CrashAwareConcreteBranch::Label,
    )
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::next(self, post, lbl),
            lbl is Internal,
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);

        let step = choose |step| CrashAwareConcreteBranch::State::next_by(self, post, lbl, step);
        match step {
            CrashAwareConcreteBranch::Step::grow(new_concrete, reads, writes, new_root_addr, new_cache) => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Grow{new_root_addr};
                old_concrete.grow_refines(new_concrete, concrete_lbl, reads, writes, new_cache);
                self.lift_loaded_internal_stack_next(post, old_concrete, new_concrete);
            }
            CrashAwareConcreteBranch::Step::split(
                new_concrete,
                reads,
                writes,
                receipt,
                new_child_addr,
                pivot,
                split_arg,
                new_cache,
            ) => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Split{new_child_addr, pivot, split_arg};
                old_concrete.split_refines(new_concrete, concrete_lbl, reads, writes, receipt, new_cache);
                self.lift_loaded_internal_stack_next(post, old_concrete, new_concrete);
            }
            CrashAwareConcreteBranch::Step::seal(new_concrete, reads, writes, aux_ptr, new_cache) => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Seal{aux_ptr};
                old_concrete.seal_refines(new_concrete, concrete_lbl, reads, writes, new_cache);
                self.lift_loaded_internal_stack_next(post, old_concrete, new_concrete);
            }
            CrashAwareConcreteBranch::Step::fill_au(new_concrete, aus) => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::FillAU{aus};
                old_concrete.fill_au_refines(new_concrete, concrete_lbl);
                self.lift_loaded_internal_stack_next(post, old_concrete, new_concrete);
            }
            CrashAwareConcreteBranch::Step::internal_cache(new_concrete, new_cache) => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Internal{};
                old_concrete.internal_cache_refines(new_concrete, concrete_lbl, new_cache);
                self.lift_loaded_internal_stack_next(post, old_concrete, new_concrete);
            }
            CrashAwareConcreteBranch::Step::internal_disk(new_concrete, new_disk) => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Internal{};
                old_concrete.internal_disk_refines(new_concrete, concrete_lbl, new_disk);
                self.lift_loaded_internal_stack_next(post, old_concrete, new_concrete);
            }
            CrashAwareConcreteBranch::Step::cache_disk_ops(
                new_concrete,
                new_cache,
                new_disk,
                cache_requests,
                cache_responses,
                disk_requests,
                disk_responses,
            ) => {
                let old_concrete = self.ephemeral->v;
                let concrete_lbl = ConcreteBranch::Label::Internal{};
                old_concrete.cache_disk_ops_refines(
                    new_concrete,
                    concrete_lbl,
                    new_cache,
                    new_disk,
                    cache_requests,
                    cache_responses,
                    disk_requests,
                    disk_responses,
                );
                self.lift_loaded_internal_stack_next(post, old_concrete, new_concrete);
            }
            CrashAwareConcreteBranch::Step::freeze_map_internal() => {
                self.freeze_map_internal_refines(post, lbl);
            }
            CrashAwareConcreteBranch::Step::freeze_persistent_internal() => {
                self.freeze_persistent_internal_refines(post, lbl);
            }
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    pub proof fn commit_start_refines(self, post: Self, lbl: CrashAwareConcreteBranch::Label)
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::commit_start(self, post, lbl),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::commit_start);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        assert(CrashAwareAllocationBranchStack::State::commit_start(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
        ));
        assert(CrashAwareAllocationBranchStack::State::next_by(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
            CrashAwareAllocationBranchStack::Step::commit_start(),
        ));
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    pub proof fn commit_complete_refines(self, post: Self, lbl: CrashAwareConcreteBranch::Label)
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::commit_complete(self, post, lbl),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::commit_complete);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        assert(CrashAwareAllocationBranchStack::State::commit_complete(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
        ));
        assert(CrashAwareAllocationBranchStack::State::next_by(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
            CrashAwareAllocationBranchStack::Step::commit_complete(),
        ));
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    pub proof fn crash_refines(self, post: Self, lbl: CrashAwareConcreteBranch::Label)
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::crash(self, post, lbl),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::crash);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        assert(CrashAwareAllocationBranchStack::State::crash(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
        ));
        assert(CrashAwareAllocationBranchStack::State::next_by(
            self.i(),
            post.i(),
            self.label_to_stack(lbl),
            CrashAwareAllocationBranchStack::Step::crash(),
        ));
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)));
    }

    pub proof fn next_refines(self, post: Self, lbl: CrashAwareConcreteBranch::Label)
        requires
            self.refinement_wf(),
            post.refinement_wf(),
            CrashAwareConcreteBranch::State::next(self, post, lbl),
        ensures
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_to_stack(lbl)),
    {
        reveal(CrashAwareConcreteBranch::State::next);
        reveal(CrashAwareConcreteBranch::State::next_by);

        let step = choose |step| CrashAwareConcreteBranch::State::next_by(self, post, lbl, step);
        match step {
            CrashAwareConcreteBranch::Step::load_ephemeral(new_concrete) => {
                self.load_ephemeral_refines(post, lbl, new_concrete);
            }
            CrashAwareConcreteBranch::Step::query(new_concrete, reads, query_receipts) => {
                self.query_refines(post, lbl, new_concrete, reads, query_receipts);
            }
            CrashAwareConcreteBranch::Step::append_to_active(new_concrete, reads, writes, receipt, new_cache) => {
                self.append_to_active_refines(post, lbl, new_concrete, reads, writes, receipt, new_cache);
            }
            CrashAwareConcreteBranch::Step::append_to_empty(new_concrete, writes, init_root, new_cache) => {
                self.append_to_empty_refines(post, lbl, new_concrete, writes, init_root, new_cache);
            }
            CrashAwareConcreteBranch::Step::commit_start() => {
                self.commit_start_refines(post, lbl);
            }
            CrashAwareConcreteBranch::Step::commit_complete() => {
                self.commit_complete_refines(post, lbl);
            }
            CrashAwareConcreteBranch::Step::crash() => {
                self.crash_refines(post, lbl);
            }
            _ => {
                self.internal_refines(post, lbl);
            }
        }
    }
}

}
