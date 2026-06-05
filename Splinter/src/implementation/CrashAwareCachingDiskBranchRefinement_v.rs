// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich
// SPDX-License-Identifier: BSD-2-Clause
//
// Refinement from CrashAwareCachingDiskBranch to CrashAwareAllocationBranchStack.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;

use crate::implementation::CachingDiskBranchRefinement_v::*;
use crate::implementation::AllocationBranchStack_v::{AllocationBranchStack, normalize_value};
use crate::implementation::CachingDiskBranch_v::{
    CachingDiskBranch, CachingDiskBranchFrozenImage, CachingDiskBranchImage,
    empty_caching_disk_branch_image, empty_caching_disk_branch_image_wf,
};
use crate::implementation::CrashAwareAllocationBranchStackRefinement_v::*;
use crate::implementation::CrashAwareAllocationBranchStack_v::*;
use crate::implementation::CrashAwareCachingDiskBranch_v::*;
use crate::spec::AsyncDisk_t::AU;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;

verus!{

impl CachingDiskBranchImage {
    pub open spec fn frozen_i(self) -> FrozenAllocationBranchStack {
        FrozenAllocationBranchStack{
            sealed_stack: self.sealed_stack_i(),
            seq_end: self.seq_end,
        }
    }
}

impl EphemeralCachingDiskBranch {
    pub open spec fn i(self) -> EphemeralAllocationBranchStack {
        match self {
            EphemeralCachingDiskBranch::Unknown => EphemeralAllocationBranchStack::Unknown,
            EphemeralCachingDiskBranch::Known{v} => EphemeralAllocationBranchStack::Known{v: v.i()},
        }
    }
}

pub open spec fn frozen_image_i(
    frozen: Option<CachingDiskBranchFrozenImage>,
    prepared: Option<CachingDiskBranchImage>,
    persistent: CachingDiskBranchImage,
    ephemeral: EphemeralCachingDiskBranch,
) -> Option<FrozenAllocationBranchStack> {
    if frozen is None {
        Option::None
    } else if prepared is Some {
        Option::Some(prepared.unwrap().frozen_i())
    } else {
        let target = frozen.unwrap();
        if ephemeral is Known {
            Option::Some(CachingDiskBranchImage{
                persistent: ephemeral->v.disk.visible(),
                sealed_roots: target.sealed_roots,
                seq_end: target.seq_end,
            }.frozen_i())
        } else if target.sealed_roots == persistent.sealed_roots
            && target.seq_end == persistent.seq_end {
            Option::Some(persistent.frozen_i())
        } else {
            Option::Some(empty_caching_disk_branch_image().frozen_i())
        }
    }
}

impl CrashAwareCachingDiskBranch::State {
    pub open spec fn i(self) -> CrashAwareAllocationBranchStack::State {
        CrashAwareAllocationBranchStack::State{
            persistent: self.persistent.sealed_stack_i(),
            persistent_seq_end: self.persistent.seq_end,
            ephemeral: self.ephemeral.i(),
            frozen: frozen_image_i(self.frozen, self.prepared, self.persistent, self.ephemeral),
        }
    }

    pub open spec fn label_i(self, post: Self, lbl: CrashAwareCachingDiskBranch::Label)
        -> CrashAwareAllocationBranchStack::Label
    {
        match lbl {
            CrashAwareCachingDiskBranch::Label::LoadEphemeral =>
                CrashAwareAllocationBranchStack::Label::LoadEphemeral{free_aus: Set::<AU>::empty()},
            CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus} =>
                CrashAwareAllocationBranchStack::Label::Internal,
            CrashAwareCachingDiskBranch::Label::Query{key, value} =>
                CrashAwareAllocationBranchStack::Label::Query{key, value},
            CrashAwareCachingDiskBranch::Label::Append{keys, msgs} =>
                CrashAwareAllocationBranchStack::Label::Append{keys, msgs},
            CrashAwareCachingDiskBranch::Label::Internal =>
                CrashAwareAllocationBranchStack::Label::Internal,
            CrashAwareCachingDiskBranch::Label::InternalAlloc{allocs, deallocs} =>
                CrashAwareAllocationBranchStack::Label::Internal,
            CrashAwareCachingDiskBranch::Label::CommitStart{new_boundary_lsn, sealed_roots} =>
                CrashAwareAllocationBranchStack::Label::CommitStart{
                    new_boundary_lsn,
                    frozen_stack: if post.frozen is Some {
                        frozen_image_i(post.frozen, post.prepared, post.persistent, post.ephemeral).unwrap()
                    } else {
                        empty_caching_disk_branch_image().frozen_i()
                    },
                },
            CrashAwareCachingDiskBranch::Label::FreezePrepared =>
                CrashAwareAllocationBranchStack::Label::Internal,
            CrashAwareCachingDiskBranch::Label::CommitComplete =>
                CrashAwareAllocationBranchStack::Label::CommitComplete,
            CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight} =>
                CrashAwareAllocationBranchStack::Label::Crash{keep_in_flight},
        }
    }

    pub proof fn interpreted_inv(self)
        requires
            self.inv(),
        ensures
            self.i().inv(),
    {
        if self.ephemeral is Known {
            self.ephemeral->v.interpreted_inv();
        }
        if self.frozen is Some && self.prepared is None {
            let frozen = self.frozen.unwrap();
            if frozen.sealed_roots == self.persistent.sealed_roots
                && frozen.seq_end == self.persistent.seq_end {
                assert(self.persistent.sealed_stack_i().wf());
            } else if self.ephemeral is Known {
                self.ephemeral->v.visible_prefix_image_matches_stack(frozen);
            }
        }
    }

    pub proof fn freeze_prepared_preserves_i(
        self,
        post: Self,
        prepared_image: CachingDiskBranchImage,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskBranch::State::freeze_prepared(
                self,
                post,
                CrashAwareCachingDiskBranch::Label::FreezePrepared,
                prepared_image,
            ),
        ensures
            post.i() == self.i(),
    {
        reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
        assert(post.ephemeral == self.ephemeral);
        assert(post.persistent == self.persistent);
        assert(post.frozen == self.frozen);
        assert(post.prepared == Option::Some(prepared_image));
        self.ephemeral->v.prepared_image_matches_visible_prefix(prepared_image);
        let frozen = self.frozen.unwrap();
        if frozen.sealed_roots == self.persistent.sealed_roots
            && frozen.seq_end == self.persistent.seq_end {
            assert(self.ephemeral->v.visible_image_for_metadata(frozen).sealed_stack_i()
                == self.persistent.sealed_stack_i());
            assert(prepared_image.sealed_stack_i() == self.persistent.sealed_stack_i());
            assert(prepared_image.seq_end == self.persistent.seq_end);
            assert(post.i().frozen == self.i().frozen);
        } else {
            assert(prepared_image.sealed_stack_i()
                == self.ephemeral->v.visible_image_for_metadata(frozen).sealed_stack_i());
            assert(prepared_image.seq_end == frozen.seq_end);
            assert(post.i().frozen == self.i().frozen);
        }
    }

    pub open spec fn abstract_i(self) -> AbstractCrashAwareMap::State {
        self.i().abstract_i()
    }

    pub open spec fn label_to_abstract_map(self, post: Self, lbl: CrashAwareCachingDiskBranch::Label)
        -> AbstractCrashAwareMap::Label
    {
        self.i().label_to_abstract_map(self.label_i(post, lbl))
    }

    pub proof fn init_refines(self)
        requires
            CrashAwareCachingDiskBranch::State::initialize(self),
        ensures
            CrashAwareAllocationBranchStack::State::initialize(self.i()),
    {
        reveal(CrashAwareCachingDiskBranch::State::initialize);
        reveal(CrashAwareAllocationBranchStack::State::initialize);
        empty_caching_disk_branch_image_wf();
        let image = empty_caching_disk_branch_image();
        assert(self.persistent == image);
        assert(image.live_persistent() =~= Map::empty()) by {
            assert_maps_equal!(image.live_persistent(), Map::empty(), addr => {
                if image.live_persistent().contains_key(addr) {
                    assert(false);
                }
            });
        };
        assert(image.sealed_stack_i().sealed_disk.entries =~= Map::empty()) by {
            assert_maps_equal!(image.sealed_stack_i().sealed_disk.entries, Map::empty(), addr => {
                if image.sealed_stack_i().sealed_disk.entries.contains_key(addr) {
                    assert(image.live_persistent().contains_key(addr));
                    assert(false);
                }
            });
        };
        assert(image.sealed_stack_i() == empty_sealed_stack());
        assert(CrashAwareAllocationBranchStack::State::initialize(self.i()));
    }

    pub proof fn init_refines_to_abstract_map(self)
        requires
            CrashAwareCachingDiskBranch::State::initialize(self),
        ensures
            AbstractCrashAwareMap::State::initialize(self.abstract_i()),
    {
        self.init_refines();
        self.i().init_refines();
    }

    proof fn loaded_step_preserves_frozen_i(
        self,
        post: Self,
        old_branch: CachingDiskBranch::State,
        new_branch: CachingDiskBranch::State,
        branch_lbl: CachingDiskBranch::Label,
    )
        requires
            self.inv(),
            self.ephemeral == (EphemeralCachingDiskBranch::Known{ v: old_branch }),
            post.ephemeral == (EphemeralCachingDiskBranch::Known{ v: new_branch }),
            post.persistent == self.persistent,
            post.frozen == self.frozen,
            post.prepared == self.prepared,
            CachingDiskBranch::State::next(old_branch, new_branch, branch_lbl),
        ensures
            post.i().frozen == self.i().frozen,
    {
        CachingDiskBranch::State::inv_next(old_branch, new_branch, branch_lbl);
        if self.frozen is None {
        } else if self.prepared is Some {
        } else {
            let frozen = self.frozen.unwrap();
            if frozen.sealed_roots == self.persistent.sealed_roots
                && frozen.seq_end == self.persistent.seq_end {
                cdb_step_preserves_image_match(
                    old_branch,
                    new_branch,
                    branch_lbl,
                    self.persistent,
                );
                assert(old_branch.visible_image_for_metadata(frozen).sealed_stack_i()
                    == self.persistent.sealed_stack_i());
                assert(new_branch.visible_image_for_metadata(frozen).sealed_stack_i()
                    == self.persistent.sealed_stack_i());
                assert(post.i().frozen == self.i().frozen);
            } else {
                old_branch.next_preserves_visible_prefix_image(
                    new_branch,
                    branch_lbl,
                    frozen,
                );
                CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                    old_branch,
                    new_branch,
                    branch_lbl,
                    frozen.sealed_roots,
                );
                old_branch.visible_prefix_image_matches_stack(frozen);
                new_branch.visible_prefix_image_matches_stack(frozen);
                assert(post.i().frozen == self.i().frozen);
            }
        }
    }

    proof fn lift_loaded_query_refines(
        self,
        post: Self,
        old_branch: CachingDiskBranch::State,
        key: crate::spec::KeyType_t::Key,
        value: crate::spec::Messages_t::Value,
        msg: crate::spec::Messages_t::Message,
    )
        requires
            self.inv(),
            self.ephemeral == (EphemeralCachingDiskBranch::Known{ v: old_branch }),
            post.ephemeral == (EphemeralCachingDiskBranch::Known{ v: old_branch }),
            post.persistent == self.persistent,
            post.frozen == self.frozen,
            post.prepared == self.prepared,
            CachingDiskBranch::State::next(
                old_branch,
                old_branch,
                CachingDiskBranch::Label::QueryLabel{key, msg},
            ),
            normalize_value(msg) == value,
        ensures
            CrashAwareAllocationBranchStack::State::next(
                self.i(),
                post.i(),
                CrashAwareAllocationBranchStack::Label::Query{key, value},
            ),
    {
        old_branch.next_refines(old_branch, CachingDiskBranch::Label::QueryLabel{key, msg});
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        let stack_lbl = AllocationBranchStack::Label::QueryLabel{key, msg};
        let stack_step = choose |step| AllocationBranchStack::State::next_by(
            old_branch.i(),
            old_branch.i(),
            stack_lbl,
            step,
        );
        match stack_step {
            AllocationBranchStack::Step::query_step() => {
                assert(CrashAwareAllocationBranchStack::State::query(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Query{key, value},
                    old_branch.i(),
                    msg,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Query{key, value},
                    CrashAwareAllocationBranchStack::Step::query(old_branch.i(), msg),
                ));
            },
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(
            self.i(),
            post.i(),
            CrashAwareAllocationBranchStack::Label::Query{key, value},
        ));
    }

    proof fn lift_loaded_append_refines(
        self,
        post: Self,
        old_branch: CachingDiskBranch::State,
        new_branch: CachingDiskBranch::State,
        keys: Seq<crate::spec::KeyType_t::Key>,
        msgs: Seq<crate::spec::Messages_t::Message>,
    )
        requires
            self.inv(),
            self.ephemeral == (EphemeralCachingDiskBranch::Known{ v: old_branch }),
            post.ephemeral == (EphemeralCachingDiskBranch::Known{ v: new_branch }),
            post.persistent == self.persistent,
            post.frozen == self.frozen,
            post.prepared == self.prepared,
            CachingDiskBranch::State::next(
                old_branch,
                new_branch,
                CachingDiskBranch::Label::AppendLabel{keys, msgs},
            ),
        ensures
            CrashAwareAllocationBranchStack::State::next(
                self.i(),
                post.i(),
                CrashAwareAllocationBranchStack::Label::Append{keys, msgs},
            ),
    {
        self.loaded_step_preserves_frozen_i(
            post,
            old_branch,
            new_branch,
            CachingDiskBranch::Label::AppendLabel{keys, msgs},
        );
        old_branch.next_refines(new_branch, CachingDiskBranch::Label::AppendLabel{keys, msgs});
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        let stack_lbl = AllocationBranchStack::Label::AppendLabel{keys, msgs};
        let stack_step = choose |step| AllocationBranchStack::State::next_by(
            old_branch.i(),
            new_branch.i(),
            stack_lbl,
            step,
        );
        match stack_step {
            AllocationBranchStack::Step::append_to_active(path) => {
                assert(CrashAwareAllocationBranchStack::State::append_to_active(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Append{keys, msgs},
                    new_branch.i(),
                    path,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Append{keys, msgs},
                    CrashAwareAllocationBranchStack::Step::append_to_active(new_branch.i(), path),
                ));
            },
            AllocationBranchStack::Step::append_to_empty(init_root) => {
                assert(CrashAwareAllocationBranchStack::State::append_to_empty(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Append{keys, msgs},
                    new_branch.i(),
                    init_root,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Append{keys, msgs},
                    CrashAwareAllocationBranchStack::Step::append_to_empty(new_branch.i(), init_root),
                ));
            },
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(
            self.i(),
            post.i(),
            CrashAwareAllocationBranchStack::Label::Append{keys, msgs},
        ));
    }

    proof fn lift_loaded_internal_refines(
        self,
        post: Self,
        old_branch: CachingDiskBranch::State,
        new_branch: CachingDiskBranch::State,
        branch_lbl: CachingDiskBranch::Label,
    )
        requires
            self.inv(),
            self.ephemeral == (EphemeralCachingDiskBranch::Known{ v: old_branch }),
            post.ephemeral == (EphemeralCachingDiskBranch::Known{ v: new_branch }),
            post.persistent == self.persistent,
            post.frozen == self.frozen,
            post.prepared == self.prepared,
            branch_lbl.i() == AllocationBranchStack::Label::InternalLabel,
            CachingDiskBranch::State::next(old_branch, new_branch, branch_lbl),
        ensures
            CrashAwareAllocationBranchStack::State::next(
                self.i(),
                post.i(),
                CrashAwareAllocationBranchStack::Label::Internal,
            ),
    {
        self.loaded_step_preserves_frozen_i(post, old_branch, new_branch, branch_lbl);
        old_branch.next_refines(new_branch, branch_lbl);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);
        reveal(AllocationBranchStack::State::next);
        reveal(AllocationBranchStack::State::next_by);
        let stack_step = choose |step| AllocationBranchStack::State::next_by(
            old_branch.i(),
            new_branch.i(),
            AllocationBranchStack::Label::InternalLabel,
            step,
        );
        match stack_step {
            AllocationBranchStack::Step::internal_noop() => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_noop(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_branch.i(),
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_noop(new_branch.i()),
                ));
            },
            AllocationBranchStack::Step::internal_grow(new_root_addr) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_grow(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_branch.i(),
                    new_root_addr,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_grow(new_branch.i(), new_root_addr),
                ));
            },
            AllocationBranchStack::Step::internal_split(new_child_addr, path, split_arg) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_split(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_branch.i(),
                    new_child_addr,
                    path,
                    split_arg,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_split(
                        new_branch.i(),
                        new_child_addr,
                        path,
                        split_arg,
                    ),
                ));
            },
            AllocationBranchStack::Step::internal_seal(aux_ptr) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_seal(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_branch.i(),
                    aux_ptr,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_seal(new_branch.i(), aux_ptr),
                ));
            },
            AllocationBranchStack::Step::internal_fill_au(aus) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_fill_au(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_branch.i(),
                    aus,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_fill_au(new_branch.i(), aus),
                ));
            },
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(
            self.i(),
            post.i(),
            CrashAwareAllocationBranchStack::Label::Internal,
        ));
    }

    pub proof fn next_refines(self, post: Self, lbl: CrashAwareCachingDiskBranch::Label)
        requires
            self.inv(),
            CrashAwareCachingDiskBranch::State::next(self, post, lbl),
        ensures
            post.inv(),
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        CrashAwareCachingDiskBranch::State::inv_next(self, post, lbl);
        self.interpreted_inv();
        post.interpreted_inv();
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);

        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(self, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_ephemeral(new_ephemeral) => {
                reveal(CrashAwareCachingDiskBranch::State::load_ephemeral);
                match lbl {
                    CrashAwareCachingDiskBranch::Label::LoadEphemeral => {
                        CachingDiskBranch::State::init_refines(new_ephemeral, self.persistent);
                        reveal(CrashAwareAllocationBranchStack::State::load_ephemeral);
                        reveal(AllocationBranchStack::State::initialize);
                        assert(post.i().ephemeral == EphemeralAllocationBranchStack::Known{ v: new_ephemeral.i() });
                        assert(new_ephemeral.i() == load_stack(
                            self.i().persistent,
                            self.i().persistent_seq_end,
                            Set::<AU>::empty(),
                        ));
                        assert(CrashAwareAllocationBranchStack::State::load_ephemeral(
                            self.i(),
                            post.i(),
                            self.label_i(post, lbl),
                        ));
                        assert(CrashAwareAllocationBranchStack::State::next_by(
                            self.i(),
                            post.i(),
                            self.label_i(post, lbl),
                            CrashAwareAllocationBranchStack::Step::load_ephemeral(),
                        ));
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                reveal(CrashAwareCachingDiskBranch::State::load_metadata);
                match lbl {
                    CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus} => {
                        let branch_lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
                        self.lift_loaded_internal_refines(post, self.ephemeral->v, new_ephemeral, branch_lbl);
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::query(msg) => {
                reveal(CrashAwareCachingDiskBranch::State::query);
                match lbl {
                    CrashAwareCachingDiskBranch::Label::Query{key, value} => {
                        self.lift_loaded_query_refines(post, self.ephemeral->v, key, value, msg);
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {
                reveal(CrashAwareCachingDiskBranch::State::append);
                match lbl {
                    CrashAwareCachingDiskBranch::Label::Append{keys, msgs} => {
                        self.lift_loaded_append_refines(post, self.ephemeral->v, new_ephemeral, keys, msgs);
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::internal(new_ephemeral) => {
                reveal(CrashAwareCachingDiskBranch::State::internal);
                self.lift_loaded_internal_refines(post, self.ephemeral->v, new_ephemeral, CachingDiskBranch::Label::Internal);
            },
            CrashAwareCachingDiskBranch::Step::internal_alloc(new_ephemeral) => {
                reveal(CrashAwareCachingDiskBranch::State::internal_alloc);
                match lbl {
                    CrashAwareCachingDiskBranch::Label::InternalAlloc{allocs, deallocs} => {
                        let branch_lbl = CachingDiskBranch::Label::InternalAlloc{allocs, deallocs};
                        self.lift_loaded_internal_refines(post, self.ephemeral->v, new_ephemeral, branch_lbl);
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::commit_start() => {
                assert(CrashAwareCachingDiskBranch::State::commit_start(self, post, lbl)) by {
                    reveal(CrashAwareCachingDiskBranch::State::commit_start);
                }
                match lbl {
                    CrashAwareCachingDiskBranch::Label::CommitStart{new_boundary_lsn, sealed_roots} => {
                        assert(post.frozen == Option::Some(CachingDiskBranchFrozenImage{
                            sealed_roots,
                            seq_end: new_boundary_lsn,
                        }));
                        assert(post.prepared is None);
                        assert(self.ephemeral is Known);
                        assert(post.ephemeral == self.ephemeral);
                        if new_boundary_lsn == self.persistent.seq_end
                            && sealed_roots == self.persistent.sealed_roots {
                            assert(post.i().frozen.unwrap() == self.persistent.frozen_i());
                            assert(CrashAwareAllocationBranchStack::State::commit_start_persistent(
                                self.i(),
                                post.i(),
                                self.label_i(post, lbl),
                            ));
                            assert(CrashAwareAllocationBranchStack::State::next_by(
                                self.i(),
                                post.i(),
                                self.label_i(post, lbl),
                                CrashAwareAllocationBranchStack::Step::commit_start_persistent(),
                            ));
                        } else {
                            let frozen = CachingDiskBranchFrozenImage{
                                sealed_roots,
                                seq_end: new_boundary_lsn,
                            };
                            let branch_lbl = CachingDiskBranch::Label::FreezeAsLabel{image: frozen};
                            reveal(CachingDiskBranch::State::next);
                            reveal(CachingDiskBranch::State::next_by);
                            let branch_step = choose |step: CachingDiskBranch::Step|
                                CachingDiskBranch::State::next_by(
                                    self.ephemeral->v,
                                    self.ephemeral->v,
                                    branch_lbl,
                                    step,
                                );
                            match branch_step {
                                CachingDiskBranch::Step::freeze_as() => {
                                    reveal(CachingDiskBranch::State::freeze_as);
                                },
                                _ => { assert(false); },
                            }
                            self.ephemeral->v.visible_prefix_image_matches_stack(frozen);
                            assert(post.i().frozen.unwrap().sealed_stack == self.ephemeral->v.sealed_stack_i());
                            assert(post.i().frozen.unwrap().seq_end == new_boundary_lsn);
                            assert(self.ephemeral->v.i().seq_end == self.ephemeral->v.seq_end);
                            assert(CrashAwareAllocationBranchStack::State::commit_start_ephemeral(
                                self.i(),
                                post.i(),
                                self.label_i(post, lbl),
                            ));
                            assert(CrashAwareAllocationBranchStack::State::next_by(
                                self.i(),
                                post.i(),
                                self.label_i(post, lbl),
                                CrashAwareAllocationBranchStack::Step::commit_start_ephemeral(),
                            ));
                        }
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::freeze_prepared(prepared_image) => {
                assert(CrashAwareCachingDiskBranch::State::freeze_prepared(self, post, lbl, prepared_image)) by {
                    reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
                }
                match lbl {
                    CrashAwareCachingDiskBranch::Label::FreezePrepared => {
                        let branch_lbl = CachingDiskBranch::Label::FreezePrepared{
                            image: prepared_image,
                        };
                        assert(post.ephemeral == self.ephemeral);
                        assert(post.persistent == self.persistent);
                        assert(post.frozen == self.frozen);
                        assert(post.prepared == Option::Some(prepared_image));
                        self.ephemeral->v.prepared_image_matches_visible_prefix(prepared_image);
                        let frozen = self.frozen.unwrap();
                        if frozen.sealed_roots == self.persistent.sealed_roots
                            && frozen.seq_end == self.persistent.seq_end {
                            assert(self.ephemeral->v.visible_image_for_metadata(frozen).sealed_stack_i()
                                == self.persistent.sealed_stack_i());
                            assert(prepared_image.sealed_stack_i() == self.persistent.sealed_stack_i());
                            assert(prepared_image.seq_end == self.persistent.seq_end);
                            assert(post.i().frozen == self.i().frozen);
                        } else {
                            assert(prepared_image.sealed_stack_i()
                                == self.ephemeral->v.visible_image_for_metadata(frozen).sealed_stack_i());
                            assert(prepared_image.seq_end == frozen.seq_end);
                            assert(post.i().frozen == self.i().frozen);
                        }
                        assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_noop(
                            self.i(),
                            post.i(),
                            self.label_i(post, lbl),
                            self.ephemeral->v.i(),
                        ));
                        assert(CrashAwareAllocationBranchStack::State::next_by(
                            self.i(),
                            post.i(),
                            self.label_i(post, lbl),
                            CrashAwareAllocationBranchStack::Step::ephemeral_internal_noop(
                                self.ephemeral->v.i(),
                            ),
                        ));
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::commit_complete() => {
                assert(CrashAwareCachingDiskBranch::State::commit_complete(self, post, lbl)) by {
                    reveal(CrashAwareCachingDiskBranch::State::commit_complete);
                }
                assert(post.i().ephemeral == self.i().ephemeral);
                assert(CrashAwareAllocationBranchStack::State::commit_complete(
                    self.i(),
                    post.i(),
                    self.label_i(post, lbl),
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_i(post, lbl),
                    CrashAwareAllocationBranchStack::Step::commit_complete(),
                ));
            },
            CrashAwareCachingDiskBranch::Step::crash() => {
                reveal(CrashAwareCachingDiskBranch::State::crash);
                assert(CrashAwareAllocationBranchStack::State::crash(
                    self.i(),
                    post.i(),
                    self.label_i(post, lbl),
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    self.label_i(post, lbl),
                    CrashAwareAllocationBranchStack::Step::crash(),
                ));
            },
            _ => { assert(false); }
        }
        assert(CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_i(post, lbl)));
    }

    pub proof fn next_refines_to_abstract_map(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskBranch::Label,
    )
        requires
            self.inv(),
            CrashAwareCachingDiskBranch::State::next(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(
                self.abstract_i(),
                post.abstract_i(),
                self.label_to_abstract_map(post, lbl),
            ),
    {
        self.next_refines(post, lbl);
        self.interpreted_inv();
        post.interpreted_inv();
        CrashAwareAllocationBranchStack::State::inv_next(self.i(), post.i(), self.label_i(post, lbl));
        self.i().next_refines(post.i(), self.label_i(post, lbl));
    }
}

}
