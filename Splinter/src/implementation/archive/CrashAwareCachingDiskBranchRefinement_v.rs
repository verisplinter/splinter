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
    CachingDiskBranch, CachingDiskBranchMetadata, CachingDiskBranchImage,
    branch_summary_reads_valid, completed_branch_summary_from_reads,
    empty_caching_disk_branch_image, empty_caching_disk_branch_image_wf,
    to_branch_nodes,
};
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
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
            branch_summary: self.branch_summary(),
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
    frozen: Option<CachingDiskBranchMetadata>,
    persistent: PersistentCachingDiskBranch,
    ephemeral: EphemeralCachingDiskBranch,
) -> Option<FrozenAllocationBranchStack> {
    if frozen is None {
        Option::None
    } else {
        let target = frozen.unwrap();
        let persistent_image = persistent_image_i(persistent, ephemeral);
        let persistent_meta = persistent.metadata();
        if target.sealed_roots == persistent_meta.sealed_roots
            && target.seq_end == persistent_meta.seq_end {
            Option::Some(persistent_image.frozen_i())
        } else if ephemeral is Known {
            Option::Some(CachingDiskBranchImage{
                persistent: ephemeral->v.disk.visible(),
                sealed_roots: target.sealed_roots,
                seq_end: target.seq_end,
            }.frozen_i())
        } else {
            Option::Some(empty_caching_disk_branch_image().frozen_i())
        }
    }
}

pub open spec fn persistent_image_i(
    persistent: PersistentCachingDiskBranch,
    ephemeral: EphemeralCachingDiskBranch,
) -> CachingDiskBranchImage {
    match persistent {
        PersistentCachingDiskBranch::Image{image} => image,
        PersistentCachingDiskBranch::Metadata{meta} => {
            if ephemeral is Known {
                ephemeral->v.visible_image_for_metadata(meta)
            } else {
                empty_caching_disk_branch_image()
            }
        },
    }
}

impl CachingDiskBranch::State {
    pub proof fn materialized_image_matches_visible_prefix(
        self,
        frozen: CachingDiskBranchMetadata,
    )
        requires
            self.inv(),
            CachingDiskBranch::State::next(
                self,
                self,
                CachingDiskBranch::Label::FreezePrepared{image: frozen},
            ),
        ensures
            ({
                let image = CachingDiskBranchImage::materialized_from_persistent(
                    self,
                    frozen,
                );
                let full_image = CachingDiskBranchImage{
                    persistent: self.disk.persistent,
                    sealed_roots: frozen.sealed_roots,
                    seq_end: frozen.seq_end,
                };
                &&& image.loadable()
                &&& image.stack_wf()
                &&& image.sealed_stack_i().wf(image.branch_summary())
                &&& image.branch_summary()
                    == self.visible_image_for_metadata(frozen).branch_summary()
                &&& image.branch_summary() == full_image.branch_summary()
                &&& summary_aus(image.branch_summary())
                    <= summary_aus(self.interpreted_branch_summary())
                &&& image.sealed_stack_i()
                    == self.visible_image_for_metadata(frozen).sealed_stack_i()
            }),
    {
        let full_image = CachingDiskBranchImage{
            persistent: self.disk.persistent,
            sealed_roots: frozen.sealed_roots,
            seq_end: frozen.seq_end,
        };
        let image = CachingDiskBranchImage::materialized_from_persistent(self, frozen);
        self.prepared_image_matches_visible_prefix(full_image);
        assert(full_image.loadable());
        assert(branch_summary_reads_valid(
            frozen.sealed_roots,
            to_branch_nodes(self.disk.persistent),
        ));
        assert(CachingDiskBranchImage::materialized_summary_addrs(
            self.disk.persistent,
            frozen,
        ) == addresses_in_aus(summary_aus(full_image.branch_summary()))) by {
            assert(completed_branch_summary_from_reads(
                frozen.sealed_roots,
                to_branch_nodes(self.disk.persistent),
            ) == full_image.branch_summary());
        }
        assert(image.persistent.restrict(addresses_in_aus(summary_aus(full_image.branch_summary())))
            == full_image.persistent.restrict(addresses_in_aus(summary_aus(full_image.branch_summary())))) by {
            assert_maps_equal!(
                image.persistent.restrict(addresses_in_aus(summary_aus(full_image.branch_summary()))),
                full_image.persistent.restrict(addresses_in_aus(summary_aus(full_image.branch_summary()))),
                addr => {}
            );
        }
        CachingDiskBranchImage::same_summary_aus_preserves_sealed_stack(full_image, image);
    }
}

impl CrashAwareCachingDiskBranch::State {
    pub open spec fn persistent_image_i(self) -> CachingDiskBranchImage {
        persistent_image_i(self.persistent, self.ephemeral)
    }

    pub open spec fn i(self) -> CrashAwareAllocationBranchStack::State {
        let persistent = self.persistent_image_i();
        CrashAwareAllocationBranchStack::State{
            persistent: persistent.sealed_stack_i(),
            persistent_branch_summary: persistent.branch_summary(),
            persistent_seq_end: self.persistent.metadata().seq_end,
            ephemeral: self.ephemeral.i(),
            frozen: frozen_image_i(self.frozen, self.persistent, self.ephemeral),
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
                        frozen_image_i(post.frozen, post.persistent, post.ephemeral).unwrap()
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

    pub open spec fn semantic_inv(self) -> bool {
        let persistent = self.persistent_image_i();
        let persistent_meta = self.persistent.metadata();
        &&& self.ephemeral is Known ==> self.ephemeral->v.refinement_inv()
        &&& persistent.sealed_stack_i().wf(persistent.branch_summary())
        &&& self.frozen is Some && self.ephemeral is Known ==> {
            let frozen = self.frozen.unwrap();
            ||| {
                &&& frozen.sealed_roots == persistent_meta.sealed_roots
                &&& frozen.seq_end == persistent_meta.seq_end
            }
            ||| {
                &&& self.ephemeral->v.metadata_loaded
                &&& frozen.sealed_roots.len() <= self.ephemeral->v.sealed_roots.len()
                &&& self.ephemeral->v.sealed_roots.subrange(
                    0,
                    frozen.sealed_roots.len() as int,
                ) == frozen.sealed_roots
            }
        }
    }

    pub open spec fn refinement_inv(self) -> bool {
        &&& self.inv()
        &&& self.semantic_inv()
    }

    pub proof fn semantic_inv_implies_i_inv(self)
        requires
            self.refinement_inv(),
        ensures
            self.i().inv(),
    {
        if self.ephemeral is Known {
            self.ephemeral->v.semantic_inv_implies_i_inv();
        }
        if self.frozen is Some {
            let frozen = self.frozen.unwrap();
            let persistent = self.persistent_image_i();
            let persistent_meta = self.persistent.metadata();
            if frozen.sealed_roots == persistent_meta.sealed_roots
                && frozen.seq_end == persistent_meta.seq_end {
                assert(persistent.sealed_stack_i().wf(persistent.branch_summary()));
                assert(self.i().frozen.unwrap() == persistent.frozen_i());
            } else if self.ephemeral is Known {
                self.ephemeral->v.visible_prefix_image_matches_stack(frozen);
                assert(self.i().frozen.unwrap()
                    == self.ephemeral->v.visible_image_for_metadata(frozen).frozen_i());
            }
        }
    }

    pub proof fn i_inv_implies_semantic_inv(self)
        requires
            self.inv(),
            self.i().inv(),
        ensures
            self.semantic_inv(),
    {
        if self.ephemeral is Known {
            self.ephemeral->v.i_inv_implies_semantic_inv();
            assert(self.ephemeral->v.refinement_inv());
        }
        if self.frozen is Some {
            let frozen = self.frozen.unwrap();
            let persistent = self.persistent_image_i();
            let persistent_meta = self.persistent.metadata();
            if frozen.sealed_roots == persistent_meta.sealed_roots
                && frozen.seq_end == persistent_meta.seq_end {
                assert(self.i().frozen.unwrap() == persistent.frozen_i());
            } else if self.ephemeral is Known {
                assert(self.i().frozen.unwrap()
                    == self.ephemeral->v.visible_image_for_metadata(frozen).frozen_i());
            }
        }
    }

    pub proof fn freeze_prepared_preserves_i(
        self,
        post: Self,
    )
        requires
            self.inv(),
            post.inv(),
        CrashAwareCachingDiskBranch::State::freeze_prepared(
            self,
            post,
            CrashAwareCachingDiskBranch::Label::FreezePrepared,
        ),
        ensures
            post.i() == self.i(),
    {
        assert(post.ephemeral == self.ephemeral);
        assert(post.persistent == self.persistent);
        assert(post.frozen == self.frozen);
        assert(post.prepared);
        assert(post.i().frozen == self.i().frozen);
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
        empty_caching_disk_branch_image_wf();
        let image = empty_caching_disk_branch_image();
        assert(self.persistent == PersistentCachingDiskBranch::Image{image});
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

    proof fn loaded_step_preserves_persistent_i(
        self,
        post: Self,
        old_branch: CachingDiskBranch::State,
        new_branch: CachingDiskBranch::State,
        branch_lbl: CachingDiskBranch::Label,
    )
        requires
            self.refinement_inv(),
            self.ephemeral == (EphemeralCachingDiskBranch::Known{ v: old_branch }),
            post.ephemeral == (EphemeralCachingDiskBranch::Known{ v: new_branch }),
            post.persistent == self.persistent,
            post.frozen == self.frozen,
            post.prepared == self.prepared,
            CachingDiskBranch::State::next(old_branch, new_branch, branch_lbl),
        ensures
            post.i().persistent == self.i().persistent,
            post.i().persistent_branch_summary == self.i().persistent_branch_summary,
            post.i().persistent_seq_end == self.i().persistent_seq_end,
    {
        let persistent = self.persistent_image_i();
        let persistent_meta = self.persistent.metadata();
        assert(self.persistent is Metadata);
        assert(post.persistent is Metadata);
        assert(persistent == old_branch.visible_image_for_metadata(persistent_meta));
        assert(persistent.sealed_roots == persistent_meta.sealed_roots);
        assert(persistent.seq_end == persistent_meta.seq_end);
        cdb_step_preserves_image_match(
            old_branch,
            new_branch,
            branch_lbl,
            persistent,
        );
        assert(post.persistent_image_i()
            == new_branch.visible_image_for_metadata(persistent_meta));
        assert(post.persistent_image_i().sealed_stack_i() == persistent.sealed_stack_i());
        assert(post.persistent_image_i().branch_summary() == persistent.branch_summary());
        assert(post.persistent_image_i().seq_end == persistent.seq_end);
    }

    proof fn loaded_step_preserves_frozen_i(
        self,
        post: Self,
        old_branch: CachingDiskBranch::State,
        new_branch: CachingDiskBranch::State,
        branch_lbl: CachingDiskBranch::Label,
    )
        requires
            self.refinement_inv(),
            self.ephemeral == (EphemeralCachingDiskBranch::Known{ v: old_branch }),
            post.ephemeral == (EphemeralCachingDiskBranch::Known{ v: new_branch }),
            post.persistent == self.persistent,
            post.frozen == self.frozen,
            post.prepared == self.prepared,
            CachingDiskBranch::State::next(old_branch, new_branch, branch_lbl),
        ensures
            post.i().persistent == self.i().persistent,
            post.i().persistent_branch_summary == self.i().persistent_branch_summary,
            post.i().persistent_seq_end == self.i().persistent_seq_end,
            post.i().frozen == self.i().frozen,
    {
        self.loaded_step_preserves_persistent_i(post, old_branch, new_branch, branch_lbl);
        CachingDiskBranch::State::inv_next(old_branch, new_branch, branch_lbl);
        if self.frozen is Some {
            let frozen = self.frozen.unwrap();
            let persistent = self.persistent_image_i();
            let persistent_meta = self.persistent.metadata();
            if frozen.sealed_roots == persistent_meta.sealed_roots
                && frozen.seq_end == persistent_meta.seq_end {
                assert(post.persistent_image_i().frozen_i() == persistent.frozen_i());
                assert(post.i().frozen.unwrap() == persistent.frozen_i());
                assert(self.i().frozen.unwrap() == persistent.frozen_i());
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
                assert(new_branch.visible_image_for_metadata(frozen).branch_summary()
                    == old_branch.visible_image_for_metadata(frozen).branch_summary());
                assert(new_branch.visible_image_for_metadata(frozen).frozen_i()
                    == old_branch.visible_image_for_metadata(frozen).frozen_i());
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
            self.refinement_inv(),
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
            self.refinement_inv(),
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
            self.refinement_inv(),
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
            AllocationBranchStack::Step::internal_seal(aux_ptr, loose_active_disk) => {
                assert(CrashAwareAllocationBranchStack::State::ephemeral_internal_seal(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    new_branch.i(),
                    aux_ptr,
                    loose_active_disk,
                ));
                assert(CrashAwareAllocationBranchStack::State::next_by(
                    self.i(),
                    post.i(),
                    CrashAwareAllocationBranchStack::Label::Internal,
                    CrashAwareAllocationBranchStack::Step::ephemeral_internal_seal(
                        new_branch.i(),
                        aux_ptr,
                        loose_active_disk,
                    ),
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
            self.refinement_inv(),
            CrashAwareCachingDiskBranch::State::next(self, post, lbl),
        ensures
            post.inv(),
            post.refinement_inv(),
            CrashAwareAllocationBranchStack::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        CrashAwareCachingDiskBranch::State::inv_next(self, post, lbl);
        self.semantic_inv_implies_i_inv();
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        reveal(CrashAwareAllocationBranchStack::State::next);
        reveal(CrashAwareAllocationBranchStack::State::next_by);

        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(self, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_ephemeral(new_ephemeral) => {
                match lbl {
                    CrashAwareCachingDiskBranch::Label::LoadEphemeral => {
                        let image = self.persistent->image;
                        let meta = image.metadata();
                        CachingDiskBranch::State::init_refines(new_ephemeral, image);
                        assert(post.persistent == PersistentCachingDiskBranch::Metadata{meta});
                        new_ephemeral.visible_prefix_image_matches_stack(meta);
                        assert(post.persistent_image_i()
                            == new_ephemeral.visible_image_for_metadata(meta));
                        assert(post.persistent_image_i().sealed_stack_i() == image.sealed_stack_i());
                        assert(post.persistent_image_i().branch_summary() == image.branch_summary());
                        assert(post.persistent_image_i().seq_end == image.seq_end);
                        assert(post.i().persistent == self.i().persistent);
                        assert(post.i().persistent_branch_summary == self.i().persistent_branch_summary);
                        assert(post.i().persistent_seq_end == self.i().persistent_seq_end);
                        assert(post.i().ephemeral == EphemeralAllocationBranchStack::Known{ v: new_ephemeral.i() });
                        assert(new_ephemeral.i() == load_stack(
                            self.i().persistent,
                            self.i().persistent_branch_summary,
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
                match lbl {
                    CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus} => {
                        let branch_lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
                        self.lift_loaded_internal_refines(post, self.ephemeral->v, new_ephemeral, branch_lbl);
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::query(msg) => {
                match lbl {
                    CrashAwareCachingDiskBranch::Label::Query{key, value} => {
                        self.lift_loaded_query_refines(post, self.ephemeral->v, key, value, msg);
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {
                match lbl {
                    CrashAwareCachingDiskBranch::Label::Append{keys, msgs} => {
                        self.lift_loaded_append_refines(post, self.ephemeral->v, new_ephemeral, keys, msgs);
                    },
                    _ => { assert(false); }
                }
            },
            CrashAwareCachingDiskBranch::Step::internal(new_ephemeral) => {
                self.lift_loaded_internal_refines(post, self.ephemeral->v, new_ephemeral, CachingDiskBranch::Label::Internal);
            },
            CrashAwareCachingDiskBranch::Step::internal_alloc(new_ephemeral) => {
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
                }
                match lbl {
                    CrashAwareCachingDiskBranch::Label::CommitStart{new_boundary_lsn, sealed_roots} => {
                        assert(post.frozen == Option::Some(CachingDiskBranchMetadata{
                            sealed_roots,
                            seq_end: new_boundary_lsn,
                        }));
                        assert(!post.prepared);
                        assert(self.ephemeral is Known);
                        assert(post.ephemeral == self.ephemeral);
                        let persistent = self.persistent_image_i();
                        let persistent_meta = self.persistent.metadata();
                        if new_boundary_lsn == persistent_meta.seq_end
                            && sealed_roots == persistent_meta.sealed_roots {
                            assert(post.i().frozen.unwrap() == persistent.frozen_i());
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
                            let frozen = CachingDiskBranchMetadata{
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
            CrashAwareCachingDiskBranch::Step::freeze_prepared() => {
                assert(CrashAwareCachingDiskBranch::State::freeze_prepared(self, post, lbl)) by {
                }
                match lbl {
                    CrashAwareCachingDiskBranch::Label::FreezePrepared => {
                        assert(post.ephemeral == self.ephemeral);
                        assert(post.persistent == self.persistent);
                        assert(post.frozen == self.frozen);
                        assert(post.prepared);
                        assert(post.i().frozen == self.i().frozen);
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
                }
                let frozen = self.frozen.unwrap();
                let prepared_image = CachingDiskBranchImage::materialized_from_persistent(
                    self.ephemeral->v,
                    frozen,
                );
                self.ephemeral->v.materialized_image_matches_visible_prefix(frozen);
                let persistent = self.persistent_image_i();
                let persistent_meta = self.persistent.metadata();
                if frozen.sealed_roots == persistent_meta.sealed_roots
                    && frozen.seq_end == persistent_meta.seq_end {
                    assert(self.i().frozen.unwrap() == persistent.frozen_i());
                    assert(self.ephemeral->v.visible_image_for_metadata(frozen).branch_summary()
                        == persistent.branch_summary());
                    assert(self.ephemeral->v.visible_image_for_metadata(frozen).sealed_stack_i()
                        == persistent.sealed_stack_i());
                    assert(prepared_image.frozen_i() == persistent.frozen_i());
                } else {
                    assert(self.i().frozen.unwrap()
                        == self.ephemeral->v.visible_image_for_metadata(frozen).frozen_i());
                    assert(prepared_image.frozen_i()
                        == self.ephemeral->v.visible_image_for_metadata(frozen).frozen_i());
                }
                assert(prepared_image.frozen_i() == self.i().frozen.unwrap());
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
                match lbl {
                    CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight} => {
                        let prepared_image = if keep_in_flight && self.ephemeral is Known {
                            CachingDiskBranchImage::materialized_from_persistent(
                                self.ephemeral->v,
                                self.frozen.unwrap(),
                            )
                        } else if self.ephemeral is Unknown {
                            self.persistent->image
                        } else {
                            CachingDiskBranchImage::materialized_from_persistent(
                                self.ephemeral->v,
                                self.persistent.metadata(),
                            )
                        };
                        if keep_in_flight {
                            self.prepared_materialized_image_matches_visible_prefix();
                            assert(prepared_image == self.prepared_materialized_image());
                            let frozen = self.frozen.unwrap();
                            let image_frozen = CachingDiskBranchMetadata{
                                sealed_roots: prepared_image.sealed_roots,
                                seq_end: prepared_image.seq_end,
                            };
                            assert(image_frozen == frozen);
                            let persistent = self.persistent_image_i();
                            let persistent_meta = self.persistent.metadata();
                            if frozen.sealed_roots == persistent_meta.sealed_roots
                                && frozen.seq_end == persistent_meta.seq_end {
                                assert(frozen_image_i(self.frozen, self.persistent, self.ephemeral).unwrap()
                                    == persistent.frozen_i());
                                assert(self.ephemeral->v.visible_image_for_metadata(frozen).branch_summary()
                                    == persistent.branch_summary());
                                assert(self.ephemeral->v.visible_image_for_metadata(frozen).sealed_stack_i()
                                    == persistent.sealed_stack_i());
                                assert(prepared_image.frozen_i() == persistent.frozen_i());
                            } else {
                                assert(prepared_image.sealed_stack_i()
                                    == self.ephemeral->v.visible_image_for_metadata(frozen).sealed_stack_i());
                                assert(frozen_image_i(self.frozen, self.persistent, self.ephemeral).unwrap()
                                    == self.ephemeral->v.visible_image_for_metadata(frozen).frozen_i());
                                assert(prepared_image.frozen_i()
                                    == frozen_image_i(self.frozen, self.persistent, self.ephemeral).unwrap());
                            }
                            assert(prepared_image.frozen_i()
                                == frozen_image_i(self.frozen, self.persistent, self.ephemeral).unwrap());
                            assert(post.i().persistent == prepared_image.sealed_stack_i());
                            assert(post.i().persistent_branch_summary == prepared_image.branch_summary());
                            assert(self.i().frozen.unwrap().sealed_stack == prepared_image.sealed_stack_i());
                            assert(self.i().frozen.unwrap().branch_summary == prepared_image.branch_summary());
                        } else {
                            assert(post.persistent == PersistentCachingDiskBranch::Image{image: prepared_image});
                            if self.ephemeral is Known {
                                let persistent_meta = self.persistent.metadata();
                                let branch_lbl = CachingDiskBranch::Label::FreezePrepared{
                                    image: persistent_meta,
                                };
                                assert(CachingDiskBranch::State::next(
                                    self.ephemeral->v,
                                    self.ephemeral->v,
                                    branch_lbl,
                                )) by {
                                    reveal(CachingDiskBranch::State::next);
                                    reveal(CachingDiskBranch::State::next_by);
                                    assert(CachingDiskBranch::State::freeze_prepared(
                                        self.ephemeral->v,
                                        self.ephemeral->v,
                                        branch_lbl,
                                    )) by {
                                    };
                                    assert(CachingDiskBranch::State::next_by(
                                        self.ephemeral->v,
                                        self.ephemeral->v,
                                        branch_lbl,
                                        CachingDiskBranch::Step::freeze_prepared(),
                                    ));
                                };
                                self.ephemeral->v.materialized_image_matches_visible_prefix(
                                    persistent_meta,
                                );
                                assert(prepared_image.sealed_stack_i()
                                    == self.persistent_image_i().sealed_stack_i());
                                assert(prepared_image.branch_summary()
                                    == self.persistent_image_i().branch_summary());
                            }
                            assert(post.i().persistent == self.i().persistent);
                            assert(post.i().persistent_branch_summary == self.i().persistent_branch_summary);
                        }
                    },
                    _ => { assert(false); }
                }
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
        self.semantic_inv_implies_i_inv();
        assert(self.i().inv());
        CrashAwareAllocationBranchStack::State::inv_next(self.i(), post.i(), self.label_i(post, lbl));
        post.i_inv_implies_semantic_inv();
        assert(post.refinement_inv());
    }

    pub proof fn next_refines_to_abstract_map(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskBranch::Label,
    )
        requires
            self.refinement_inv(),
            CrashAwareCachingDiskBranch::State::next(self, post, lbl),
        ensures
            AbstractCrashAwareMap::State::next(
                self.abstract_i(),
                post.abstract_i(),
                self.label_to_abstract_map(post, lbl),
            ),
    {
        self.next_refines(post, lbl);
        self.semantic_inv_implies_i_inv();
        assert(self.i().inv());
        CrashAwareAllocationBranchStack::State::inv_next(self.i(), post.i(), self.label_i(post, lbl));
        self.i().next_refines(post.i(), self.label_i(post, lbl));
    }
}

}
