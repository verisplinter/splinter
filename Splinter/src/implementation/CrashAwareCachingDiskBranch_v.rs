// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Crash-aware wrapper for CachingDiskBranch.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;
use vstd::assert_maps_equal;
use vstd::assert_seqs_equal;

use verus_state_machines_macros::state_machine;

use crate::disk::GenericDisk_v::{Address, AU};
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::AllocationBranch_v::Summary;
use crate::implementation::AllocationBranchStack_v::{new_branch_inv, normalize_value};
use crate::implementation::CachingDiskBranch_v::*;
use crate::implementation::CachingDisk_v::{addresses_in_aus, CachingDisk};
use crate::implementation::CrashAwareAllocationBranchStack_v::{
    EphemeralAllocationBranchStack, FrozenAllocationBranchStack,
    CrashAwareAllocationBranchStack,
};

verus!{

pub enum EphemeralCachingDiskBranch {
    Unknown,
    Known{ v: CachingDiskBranch::State },
}

pub enum PersistentCachingDiskBranch {
    Metadata{ meta: CachingDiskBranchMetadata },
    Image{ image: CachingDiskBranchImage },
}

impl CachingDiskBranchImage {
    pub open spec fn metadata(self) -> CachingDiskBranchMetadata {
        CachingDiskBranchMetadata{
            sealed_roots: self.sealed_roots,
            seq_end: self.seq_end,
        }
    }

    pub open spec fn materialized_summary_addrs(
        persistent: Map<Address, crate::spec::AsyncDisk_t::RawPage>,
        frozen: CachingDiskBranchMetadata,
    ) -> Set<Address> {
        let nodes = to_branch_nodes(persistent);
        let summary = if branch_summary_reads_valid(frozen.sealed_roots, nodes) {
            completed_branch_summary_from_reads(frozen.sealed_roots, nodes)
        } else {
            Map::<AU, Summary>::empty()
        };
        addresses_in_aus(summary_aus(summary))
    }

    pub open spec fn materialized_from_persistent(
        state: CachingDiskBranch::State,
        frozen: CachingDiskBranchMetadata,
    ) -> Self {
        CachingDiskBranchImage{
            persistent: state.disk.persistent.restrict(
                Self::materialized_summary_addrs(state.disk.persistent, frozen),
            ),
            sealed_roots: frozen.sealed_roots,
            seq_end: frozen.seq_end,
        }
    }
}

impl PersistentCachingDiskBranch {
    pub open spec fn metadata(self) -> CachingDiskBranchMetadata {
        match self {
            PersistentCachingDiskBranch::Metadata{meta} => meta,
            PersistentCachingDiskBranch::Image{image} => image.metadata(),
        }
    }

    pub open spec fn image(self) -> CachingDiskBranchImage
        recommends
            self is Image,
    {
        self->image
    }
}

impl CrashAwareCachingDiskBranch::State {
    pub open spec fn prepared_materialized_image(self) -> CachingDiskBranchImage {
        if self.ephemeral is Known && self.frozen is Some {
            CachingDiskBranchImage::materialized_from_persistent(
                self.ephemeral->v,
                self.frozen.unwrap(),
            )
        } else {
            empty_caching_disk_branch_image()
        }
    }
}

pub proof fn cdb_step_preserves_image_match(
    pre: CachingDiskBranch::State,
    post: CachingDiskBranch::State,
    lbl: CachingDiskBranch::Label,
    image: CachingDiskBranchImage,
)
    requires
        pre.inv(),
        image.sealed_roots.len() <= pre.sealed_roots.len(),
        pre.sealed_roots.subrange(0, image.sealed_roots.len() as int) == image.sealed_roots,
        pre.visible_image_for_metadata(CachingDiskBranchMetadata{
            sealed_roots: image.sealed_roots,
            seq_end: image.seq_end,
        }).sealed_stack_i() == image.sealed_stack_i(),
        pre.visible_image_for_metadata(CachingDiskBranchMetadata{
            sealed_roots: image.sealed_roots,
            seq_end: image.seq_end,
        }).branch_summary() == image.branch_summary(),
        CachingDiskBranch::State::next(pre, post, lbl),
    ensures
        image.sealed_roots.len() <= post.sealed_roots.len(),
        post.sealed_roots.subrange(0, image.sealed_roots.len() as int) == image.sealed_roots,
        post.visible_image_for_metadata(CachingDiskBranchMetadata{
            sealed_roots: image.sealed_roots,
            seq_end: image.seq_end,
        }).sealed_stack_i() == image.sealed_stack_i(),
        post.visible_image_for_metadata(CachingDiskBranchMetadata{
            sealed_roots: image.sealed_roots,
            seq_end: image.seq_end,
        }).branch_summary() == image.branch_summary(),
{
    let frozen = CachingDiskBranchMetadata{
        sealed_roots: image.sealed_roots,
        seq_end: image.seq_end,
    };
    CachingDiskBranch::State::inv_next(pre, post, lbl);
    if pre.metadata_loaded {
        CachingDiskBranch::State::next_preserves_loaded_root_prefix(
            pre,
            post,
            lbl,
            image.sealed_roots,
        );
        pre.next_preserves_visible_prefix_image(post, lbl, frozen);
    } else {
        reveal(CachingDiskBranch::State::next);
        reveal(CachingDiskBranch::State::next_by);
        let step = choose |step: CachingDiskBranch::Step|
            CachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CachingDiskBranch::Step::disk_internal(new_disk) => {
                reveal(CachingDiskBranch::State::disk_internal);
                CachingDisk::State::internal_visible_unchanged(pre.disk, post.disk);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.visible_image_for_metadata(frozen)
                    == pre.visible_image_for_metadata(frozen));
            },
            CachingDiskBranch::Step::load_metadata(reads) => {
                reveal(CachingDiskBranch::State::load_metadata);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.disk == pre.disk);
                assert(post.visible_image_for_metadata(frozen)
                    == pre.visible_image_for_metadata(frozen));
            },
            CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
                reveal(CachingDiskBranch::State::internal_fill_au);
                assert(post.sealed_roots == pre.sealed_roots);
                assert(post.visible_image_for_metadata(frozen)
                    == pre.visible_image_for_metadata(frozen));
            },
            CachingDiskBranch::Step::internal_noop() => {
                reveal(CachingDiskBranch::State::internal_noop);
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

pub proof fn cdb_step_preserves_root_prefix(
    pre: CachingDiskBranch::State,
    post: CachingDiskBranch::State,
    lbl: CachingDiskBranch::Label,
    roots: Seq<Address>,
)
    requires
        pre.inv(),
        roots.len() <= pre.sealed_roots.len(),
        pre.sealed_roots.subrange(0, roots.len() as int) == roots,
        CachingDiskBranch::State::next(pre, post, lbl),
    ensures
        roots.len() <= post.sealed_roots.len(),
        post.sealed_roots.subrange(0, roots.len() as int) == roots,
{
    CachingDiskBranch::State::inv_next(pre, post, lbl);
    reveal(CachingDiskBranch::State::next);
    reveal(CachingDiskBranch::State::next_by);
    let step = choose |step: CachingDiskBranch::Step|
        CachingDiskBranch::State::next_by(pre, post, lbl, step);
    match step {
        CachingDiskBranch::Step::load_metadata(reads) => {
            reveal(CachingDiskBranch::State::load_metadata);
            assert(post.sealed_roots == pre.sealed_roots);
        },
        CachingDiskBranch::Step::internal_seal(written_disk, aux_ptr, reads, writes) => {
            reveal(CachingDiskBranch::State::internal_seal);
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
            };
        },
        CachingDiskBranch::Step::append(new_disk, new_active_branch, receipt, init_root, reads, writes) => {
            reveal(CachingDiskBranch::State::append);
            assert(post.sealed_roots == pre.sealed_roots);
        },
        CachingDiskBranch::Step::internal_noop() => {
            reveal(CachingDiskBranch::State::internal_noop);
            assert(post == pre);
        },
        CachingDiskBranch::Step::internal_grow(new_disk, new_root_addr, reads, writes) => {
            reveal(CachingDiskBranch::State::internal_grow);
            assert(post.sealed_roots == pre.sealed_roots);
        },
        CachingDiskBranch::Step::internal_split(new_disk, new_child_addr, receipt, split_arg, reads, writes) => {
            reveal(CachingDiskBranch::State::internal_split);
            assert(post.sealed_roots == pre.sealed_roots);
        },
        CachingDiskBranch::Step::internal_fill_au(aus, new_disk) => {
            reveal(CachingDiskBranch::State::internal_fill_au);
            assert(post.sealed_roots == pre.sealed_roots);
        },
        CachingDiskBranch::Step::disk_internal(new_disk) => {
            reveal(CachingDiskBranch::State::disk_internal);
            assert(post.sealed_roots == pre.sealed_roots);
        },
        CachingDiskBranch::Step::observe_persisted_roots(target_count) => {
            reveal(CachingDiskBranch::State::observe_persisted_roots);
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

state_machine!{ CrashAwareCachingDiskBranch {
    fields {
        pub persistent: PersistentCachingDiskBranch,
        pub ephemeral: EphemeralCachingDiskBranch,
        pub frozen: Option<CachingDiskBranchMetadata>,
        pub prepared: bool,
    }

    pub enum Label {
        LoadEphemeral,
        LoadMetadata{ root: Address, discovered_aus: Set<AU> },
        Query{ key: Key, value: Value },
        Append{ keys: Seq<Key>, msgs: Seq<Message> },
        Internal,
        InternalAlloc{ allocs: Set<AU>, deallocs: Set<AU> },
        CommitStart{ new_boundary_lsn: nat, sealed_roots: Seq<Address> },
        FreezePrepared,
        CommitComplete,
        Crash{ keep_in_flight: bool },
    }

    init!{ initialize() {
        init persistent = PersistentCachingDiskBranch::Image{
            image: empty_caching_disk_branch_image(),
        };
        init ephemeral = EphemeralCachingDiskBranch::Unknown;
        init frozen = Option::None;
        init prepared = false;
    }}

    transition!{ load_ephemeral(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require lbl is LoadEphemeral;
        require pre.ephemeral is Unknown;
        require pre.persistent is Image;
        let image = pre.persistent->image;
        require CachingDiskBranch::State::initialize(new_ephemeral, image);
        update ephemeral = EphemeralCachingDiskBranch::Known{
            v: new_ephemeral,
        };
        update persistent = PersistentCachingDiskBranch::Metadata{
            meta: image.metadata(),
        };
    }}

    transition!{ load_metadata(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require let Label::LoadMetadata{root, discovered_aus} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskBranch::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
        );
        update ephemeral = EphemeralCachingDiskBranch::Known{
            v: new_ephemeral,
        };
    }}

    transition!{ query(lbl: Label, msg: Message) {
        require let Label::Query{key, value} = lbl;
        require pre.ephemeral is Known;
        require normalize_value(msg) == value;
        require CachingDiskBranch::State::next(pre.ephemeral->v, pre.ephemeral->v,
            CachingDiskBranch::Label::QueryLabel{key, msg});
    }}

    transition!{ append(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require let Label::Append{keys, msgs} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskBranch::State::next(pre.ephemeral->v, new_ephemeral,
            CachingDiskBranch::Label::AppendLabel{keys, msgs});
        update ephemeral = EphemeralCachingDiskBranch::Known{ v: new_ephemeral };
    }}

    transition!{ internal(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require lbl is Internal;
        require pre.ephemeral is Known;
        require CachingDiskBranch::State::next(pre.ephemeral->v, new_ephemeral,  CachingDiskBranch::Label::Internal);
        update ephemeral = EphemeralCachingDiskBranch::Known{ v: new_ephemeral };
    }}

    transition!{ internal_alloc(lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        require let Label::InternalAlloc{allocs, deallocs} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskBranch::State::next(pre.ephemeral->v, new_ephemeral,
            CachingDiskBranch::Label::InternalAlloc{allocs, deallocs});
        update ephemeral = EphemeralCachingDiskBranch::Known{ v: new_ephemeral };
    }}

    transition!{ commit_start(lbl: Label) {
        require let Label::CommitStart{new_boundary_lsn, sealed_roots} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        let frozen = CachingDiskBranchMetadata{
            sealed_roots,
            seq_end: new_boundary_lsn,
        };
        let persistent = pre.persistent.metadata();
        require {
            ||| {
                &&& new_boundary_lsn == persistent.seq_end
                &&& sealed_roots == persistent.sealed_roots
            }
            ||| CachingDiskBranch::State::next(
                pre.ephemeral->v,
                pre.ephemeral->v,
                CachingDiskBranch::Label::FreezeAsLabel{image: frozen},
            )
        };

        update frozen = Option::Some(frozen);
    }}

    transition!{ freeze_prepared(lbl: Label) {
        require lbl is FreezePrepared;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require !pre.prepared;
        let frozen = pre.frozen.unwrap();
        require CachingDiskBranch::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskBranch::Label::FreezePrepared{
                image: frozen,
            },
        );

        update prepared = true;
    }}

    transition!{ commit_complete(lbl: Label) {
        require lbl is CommitComplete;
        require pre.frozen is Some;
        require pre.prepared;
        require pre.ephemeral is Known;
        let frozen = pre.frozen.unwrap();
        require CachingDiskBranch::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskBranch::Label::FreezePrepared{
                image: frozen,
            },
        );

        update persistent = PersistentCachingDiskBranch::Metadata{meta: frozen};
        update frozen = Option::None;
        update prepared = false;
    }}

    transition!{ crash(lbl: Label) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.frozen is Some;
        require keep_in_flight ==> pre.prepared;
        let persistent_image = if keep_in_flight && pre.ephemeral is Known {
            CachingDiskBranchImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.frozen.unwrap(),
            )
        } else if pre.ephemeral is Unknown {
            pre.persistent->image
        } else {
            CachingDiskBranchImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.persistent.metadata(),
            )
        };

        update ephemeral = EphemeralCachingDiskBranch::Unknown;
        update frozen = Option::None;
        update prepared = false;
        update persistent = PersistentCachingDiskBranch::Image{
            image: persistent_image,
        };
    }}

    #[invariant]
    pub open spec(checked) fn inv(self) -> bool {
        &&& self.wf()
        &&& self.stack_compatible()
        &&& self.persistent_matches_ephemeral()
        &&& self.frozen is None ==> !self.prepared
        &&& self.frozen is Some ==> self.ephemeral is Known
        &&& self.frozen is Some && self.ephemeral is Known ==> {
            let persistent = self.persistent.metadata();
            ||| {
                &&& self.frozen.unwrap().sealed_roots == persistent.sealed_roots
                &&& self.frozen.unwrap().seq_end == persistent.seq_end
            }
            ||| {
                &&& self.ephemeral->v.metadata_loaded
                &&& self.frozen.unwrap().sealed_roots.len()
                    <= self.ephemeral->v.sealed_roots.len()
                &&& self.ephemeral->v.sealed_roots.subrange(
                    0,
                    self.frozen.unwrap().sealed_roots.len() as int,
                ) == self.frozen.unwrap().sealed_roots
            }
        }
        &&& self.prepared ==> self.frozen is Some
        &&& self.prepared ==> self.ephemeral is Known
        &&& self.prepared && self.ephemeral is Known && self.frozen is Some ==>
            self.frozen.unwrap().sealed_roots.len() <= self.ephemeral->v.persisted_root_count
    }

    #[invariant]
    pub open spec(checked) fn stack_compatible(self) -> bool {
        &&& self.frozen is Some ==> self.persistent.metadata().seq_end <= self.frozen.unwrap().seq_end
        &&& self.ephemeral is Known ==> self.persistent.metadata().seq_end <= self.ephemeral->v.seq_end
        &&& self.ephemeral is Known && self.frozen is Some
            ==> self.frozen.unwrap().seq_end <= self.ephemeral->v.seq_end
    }

    #[invariant]
    pub open spec(checked) fn persistent_matches_ephemeral(self) -> bool {
        self.ephemeral is Known ==> {
            let persistent = self.persistent.metadata();
            &&& persistent.sealed_roots.len() <= self.ephemeral->v.sealed_roots.len()
            &&& self.ephemeral->v.sealed_roots.subrange(
                0,
                persistent.sealed_roots.len() as int,
            ) == persistent.sealed_roots
            &&& persistent.sealed_roots.len() <= self.ephemeral->v.persisted_root_count
        }
    }

    pub proof fn prepared_materialized_image_matches_visible_prefix(self)
        requires
            self.inv(),
            self.prepared,
        ensures
            self.frozen is Some,
            self.ephemeral is Known,
            self.prepared_materialized_image().loadable(),
            self.prepared_materialized_image().stack_wf(),
            self.prepared_materialized_image().sealed_stack_i().wf(
                self.prepared_materialized_image().branch_summary(),
            ),
            self.prepared_materialized_image().branch_summary()
                == self.ephemeral->v.visible_image_for_metadata(
                    self.frozen.unwrap(),
                ).branch_summary(),
            summary_aus(self.prepared_materialized_image().branch_summary())
                <= summary_aus(self.ephemeral->v.interpreted_branch_summary()),
            self.prepared_materialized_image().sealed_stack_i()
                == self.ephemeral->v.visible_image_for_metadata(
                    self.frozen.unwrap(),
                ).sealed_stack_i(),
    {
        let frozen = self.frozen.unwrap();
        let persistent = self.persistent.metadata();
        assert(frozen.sealed_roots.len() <= self.ephemeral->v.persisted_root_count);
        if frozen.sealed_roots == persistent.sealed_roots
            && frozen.seq_end == persistent.seq_end {
            assert(self.ephemeral->v.sealed_roots.subrange(
                0,
                frozen.sealed_roots.len() as int,
            ) == frozen.sealed_roots);
        } else {
            assert(self.ephemeral->v.metadata_loaded);
            assert(self.ephemeral->v.sealed_roots.subrange(
                0,
                frozen.sealed_roots.len() as int,
            ) == frozen.sealed_roots);
        }
        let branch_lbl = CachingDiskBranch::Label::FreezePrepared{image: frozen};
        assert(CachingDiskBranch::State::freeze_prepared(
            self.ephemeral->v,
            self.ephemeral->v,
            branch_lbl,
        )) by {
            reveal(CachingDiskBranch::State::freeze_prepared);
        };
        assert(CachingDiskBranch::State::next_by(
            self.ephemeral->v,
            self.ephemeral->v,
            branch_lbl,
            CachingDiskBranch::Step::freeze_prepared(),
        )) by {
            reveal(CachingDiskBranch::State::next_by);
        };
        assert(CachingDiskBranch::State::next(
            self.ephemeral->v,
            self.ephemeral->v,
            branch_lbl,
        )) by {
            reveal(CachingDiskBranch::State::next);
        };
        let image = self.prepared_materialized_image();
        assert(image == CachingDiskBranchImage::materialized_from_persistent(
            self.ephemeral->v,
            frozen,
        ));
        let full_image = CachingDiskBranchImage{
            persistent: self.ephemeral->v.disk.persistent,
            sealed_roots: frozen.sealed_roots,
            seq_end: frozen.seq_end,
        };
        self.ephemeral->v.prepared_image_matches_visible_prefix(full_image);
        assert(CachingDiskBranchImage::materialized_summary_addrs(
            self.ephemeral->v.disk.persistent,
            frozen,
        ) == addresses_in_aus(summary_aus(full_image.branch_summary()))) by {
            assert(completed_branch_summary_from_reads(
                frozen.sealed_roots,
                to_branch_nodes(self.ephemeral->v.disk.persistent),
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
        assert(CachingDiskBranchMetadata{
            sealed_roots: image.sealed_roots,
            seq_end: image.seq_end,
        } == frozen);
    }

    pub proof fn materialized_image_summary_aus_subset_interpreted(
        self,
        frozen: CachingDiskBranchMetadata,
    )
        requires
            self.inv(),
            self.ephemeral is Known,
            frozen.sealed_roots.len() <= self.ephemeral->v.persisted_root_count,
            self.ephemeral->v.sealed_roots.subrange(
                0,
                frozen.sealed_roots.len() as int,
            ) == frozen.sealed_roots,
        ensures
            summary_aus(CachingDiskBranchImage::materialized_from_persistent(
                self.ephemeral->v,
                frozen,
            ).branch_summary()) <= summary_aus(self.ephemeral->v.interpreted_branch_summary()),
    {
        let branch_lbl = CachingDiskBranch::Label::FreezePrepared{image: frozen};
        assert(CachingDiskBranch::State::freeze_prepared(
            self.ephemeral->v,
            self.ephemeral->v,
            branch_lbl,
        )) by {
            reveal(CachingDiskBranch::State::freeze_prepared);
        };
        assert(CachingDiskBranch::State::next_by(
            self.ephemeral->v,
            self.ephemeral->v,
            branch_lbl,
            CachingDiskBranch::Step::freeze_prepared(),
        )) by {
            reveal(CachingDiskBranch::State::next_by);
        };
        assert(CachingDiskBranch::State::next(
            self.ephemeral->v,
            self.ephemeral->v,
            branch_lbl,
        )) by {
            reveal(CachingDiskBranch::State::next);
        };
        let image = CachingDiskBranchImage::materialized_from_persistent(
            self.ephemeral->v,
            frozen,
        );
        let full_image = CachingDiskBranchImage{
            persistent: self.ephemeral->v.disk.persistent,
            sealed_roots: frozen.sealed_roots,
            seq_end: frozen.seq_end,
        };
        self.ephemeral->v.prepared_image_matches_visible_prefix(full_image);
        assert(CachingDiskBranchImage::materialized_summary_addrs(
            self.ephemeral->v.disk.persistent,
            frozen,
        ) == addresses_in_aus(summary_aus(full_image.branch_summary()))) by {
            assert(completed_branch_summary_from_reads(
                frozen.sealed_roots,
                to_branch_nodes(self.ephemeral->v.disk.persistent),
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
        assert(summary_aus(full_image.branch_summary())
            <= summary_aus(self.ephemeral->v.interpreted_branch_summary()));
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
        empty_caching_disk_branch_image_wf();
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskBranch::State,
    ) {
        match lbl {
            Label::LoadEphemeral => {
                reveal(CrashAwareCachingDiskBranch::State::load_ephemeral);
                reveal(CachingDiskBranch::State::initialize);
                let image = pre.persistent->image;
                CachingDiskBranch::State::initialize_inductive(
                    new_ephemeral,
                    image,
                );
                assert(post.ephemeral == EphemeralCachingDiskBranch::Known{v: new_ephemeral});
                assert(post.persistent == PersistentCachingDiskBranch::Metadata{meta: image.metadata()});
                assert(new_ephemeral == CachingDiskBranch::State::load_from_persistent(image));
                assert(new_ephemeral.sealed_roots == image.sealed_roots);
                assert(new_ephemeral.disk.persistent == image.persistent);
                assert(new_ephemeral.persisted_root_count == image.sealed_roots.len());
                assert_seqs_equal!(
                    post.ephemeral->v.sealed_roots.subrange(
                        0,
                        post.persistent.metadata().sealed_roots.len() as int,
                    ),
                    post.persistent.metadata().sealed_roots
                );
                let branch_lbl = CachingDiskBranch::Label::FreezePrepared{
                    image: CachingDiskBranchMetadata{
                        sealed_roots: image.sealed_roots,
                        seq_end: image.seq_end,
                    },
                };
                assert(CachingDiskBranch::State::next(
                    post.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                )) by {
                    reveal(CachingDiskBranch::State::next);
                    reveal(CachingDiskBranch::State::next_by);
                    assert(CachingDiskBranch::State::freeze_prepared(
                        post.ephemeral->v,
                        post.ephemeral->v,
                        branch_lbl,
                    )) by {
                        reveal(CachingDiskBranch::State::freeze_prepared);
                    };
                    assert(CachingDiskBranch::State::next_by(
                        post.ephemeral->v,
                        post.ephemeral->v,
                        branch_lbl,
                        CachingDiskBranch::Step::freeze_prepared(),
                    ));
                };
                post.ephemeral->v.prepared_image_matches_visible_prefix(image);
                assert_seqs_equal!(
                    post.ephemeral->v.sealed_roots.subrange(
                        0,
                        post.persistent.metadata().sealed_roots.len() as int,
                    ),
                    post.persistent.metadata().sealed_roots
                );
                assert(post.ephemeral->v.disk.inv());
                assert(post.ephemeral->v.inv());
            },
            _ => { }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(load_metadata)]
    fn load_metadata_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskBranch::State,
    ) {
        reveal(CrashAwareCachingDiskBranch::State::load_metadata);
        match lbl {
            Label::LoadMetadata{root, discovered_aus} => {
                let branch_lbl = CachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
                let persistent = pre.persistent.metadata();
                CachingDiskBranch::State::inv_next(pre.ephemeral->v, new_ephemeral, branch_lbl);
                cdb_step_preserves_root_prefix(
                    pre.ephemeral->v,
                    new_ephemeral,
                    branch_lbl,
                    persistent.sealed_roots,
                );
                CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                    pre.ephemeral->v,
                    new_ephemeral,
                    branch_lbl,
                    persistent.sealed_roots.len() as nat,
                );
                CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                    pre.ephemeral->v,
                    new_ephemeral,
                    branch_lbl,
                    persistent.seq_end,
                );
                if pre.frozen is Some {
                    CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                        pre.ephemeral->v,
                        new_ephemeral,
                        branch_lbl,
                        pre.frozen.unwrap().seq_end,
                    );
                    if pre.prepared {
                        CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                            pre.ephemeral->v,
                            new_ephemeral,
                            branch_lbl,
                            pre.frozen.unwrap().sealed_roots.len() as nat,
                        );
                    }
                    if !(pre.frozen.unwrap().sealed_roots == persistent.sealed_roots
                        && pre.frozen.unwrap().seq_end == persistent.seq_end) {
                        CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                            pre.ephemeral->v,
                            new_ephemeral,
                            branch_lbl,
                            pre.frozen.unwrap().sealed_roots,
                        );
                    }
                }
            },
            _ => { }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(query)]
    fn query_inductive(pre: Self, post: Self, lbl: Label, msg: Message) {
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(append)]
    fn append_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        reveal(CrashAwareCachingDiskBranch::State::append);
        let branch_lbl = CachingDiskBranch::Label::AppendLabel{
            keys: lbl.arrow_Append_keys(),
            msgs: lbl.arrow_Append_msgs(),
        };
        let persistent = pre.persistent.metadata();
        CachingDiskBranch::State::inv_next(pre.ephemeral->v, post.ephemeral->v, branch_lbl);
        cdb_step_preserves_root_prefix(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.sealed_roots,
        );
        CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.sealed_roots.len() as nat,
        );
        CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.seq_end,
        );
        if pre.frozen is Some {
            CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                pre.ephemeral->v,
                post.ephemeral->v,
                branch_lbl,
                pre.frozen.unwrap().seq_end,
            );
            if pre.prepared {
                CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots.len() as nat,
                );
            }
            if !(pre.frozen.unwrap().sealed_roots == persistent.sealed_roots
                && pre.frozen.unwrap().seq_end == persistent.seq_end) {
                CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots,
                );
            }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        reveal(CrashAwareCachingDiskBranch::State::internal);
        let branch_lbl = CachingDiskBranch::Label::Internal;
        let persistent = pre.persistent.metadata();
        CachingDiskBranch::State::inv_next(pre.ephemeral->v, post.ephemeral->v, branch_lbl);
        cdb_step_preserves_root_prefix(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.sealed_roots,
        );
        CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.sealed_roots.len() as nat,
        );
        CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.seq_end,
        );
        if pre.frozen is Some {
            CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                pre.ephemeral->v,
                post.ephemeral->v,
                branch_lbl,
                pre.frozen.unwrap().seq_end,
            );
            if pre.prepared {
                CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots.len() as nat,
                );
            }
            if !(pre.frozen.unwrap().sealed_roots == persistent.sealed_roots
                && pre.frozen.unwrap().seq_end == persistent.seq_end) {
                CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots,
                );
            }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(internal_alloc)]
    fn internal_alloc_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskBranch::State) {
        reveal(CrashAwareCachingDiskBranch::State::internal_alloc);
        let branch_lbl = CachingDiskBranch::Label::InternalAlloc{
            allocs: lbl.arrow_InternalAlloc_allocs(),
            deallocs: lbl.arrow_InternalAlloc_deallocs(),
        };
        let persistent = pre.persistent.metadata();
        CachingDiskBranch::State::inv_next(pre.ephemeral->v, post.ephemeral->v, branch_lbl);
        cdb_step_preserves_root_prefix(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.sealed_roots,
        );
        CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.sealed_roots.len() as nat,
        );
        CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
            pre.ephemeral->v,
            post.ephemeral->v,
            branch_lbl,
            persistent.seq_end,
        );
        if pre.frozen is Some {
            CachingDiskBranch::State::next_preserves_seq_end_lower_bound(
                pre.ephemeral->v,
                post.ephemeral->v,
                branch_lbl,
                pre.frozen.unwrap().seq_end,
            );
            if pre.prepared {
                CachingDiskBranch::State::next_preserves_persisted_root_count_lower_bound(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots.len() as nat,
                );
            }
            if !(pre.frozen.unwrap().sealed_roots == persistent.sealed_roots
                && pre.frozen.unwrap().seq_end == persistent.seq_end) {
                CachingDiskBranch::State::next_preserves_loaded_root_prefix(
                    pre.ephemeral->v,
                    post.ephemeral->v,
                    branch_lbl,
                    pre.frozen.unwrap().sealed_roots,
                );
            }
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(CrashAwareCachingDiskBranch::State::commit_start);
        match lbl {
            Label::CommitStart{new_boundary_lsn, sealed_roots} => {
                let frozen = CachingDiskBranchMetadata{
                    sealed_roots,
                    seq_end: new_boundary_lsn,
                };
                let persistent = post.persistent.metadata();
                if !(post.frozen.unwrap().sealed_roots == persistent.sealed_roots
                    && post.frozen.unwrap().seq_end == persistent.seq_end) {
                    reveal(CachingDiskBranch::State::next);
                    reveal(CachingDiskBranch::State::next_by);
                    let branch_lbl = CachingDiskBranch::Label::FreezeAsLabel{image: frozen};
                    let step = choose |step: CachingDiskBranch::Step|
                        CachingDiskBranch::State::next_by(pre.ephemeral->v, pre.ephemeral->v, branch_lbl, step);
                    match step {
                        CachingDiskBranch::Step::freeze_as() => {
                            reveal(CachingDiskBranch::State::freeze_as);
                        },
                        _ => { assert(false); },
                    }
                    assert(sealed_roots == pre.ephemeral->v.sealed_roots);
                    assert(post.frozen.unwrap().sealed_roots == pre.ephemeral->v.sealed_roots);
                    assert(post.frozen.unwrap().sealed_roots.len()
                        == pre.ephemeral->v.sealed_roots.len());
                    assert(pre.ephemeral->v.sealed_roots.subrange(
                        0,
                        post.frozen.unwrap().sealed_roots.len() as int,
                    ) == post.frozen.unwrap().sealed_roots);
                }
            },
            _ => {}
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(freeze_prepared)]
    fn freeze_prepared_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
        assert(post.prepared);
        let frozen = pre.frozen.unwrap();
        let branch_lbl = CachingDiskBranch::Label::FreezePrepared{
            image: frozen,
        };
        assert(CachingDiskBranch::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            branch_lbl,
        )) by {
            reveal(CachingDiskBranch::State::next);
            reveal(CachingDiskBranch::State::next_by);
            assert(CachingDiskBranch::State::freeze_prepared(
                pre.ephemeral->v,
                pre.ephemeral->v,
                branch_lbl,
            )) by {
                reveal(CachingDiskBranch::State::freeze_prepared);
            };
            assert(CachingDiskBranch::State::next_by(
                pre.ephemeral->v,
                pre.ephemeral->v,
                branch_lbl,
                CachingDiskBranch::Step::freeze_prepared(),
            ));
        };
        assert(frozen.sealed_roots.len() <= pre.ephemeral->v.persisted_root_count) by {
            reveal(CachingDiskBranch::State::next);
            reveal(CachingDiskBranch::State::next_by);
            let step = choose |step: CachingDiskBranch::Step|
                CachingDiskBranch::State::next_by(
                    pre.ephemeral->v,
                    pre.ephemeral->v,
                    branch_lbl,
                    step,
                );
            match step {
                CachingDiskBranch::Step::freeze_prepared() => {
                    reveal(CachingDiskBranch::State::freeze_prepared);
                },
                _ => { assert(false); },
            }
            assert(CachingDiskBranch::State::freeze_prepared(
                pre.ephemeral->v,
                pre.ephemeral->v,
                branch_lbl,
            ));
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
    ) {
        reveal(CrashAwareCachingDiskBranch::State::commit_complete);
        let frozen = pre.frozen.unwrap();
        assert(post.ephemeral->v.inv());
        assert(post.wf());
        assert(post.stack_compatible());
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) {
        let persistent_image = if lbl.arrow_Crash_keep_in_flight() && pre.ephemeral is Known {
            CachingDiskBranchImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.frozen.unwrap(),
            )
        } else if pre.ephemeral is Unknown {
            pre.persistent->image
        } else {
            CachingDiskBranchImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.persistent.metadata(),
            )
        };
        if lbl.arrow_Crash_keep_in_flight() {
            pre.prepared_materialized_image_matches_visible_prefix();
            assert(persistent_image == pre.prepared_materialized_image());
        } else {
            assert(post.persistent == PersistentCachingDiskBranch::Image{image: persistent_image});
        }
        assert(post.wf());
        assert(post.stack_compatible());
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CrashAwareCachingDiskBranch::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_ephemeral(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_ephemeral(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_ephemeral);
                }
                CrashAwareCachingDiskBranch::State::load_ephemeral_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_metadata(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_metadata);
                }
                CrashAwareCachingDiskBranch::State::load_metadata_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::query(msg) => {
                assert(CrashAwareCachingDiskBranch::State::query(pre, post, lbl, msg)) by {
                    reveal(CrashAwareCachingDiskBranch::State::query);
                }
                CrashAwareCachingDiskBranch::State::query_inductive(pre, post, lbl, msg);
            },
            CrashAwareCachingDiskBranch::Step::append(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::append(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::append);
                }
                CrashAwareCachingDiskBranch::State::append_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::internal(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::internal(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::internal);
                }
                CrashAwareCachingDiskBranch::State::internal_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::internal_alloc(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::internal_alloc(pre, post, lbl, new_ephemeral)) by {
                    reveal(CrashAwareCachingDiskBranch::State::internal_alloc);
                }
                CrashAwareCachingDiskBranch::State::internal_alloc_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskBranch::Step::commit_start() => {
                assert(CrashAwareCachingDiskBranch::State::commit_start(pre, post, lbl)) by {
                    reveal(CrashAwareCachingDiskBranch::State::commit_start);
                }
                CrashAwareCachingDiskBranch::State::commit_start_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskBranch::Step::freeze_prepared() => {
                assert(CrashAwareCachingDiskBranch::State::freeze_prepared(pre, post, lbl)) by {
                    reveal(CrashAwareCachingDiskBranch::State::freeze_prepared);
                }
                CrashAwareCachingDiskBranch::State::freeze_prepared_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskBranch::Step::commit_complete() => {
                assert(CrashAwareCachingDiskBranch::State::commit_complete(pre, post, lbl)) by {
                    reveal(CrashAwareCachingDiskBranch::State::commit_complete);
                }
                CrashAwareCachingDiskBranch::State::commit_complete_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskBranch::Step::crash() => {
                assert(CrashAwareCachingDiskBranch::State::crash(pre, post, lbl)) by {
                    reveal(CrashAwareCachingDiskBranch::State::crash);
                }
                CrashAwareCachingDiskBranch::State::crash_inductive(pre, post, lbl);
            },
            _ => {
                assert(post.inv());
            },
        }
    }
}}

impl CrashAwareCachingDiskBranch::State {
    pub open spec fn wf(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.frozen is None && !self.prepared
        &&& self.ephemeral is Unknown <==> self.persistent is Image
        &&& self.ephemeral is Known <==> self.persistent is Metadata
        &&& self.ephemeral is Known ==> self.ephemeral->v.inv()
    }

    pub proof fn load_metadata_preserves_full_accessible_aus(
        pre: Self,
        post: Self,
        root: Address,
        discovered_aus: Set<AU>,
    )
        requires
            pre.inv(),
            CrashAwareCachingDiskBranch::State::next(
                pre,
                post,
                CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
            ),
        ensures
            post.persistent == pre.persistent,
            post.frozen == pre.frozen,
            pre.ephemeral is Known,
            post.ephemeral is Known,
            post.ephemeral->v.full_accessible_aus()
                == pre.ephemeral->v.full_accessible_aus(),
    {
        let lbl = CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_metadata(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                )) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_metadata);
                }
                CachingDiskBranch::State::load_metadata_preserves_full_accessible_aus(
                    pre.ephemeral->v,
                    new_ephemeral,
                    root,
                    discovered_aus,
                );
                assert(post.ephemeral->v == new_ephemeral);
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
            CrashAwareCachingDiskBranch::State::next(
                pre,
                post,
                CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
            ),
        ensures
            pre.ephemeral is Known,
            discovered_aus <= pre.ephemeral->v.full_accessible_aus(),
            discovered_aus <= pre.ephemeral->v.semantic_owned_aus(),
    {
        let lbl = CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_metadata(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                )) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_metadata);
                }
                CachingDiskBranch::State::load_metadata_discovered_aus_subset_full_accessible(
                    pre.ephemeral->v,
                    new_ephemeral,
                    root,
                    discovered_aus,
                );
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
            CrashAwareCachingDiskBranch::State::next(
                pre,
                post,
                CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
            ),
        ensures
            post.persistent == pre.persistent,
            post.frozen == pre.frozen,
            pre.ephemeral is Known,
            post.ephemeral is Known,
            summary_aus(post.ephemeral->v.branch_summary)
                <= summary_aus(pre.ephemeral->v.branch_summary) + discovered_aus,
            post.ephemeral->v.accessible_aus()
                <= pre.ephemeral->v.accessible_aus() + discovered_aus,
    {
        let lbl = CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus};
        reveal(CrashAwareCachingDiskBranch::State::next);
        reveal(CrashAwareCachingDiskBranch::State::next_by);
        let step = choose |step| CrashAwareCachingDiskBranch::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskBranch::Step::load_metadata(new_ephemeral) => {
                assert(CrashAwareCachingDiskBranch::State::load_metadata(
                    pre,
                    post,
                    lbl,
                    new_ephemeral,
                )) by {
                    reveal(CrashAwareCachingDiskBranch::State::load_metadata);
                }
                CachingDiskBranch::State::load_metadata_accessible_aus_growth(
                    pre.ephemeral->v,
                    new_ephemeral,
                    root,
                    discovered_aus,
                );
                assert(post.ephemeral->v == new_ephemeral);
            },
            _ => {
                assert(false);
            },
        }
    }
}

}
