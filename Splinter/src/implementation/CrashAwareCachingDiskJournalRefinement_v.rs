// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Refinement from CrashAwareCachingDiskJournal to AllocationCrashAwareJournal.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::assert_maps_equal;

use crate::abstract_system::AbstractCrashAwareJournal_v::AbstractCrashAwareJournal;
use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationCrashAwareJournal_v::{
    AllocationCrashAwareJournal, Ephemeral as AllocationEphemeral,
};
use crate::allocation_layer::AllocationCrashAwareJournalRefinement_v::*;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalMetadata, JournalImage, addrs_in_aus, maps_agree_on,
};
use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::CachingDiskRawPage as RawPage;
use crate::implementation::CachingDiskJournal_v::{
    CachingDiskJournal, cj_lsn_au_index,
};
use crate::implementation::CachingDiskJournalRefinement_v::*;
use crate::implementation::CrashAwareCachingDiskJournal_v::*;
use crate::implementation::JournalTypes_v::{to_journal_records, to_journal_records_restrict};
use crate::journal::LinkedJournal_v::*;

verus!{

impl EphemeralCachingDiskJournal {
    pub open spec fn i(self) -> AllocationEphemeral {
        match self {
            EphemeralCachingDiskJournal::Unknown => AllocationEphemeral::Unknown,
            EphemeralCachingDiskJournal::Known{v} => AllocationEphemeral::Known{v: v.i()},
        }
    }
}

pub open spec fn frozen_image_metadata_i(frozen: CachingDiskJournalFrozenMetadata)
    -> JournalMetadata
{
    JournalMetadata{
        boundary_lsn: frozen.snapshot.boundary_lsn,
        seq_end: frozen.seq_end,
        freshest_rec: frozen.snapshot.freshest_rec(),
        first: frozen.snapshot.first(),
    }
}

pub open spec fn option_frozen_metadata_i(
    frozen: Option<CachingDiskJournalFrozenMetadata>,
) -> Option<JournalMetadata> {
    if frozen is None {
        Option::None
    } else {
        Option::Some(frozen_image_metadata_i(frozen.unwrap()))
    }
}

pub open spec fn materialization_certificate(
    state: CachingDiskJournal::State,
    frozen: CachingDiskJournalFrozenMetadata,
) -> bool
{
    state.frozen_materialization_certificate(frozen.snapshot, frozen.seq_end)
}

impl CrashAwareCachingDiskJournal::State {
    pub open spec fn i(self) -> AllocationCrashAwareJournal::State {
        AllocationCrashAwareJournal::State{
            persistent: frozen_image_metadata_i(self.persistent.metadata()),
            persistent_image: if self.persistent is Image {
                Option::Some(self.persistent->image.i())
            } else {
                Option::None
            },
            ephemeral: self.ephemeral.i(),
            frozen: option_frozen_metadata_i(self.frozen),
        }
    }

    pub open spec fn semantic_inv(self) -> bool {
        &&& self.persistent is Image ==> self.persistent->image.wf()
        &&& self.ephemeral is Known ==> self.ephemeral->v.refinement_inv()
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is None ==>
            self.ephemeral->v.disk.addrs_clean_or_evictable(
                self.ephemeral->v.disk.cache.dom(),
            )
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is Some ==>
            self.ephemeral->v.clean_watermark_au_page_bounds_clean_or_evictable()
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is Some ==>
            self.ephemeral->v.clean_watermark_records_bounded_by_clean_au_page_bounds()
        &&& self.ephemeral is Known ==>
            self.ephemeral->v.i().frozen_metadata_valid(
                frozen_image_metadata_i(self.persistent.metadata()),
            )
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is Some ==>
            materialization_certificate(
                self.ephemeral->v,
                self.persistent.metadata(),
            )
        &&& self.ephemeral is Known && self.ephemeral->v.journal.status is None ==>
            self.ephemeral->v.persistent_visible_agree_on(
                self.ephemeral->v.frozen_loose_domain(self.persistent.metadata().snapshot),
            )
        &&& self.frozen is Some && self.ephemeral is Known ==>
            self.ephemeral->v.i().frozen_metadata_valid(
                frozen_image_metadata_i(self.frozen.unwrap()),
            )
        &&& self.frozen is Some && self.ephemeral is Known ==>
            self.ephemeral->v.frozen_snapshot_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            )
        &&& self.prepared && self.frozen is Some ==>
            materialization_certificate(self.ephemeral->v, self.frozen.unwrap())
    }

    pub open spec fn refinement_inv(self) -> bool {
        &&& self.inv()
        &&& self.semantic_inv()
    }

    pub proof fn semantic_inv_implies_i_inv(self)
        requires
            self.inv(),
            self.semantic_inv(),
        ensures
            self.i().inv(),
    {
        if self.ephemeral is Known {
            self.ephemeral->v.semantic_inv_implies_i_inv();
        }
        if self.frozen is Some && self.ephemeral is Known {
            assert(self.ephemeral->v.i().frozen_metadata_valid(
                frozen_image_metadata_i(self.frozen.unwrap()),
            ));
        }
    }

    pub proof fn internal_allocs_disjoint_implies_fresh_label(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            self.ephemeral is Known,
            self.label_i(post, lbl) is Internal,
            self.label_i(post, lbl).arrow_Internal_allocs()
                .disjoint(caching_disk_journal_accessible_aus(self.ephemeral->v)),
        ensures
            self.i().fresh_label(self.label_i(post, lbl)),
    {
        let allocs = self.label_i(post, lbl).arrow_Internal_allocs();
        let persistent_meta = frozen_image_metadata_i(self.persistent.metadata());
        self.ephemeral->v.i_accessible_aus_subset_accessible_aus();
        self.ephemeral->v.i_frozen_image_accessible_aus(persistent_meta);
        assert(self.i().persistent_image is None);
        assert(self.i().persistent_image_view()
            == self.ephemeral->v.i().frozen_image(persistent_meta));
        assert(self.i().persistent_image_view().accessible_aus()
            <= self.ephemeral->v.accessible_aus());
        assert forall |au: AU| #[trigger] allocs.contains(au)
            implies !self.i().persistent_image_view().accessible_aus().contains(au) by {
            if self.i().persistent_image_view().accessible_aus().contains(au) {
                assert(self.ephemeral->v.accessible_aus().contains(au));
                assert(caching_disk_journal_accessible_aus(self.ephemeral->v).contains(au));
            }
        }
        assert forall |au: AU| #[trigger] allocs.contains(au)
            implies !self.i().ephemeral->v.accessible_aus().contains(au) by {
            if self.i().ephemeral->v.accessible_aus().contains(au) {
                assert(self.ephemeral->v.accessible_aus().contains(au));
                assert(caching_disk_journal_accessible_aus(self.ephemeral->v).contains(au));
            }
        }
    }

    pub proof fn materialization_certificate_implies_materialized_image_refines(
        state: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            state.refinement_inv(),
            materialization_certificate(state, frozen),
        ensures
            CachingDiskJournalImage::materialized_from_persistent(
                state,
                frozen,
            ).wf(),
            state.i().acceptable_frozen_image(
                frozen_image_metadata_i(frozen),
                CachingDiskJournalImage::materialized_from_persistent(
                    state,
                    frozen,
                ).i(),
            ),
    {
        let meta = frozen_image_metadata_i(frozen);
        let image = CachingDiskJournalImage::materialized_from_persistent(state, frozen);
        let concrete_prefix = state.frozen_prefix_domain(frozen.snapshot);
        let allocation_prefix = state.i().frozen_prefix_domain(meta);

        state.frozen_snapshot_valid_implies_i_metadata_valid(frozen.snapshot, frozen.seq_end);
        state.i_metadata_valid_implies_frozen_tj_matches_i(frozen.snapshot, frozen.seq_end);
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            state.i(),
            state.i(),
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(state.i(), state.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        AllocationJournal::State::frozen_journal_is_valid_image(
            state.i(),
            state.i(),
            freeze_lbl,
        );
        let base_image = state.i().frozen_image(meta);
        assert(base_image.valid_image());

        state.persistent_dom_wf();
        assert(image.i().tj.disk_view.wf_addrs()) by {
            assert forall |addr: Address| #[trigger] image.i().tj.disk_view.entries.contains_key(addr)
                implies addr.wf() by {
                assert(to_journal_records(image.persistent).contains_key(addr));
                assert(image.persistent.contains_key(addr));
                assert(image.persistent.dom().contains(addr));
                assert(state.disk.persistent.contains_key(addr));
                assert(state.disk.persistent.dom().contains(addr));
            }
        }
        assert(state.frozen_loose_domain(frozen.snapshot) =~= state.i().frozen_loose_domain(meta));
        assert(image.i().tj.disk_view.entries.dom() <= state.i().frozen_loose_domain(meta)) by {
            assert forall |addr: Address|
                #[trigger] image.i().tj.disk_view.entries.dom().contains(addr)
                implies state.i().frozen_loose_domain(meta).contains(addr) by {
                assert(image.i().tj.disk_view.entries.contains_key(addr));
                assert(to_journal_records(image.persistent).contains_key(addr));
                assert(image.persistent.contains_key(addr));
                assert(state.disk.persistent.restrict(state.frozen_loose_domain(frozen.snapshot)).contains_key(addr));
                assert(state.frozen_loose_domain(frozen.snapshot).contains(addr));
            }
        }

        assert(maps_agree_on(
            allocation_prefix,
            image.i().tj.disk_view.entries,
            state.i().disk_view.entries,
        )) by {
            assert(allocation_prefix =~= concrete_prefix);
            assert_maps_equal!(
                image.i().tj.disk_view.entries.restrict(allocation_prefix),
                state.i().disk_view.entries.restrict(allocation_prefix),
                addr => {
                    if image.i().tj.disk_view.entries.restrict(allocation_prefix).contains_key(addr) {
                        assert(allocation_prefix.contains(addr));
                        assert(concrete_prefix.contains(addr));
                        assert(image.i().tj.disk_view.entries.contains_key(addr));
                        assert(to_journal_records(image.persistent).contains_key(addr));
                        assert(image.persistent.contains_key(addr));
                        assert(image.persistent[addr] == state.disk.persistent[addr]);
                        assert(state.disk.persistent.restrict(concrete_prefix)
                            == state.disk.visible().restrict(concrete_prefix));
                        assert(state.disk.visible().contains_key(addr));
                        assert(state.disk.persistent.restrict(concrete_prefix).contains_key(addr));
                        assert(state.disk.visible().restrict(concrete_prefix).contains_key(addr));
                        assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                            == state.disk.visible().restrict(concrete_prefix)[addr]);
                        assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                            == state.disk.persistent[addr]);
                        assert(state.disk.visible().restrict(concrete_prefix)[addr]
                            == state.disk.visible()[addr]);
                        assert(state.disk.persistent[addr] == state.disk.visible()[addr]);
                        assert(state.i().disk_view.entries.contains_key(addr));
                        assert(state.i().disk_view.entries[addr] == to_journal_records(state.disk.visible())[addr]);
                        assert(image.i().tj.disk_view.entries[addr]
                            == to_journal_records(image.persistent)[addr]);
                        assert(to_journal_records(image.persistent)[addr]
                            == to_journal_records(state.disk.visible())[addr]);
                    }
                    if state.i().disk_view.entries.restrict(allocation_prefix).contains_key(addr) {
                        assert(allocation_prefix.contains(addr));
                        assert(concrete_prefix.contains(addr));
                        assert(state.i().disk_view.entries.contains_key(addr));
                        assert(state.disk.visible().contains_key(addr));
                        assert(state.disk.persistent.restrict(concrete_prefix)
                            == state.disk.visible().restrict(concrete_prefix));
                        assert(state.disk.visible().restrict(concrete_prefix).contains_key(addr));
                        assert(state.disk.persistent.restrict(concrete_prefix).contains_key(addr));
                        assert(state.disk.persistent.contains_key(addr));
                        assert(state.disk.visible().restrict(concrete_prefix)[addr]
                            == state.disk.visible()[addr]);
                        assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                            == state.disk.persistent[addr]);
                        assert(state.disk.persistent.restrict(concrete_prefix)[addr]
                            == state.disk.visible().restrict(concrete_prefix)[addr]);
                        assert(state.disk.persistent[addr] == state.disk.visible()[addr]);
                        assert(image.persistent.contains_key(addr));
                        assert(image.persistent[addr] == state.disk.persistent[addr]);
                        assert(to_journal_records(image.persistent).contains_key(addr));
                        assert(image.i().tj.disk_view.entries.contains_key(addr));
                        assert(to_journal_records(image.persistent)[addr]
                            == to_journal_records(state.disk.visible())[addr]);
                    }
                }
            );
        }

        let base_tight = base_image.tight_tj();
        let image_tj = image.i().tj;
        let image_dv = image_tj.disk_view;
        let root = image_tj.freshest_rec;
        let tight_index = base_tight.build_lsn_au_index_from_first(meta.first);
        let base_bounds = base_tight.disk_view.build_au_page_bounds_au_walk(
            base_tight.freshest_rec,
            meta.first,
        );
        base_image.valid_image_implies_tight_valid_image();
        base_image.valid_image_implies_tight_seq_bounds();
        base_image.tj.disk_view.path_build_tight_is_sub_disk(base_image.tj.freshest_rec);
        base_tight.disk_view.decodable_implies_path_decodable(base_tight.freshest_rec);
        base_image.tj.disk_view.path_build_tight_idempotent(base_image.tj.freshest_rec);
        base_tight.disk_view.path_build_tight_equals_build_tight(base_tight.freshest_rec);
        base_tight.disk_view.build_au_page_bounds_au_walk_domain_matches_build_tight(
            base_tight.freshest_rec,
            meta.first,
        );
        assert(base_tight.disk_view.build_tight(base_tight.freshest_rec)
            == base_tight.disk_view);
        assert(base_tight.disk_view.entries_bounded_by_au_page_bounds(base_bounds)
            == base_tight.disk_view.entries);
        assert(base_tight.build_lsn_au_index_from_first(meta.first)
            == state.i().frozen_lsn_au_index(meta));
        assert(base_tight.disk_view.entries <= image_dv.entries) by {
            assert forall |addr: Address| #[trigger] base_tight.disk_view.entries.contains_key(addr)
                implies image_dv.entries.contains_key(addr)
                    && image_dv.entries[addr] == base_tight.disk_view.entries[addr] by {
                assert(base_tight.disk_view.is_sub_disk_with_newer_lsn(state.i().tj().disk_view));
                assert(state.i().tj().disk_view.entries.contains_key(addr));
                assert(state.i().tj().disk_view.entries[addr] == base_tight.disk_view.entries[addr]);
                assert(base_tight.disk_view.is_sub_disk(base_image.tj.disk_view)) by {
                    base_image.tj.disk_view.path_build_tight_is_sub_disk(base_image.tj.freshest_rec);
                }
                assert(base_image.tj.disk_view.entries.contains_key(addr));
                assert(base_tight.disk_view.entries_bounded_by_au_page_bounds(base_bounds)
                    .contains_key(addr));
                assert(base_bounds.contains_key(addr.au));
                assert(addr.page <= base_bounds[addr.au]);
                assert(allocation_prefix.contains(addr));
                assert(maps_agree_on(
                    allocation_prefix,
                    image.i().tj.disk_view.entries,
                    state.i().disk_view.entries,
                ));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)
                    == state.i().disk_view.entries.restrict(allocation_prefix));
                assert(state.i().disk_view.entries.contains_key(addr));
                assert(state.i().disk_view.entries[addr] == state.i().tj().disk_view.entries[addr]) by {
                    assert(state.i().tj().disk_view.is_sub_disk(state.i().disk_view));
                }
                assert(state.i().disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)[addr]
                    == state.i().disk_view.entries.restrict(allocation_prefix)[addr]);
                assert(image.i().tj.disk_view.entries.contains_key(addr));
                assert(image.i().tj.disk_view.entries[addr] == state.i().disk_view.entries[addr]);
            }
        }
        assert(base_tight.disk_view.is_sub_disk(image_dv)) by {
            assert(base_tight.disk_view.boundary_lsn == image_dv.boundary_lsn);
            assert(base_tight.disk_view.entries <= image_dv.entries);
        }
        assert(base_tight.disk_view.path_build_tight(base_tight.freshest_rec)
            == base_tight.disk_view);
        base_tight.disk_view.path_build_tight_preserved_in_superdisk(image_dv, root);
        assert(image.i().tight_tj() == base_tight);
        assert(image.i().tj.disk_view.domain_au_bounded_wrt_index(tight_index)) by {
            assert forall |addr: Address| #[trigger] image.i().tj.disk_view.entries.dom().contains(addr)
                implies tight_index.values().contains(addr.au) by {
                assert(state.i().frozen_loose_domain(meta).contains(addr));
                assert(state.i().frozen_domain(meta).contains(addr));
                assert(addrs_in_aus(state.i().frozen_lsn_au_index(meta).values()).contains(addr));
                assert(state.i().frozen_lsn_au_index(meta).values().contains(addr.au));
            }
        }
        assert(image.i().bounded_live_entries_are_tight()) by {
            assert forall |addr: Address| {
                let record = image.i().tj.disk_view.entries[addr];
                &&& #[trigger] image.i().tj.disk_view.entries.contains_key(addr)
                &&& base_bounds.contains_key(addr.au)
                &&& addr.page <= base_bounds[addr.au]
                &&& image.i().tj.seq_start() < record.message_seq.seq_end
            } implies base_tight.disk_view.entries.contains_key(addr) by {
                assert(state.i().frozen_loose_domain(meta).contains(addr));
                assert(allocation_prefix.contains(addr));
                assert(maps_agree_on(
                    allocation_prefix,
                    image.i().tj.disk_view.entries,
                    state.i().disk_view.entries,
                ));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)
                    == state.i().disk_view.entries.restrict(allocation_prefix));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(state.i().disk_view.entries.restrict(allocation_prefix).contains_key(addr));
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)[addr]
                    == image.i().tj.disk_view.entries[addr]);
                assert(state.i().disk_view.entries.restrict(allocation_prefix)[addr]
                    == state.i().disk_view.entries[addr]);
                assert(image.i().tj.disk_view.entries.restrict(allocation_prefix)[addr]
                    == state.i().disk_view.entries.restrict(allocation_prefix)[addr]);
                assert(state.i().disk_view.entries.contains_key(addr));
                assert(state.i().disk_view.entries[addr] == image.i().tj.disk_view.entries[addr]);
                assert(base_image.tj.disk_view.entries.contains_key(addr)) by {
                    assert(state.i().frozen_tj(meta).disk_view.entries.contains_key(addr));
                }
                assert(base_image.tj.disk_view.entries[addr]
                    == image.i().tj.disk_view.entries[addr]);
                assert(base_image.bounded_live_entries_are_tight());
            }
        }
        assert(image.i().valid_image());
        assert(image.i().first == meta.first);
        assert(image.i().tj.freshest_rec == meta.freshest_rec);
        assert(image.i().tj.disk_view.boundary_lsn == meta.boundary_lsn);
        assert(image.i().tj.seq_end() == meta.seq_end);
        assert(image.seq_end == meta.seq_end);
        image.i_valid_image_seq_end_implies_wf();
    }

    pub proof fn prepared_materialized_image_refines(
        self,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            self.refinement_inv(),
            self.ephemeral is Known,
            self.frozen is Some,
            self.frozen.unwrap() == frozen,
            self.ephemeral->v.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end),
            CachingDiskJournal::State::next(
                self.ephemeral->v,
                self.ephemeral->v,
                CachingDiskJournal::Label::CommitPrepared{
                    frozen: frozen.snapshot,
                    seq_end: frozen.seq_end,
                },
            ),
        ensures
            materialization_certificate(self.ephemeral->v, frozen),
            CachingDiskJournalImage::materialized_from_persistent(
                self.ephemeral->v,
                frozen,
            ).wf(),
            self.ephemeral->v.i().acceptable_frozen_image(
                frozen_image_metadata_i(frozen),
                CachingDiskJournalImage::materialized_from_persistent(
                    self.ephemeral->v,
                    frozen,
                ).i(),
            ),
    {
        let state = self.ephemeral->v;
        CachingDiskJournal::State::commit_prepared_effect(
            state,
            frozen.snapshot,
            frozen.seq_end,
        );
        state.frozen_snapshot_valid_implies_i_metadata_valid(frozen.snapshot, frozen.seq_end);
        if frozen.snapshot.freshest_rec() is Some {
            assert(state.clean_watermark_au_page_bounds_clean_or_evictable());
            state.clean_watermark_au_page_bounds_clean_implies_frozen_materialization_certificate(
                frozen.snapshot,
                frozen.seq_end,
            );
        } else {
            state.rootless_frozen_snapshot_materialization_certificate(
                frozen.snapshot,
                frozen.seq_end,
            );
        }
        assert(materialization_certificate(state, frozen));
        Self::materialization_certificate_implies_materialized_image_refines(state, frozen);
    }

    pub proof fn loaded_materialized_persistent_image_refines(
        image: CachingDiskJournalImage,
    )
        requires
            image.wf(),
        ensures
            ({
                let loaded = CachingDiskJournal::State::load_from_persistent(
                    image.snapshot,
                    image.persistent,
                );
                let frozen = image.metadata();
                let materialized = CachingDiskJournalImage::materialized_from_persistent(
                    loaded,
                    frozen,
                );
                let meta = frozen_image_metadata_i(frozen);
                &&& materialized == image
                &&& materialized.wf()
                &&& loaded.i().acceptable_frozen_image(meta, materialized.i())
            }),
    {
        let loaded = CachingDiskJournal::State::load_from_persistent(
            image.snapshot,
            image.persistent,
        );
        let frozen = image.metadata();
        let materialized = CachingDiskJournalImage::materialized_from_persistent(
            loaded,
            frozen,
        );
        let persistent = image.i();
        let meta = frozen_image_metadata_i(frozen);

        CachingDiskJournal::State::load_from_persistent_refines_image(
            image.snapshot,
            image.persistent,
            persistent,
        );
        AllocationJournal::State::initialize_inductive(loaded.i(), persistent);
        AllocationJournal::State::initialize_semantic_inv(loaded.i(), persistent);
        assert(loaded.i().semantic_inv());

        assert(loaded.i().disk_view == persistent.tj.disk_view);
        assert(loaded.i().lsn_au_index == loaded.lsn_au_index_or_empty());
        assert(loaded.journal_disk_view().entries == persistent.tj.disk_view.entries);
        assert(loaded.frozen_seq_end(frozen.snapshot) == frozen.seq_end) by {
            if frozen.snapshot.freshest_rec() is Some {
                let root = frozen.snapshot.freshest_rec().unwrap();
                assert(persistent.tj.disk_view.entries.contains_key(root));
                assert(persistent.tj.disk_view.entries[root].message_seq.seq_end
                    == persistent.tj.seq_end());
                assert(persistent.tj.seq_end() == frozen.seq_end);
            } else {
                assert(frozen.snapshot.boundary_lsn == persistent.tj.seq_end());
                assert(persistent.tj.seq_end() == frozen.seq_end);
            }
        }
        assert(loaded.i().frozen_lsns(meta) =~= loaded.frozen_lsns(frozen.snapshot)) by {
            assert forall |lsn: LSN| #[trigger] loaded.i().frozen_lsns(meta).contains(lsn)
                <==> loaded.frozen_lsns(frozen.snapshot).contains(lsn) by {}
        }
        assert(loaded.i().frozen_lsn_au_index(meta)
            =~= loaded.lsn_au_index_or_empty().restrict(loaded.frozen_lsns(frozen.snapshot))) by {
            assert forall |lsn: LSN|
                #[trigger] loaded.i().frozen_lsn_au_index(meta).contains_key(lsn)
                <==> loaded.lsn_au_index_or_empty().restrict(
                    loaded.frozen_lsns(frozen.snapshot),
                ).contains_key(lsn) by {}
            assert forall |lsn: LSN|
                #[trigger] loaded.i().frozen_lsn_au_index(meta).contains_key(lsn)
                implies loaded.i().frozen_lsn_au_index(meta)[lsn]
                    == loaded.lsn_au_index_or_empty().restrict(
                        loaded.frozen_lsns(frozen.snapshot),
                    )[lsn] by {}
        }
        assert(loaded.i().frozen_lsn_au_index(meta).values()
            =~= loaded.lsn_au_index_or_empty().restrict(
                loaded.frozen_lsns(frozen.snapshot),
            ).values());
        assert(loaded.i().frozen_loose_domain(meta)
            =~= loaded.frozen_loose_domain(frozen.snapshot)) by {
            assert forall |addr: Address|
                #[trigger] loaded.i().frozen_loose_domain(meta).contains(addr)
                <==> loaded.frozen_loose_domain(frozen.snapshot).contains(addr) by {}
        }

        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            loaded.i(),
            loaded.i(),
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(loaded.i(), loaded.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        AllocationJournal::State::frozen_journal_is_valid_image(
            loaded.i(),
            loaded.i(),
            freeze_lbl,
        );

        assert(loaded.i().acceptable_frozen_image(meta, persistent)) by {
            assert(persistent.valid_image());
            assert(persistent.first == meta.first);
            assert(persistent.tj.freshest_rec == meta.freshest_rec);
            assert(persistent.tj.disk_view.boundary_lsn == meta.boundary_lsn);
            assert(persistent.tj.seq_end() == meta.seq_end);
            let tight_index = persistent.tight_tj().build_lsn_au_index_from_first(
                persistent.first,
            );
            assert(loaded.i().lsn_au_index == tight_index);
            assert(persistent.tj.disk_view.domain_au_bounded_wrt_index(tight_index));
            assert(persistent.tj.disk_view.entries.dom()
                <= loaded.i().frozen_loose_domain(meta)) by {
                assert forall |addr: Address|
                    #[trigger] persistent.tj.disk_view.entries.dom().contains(addr)
                    implies loaded.i().frozen_loose_domain(meta).contains(addr) by {
                    assert(tight_index.values().contains(addr.au));
                    assert(loaded.i().lsn_au_index.values().contains(addr.au));
                    let lsn = choose |lsn: nat| #![trigger loaded.i().lsn_au_index[lsn]] {
                        &&& loaded.i().lsn_au_index.contains_key(lsn)
                        &&& loaded.i().lsn_au_index[lsn] == addr.au
                    };
                    assert(tight_index.contains_key(lsn));
                    persistent.tight_tj().build_lsn_au_index_from_first_ensures(
                        persistent.first,
                    );
                    reveal(TruncatedJournal::au_domain_valid);
                    assert(persistent.tight_tj().seq_start() <= lsn
                        < persistent.tight_tj().seq_end());
                    persistent.valid_image_implies_tight_seq_bounds();
                    assert(meta.boundary_lsn <= lsn < meta.seq_end);
                    assert(loaded.i().frozen_lsns(meta).contains(lsn));
                    assert(loaded.i().frozen_lsn_au_index(meta).contains_key(lsn));
                    assert(loaded.i().frozen_lsn_au_index(meta)[lsn] == addr.au);
                    assert(loaded.i().frozen_lsn_au_index(meta).values().contains(addr.au));
                }
            }
            assert(maps_agree_on(
                loaded.i().frozen_prefix_domain(meta),
                persistent.tj.disk_view.entries,
                loaded.i().disk_view.entries,
            ));
        }

        assert(materialized.persistent == image.persistent) by {
            assert_maps_equal!(materialized.persistent, image.persistent, addr => {
                if materialized.persistent.contains_key(addr) {
                    assert(loaded.disk.persistent.contains_key(addr));
                }
                if image.persistent.contains_key(addr) {
                    assert(persistent.tj.disk_view.entries.contains_key(addr));
                    assert(loaded.i().frozen_loose_domain(meta).contains(addr));
                    assert(loaded.frozen_loose_domain(frozen.snapshot).contains(addr));
                    assert(loaded.disk.persistent.restrict(
                        loaded.frozen_loose_domain(frozen.snapshot),
                    ).contains_key(addr));
                }
            });
        }
        assert(materialized.snapshot == image.snapshot);
        assert(materialized.seq_end == image.seq_end);
        assert(materialized == image);
        assert(materialized.wf());
        assert(loaded.i().acceptable_frozen_image(meta, materialized.i()));
    }

    pub proof fn unloaded_materialized_persistent_image_refines(
        state: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            state.refinement_inv(),
            state.journal.status is None,
            state.i().frozen_metadata_valid(frozen_image_metadata_i(frozen)),
            state.persistent_visible_agree_on(state.frozen_loose_domain(frozen.snapshot)),
        ensures
            ({
                let materialized = CachingDiskJournalImage::materialized_from_persistent(
                    state,
                    frozen,
                );
                let meta = frozen_image_metadata_i(frozen);
                &&& materialized.wf()
                &&& state.i().acceptable_frozen_image(meta, materialized.i())
            }),
    {
        let materialized = CachingDiskJournalImage::materialized_from_persistent(
            state,
            frozen,
        );
        let meta = frozen_image_metadata_i(frozen);

        state.semantic_inv_implies_i_inv();
        state.i_metadata_valid_implies_frozen_tj_matches_i(frozen.snapshot, frozen.seq_end);
        let freeze_lbl = AllocationJournal::Label::FreezeForCommit{frozen_journal: meta};
        assert(AllocationJournal::State::next_by(
            state.i(),
            state.i(),
            freeze_lbl,
            AllocationJournal::Step::freeze_for_commit(),
        )) by {
            reveal(AllocationJournal::State::next_by);
        }
        assert(AllocationJournal::State::next(state.i(), state.i(), freeze_lbl)) by {
            reveal(AllocationJournal::State::next);
        }
        AllocationJournal::State::frozen_journal_is_valid_image(
            state.i(),
            state.i(),
            freeze_lbl,
        );

        let domain = state.frozen_loose_domain(frozen.snapshot);
        to_journal_records_restrict(state.disk.persistent, domain);
        to_journal_records_restrict(state.disk.visible(), domain);
        assert(materialized.i().tj.disk_view.entries
            == state.frozen_tj(frozen.snapshot).disk_view.entries) by {
            assert_maps_equal!(
                materialized.i().tj.disk_view.entries,
                state.frozen_tj(frozen.snapshot).disk_view.entries,
                addr => {}
            );
        }
        assert(materialized.i() == state.i().frozen_image(meta));
        assert(materialized.i().valid_image());
        assert(materialized.i().tj.seq_end() == meta.seq_end);
        assert(materialized.seq_end == meta.seq_end);
        materialized.i_valid_image_seq_end_implies_wf();
        assert(materialized.wf());
        assert(maps_agree_on(
            state.i().frozen_prefix_domain(meta),
            materialized.i().tj.disk_view.entries,
            state.i().disk_view.entries,
        )) by {
            let prefix = state.i().frozen_prefix_domain(meta);
            assert_maps_equal!(
                materialized.i().tj.disk_view.entries.restrict(prefix),
                state.i().disk_view.entries.restrict(prefix),
                addr => {
                    if materialized.i().tj.disk_view.entries.restrict(prefix).contains_key(addr) {
                        assert(prefix.contains(addr));
                        assert(state.i().frozen_loose_domain(meta).contains(addr));
                        assert(state.i().frozen_tj(meta).disk_view.entries.contains_key(addr));
                        assert(state.i().frozen_tj(meta).disk_view.entries[addr]
                            == state.i().disk_view.entries[addr]);
                    }
                    if state.i().disk_view.entries.restrict(prefix).contains_key(addr) {
                        assert(prefix.contains(addr));
                        assert(state.i().frozen_loose_domain(meta).contains(addr));
                        assert(state.i().frozen_tj(meta).disk_view.entries.contains_key(addr));
                        assert(state.i().frozen_tj(meta).disk_view.entries[addr]
                            == state.i().disk_view.entries[addr]);
                    }
                }
            );
        }
        assert(state.i().acceptable_frozen_image(meta, materialized.i()));
    }

    pub proof fn materialized_from_persistent_unchanged(
        pre: CachingDiskJournal::State,
        post: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenMetadata,
    )
        requires
            pre.disk.persistent == post.disk.persistent,
            pre.lsn_au_index_or_empty() == post.lsn_au_index_or_empty(),
            pre.frozen_seq_end(frozen.snapshot) == post.frozen_seq_end(frozen.snapshot),
        ensures
            CachingDiskJournalImage::materialized_from_persistent(pre, frozen)
                == CachingDiskJournalImage::materialized_from_persistent(post, frozen),
    {
        assert(pre.frozen_lsns(frozen.snapshot) =~= post.frozen_lsns(frozen.snapshot)) by {
            assert forall |lsn: LSN| #[trigger] pre.frozen_lsns(frozen.snapshot).contains(lsn)
                <==> post.frozen_lsns(frozen.snapshot).contains(lsn) by {}
        }
        assert(pre.frozen_loose_domain(frozen.snapshot)
            =~= post.frozen_loose_domain(frozen.snapshot)) by {
            assert forall |addr: Address|
                #[trigger] pre.frozen_loose_domain(frozen.snapshot).contains(addr)
                <==> post.frozen_loose_domain(frozen.snapshot).contains(addr) by {}
        }
        assert(pre.disk.persistent.restrict(pre.frozen_loose_domain(frozen.snapshot))
            == post.disk.persistent.restrict(post.frozen_loose_domain(frozen.snapshot))) by {
            assert_maps_equal!(
                pre.disk.persistent.restrict(pre.frozen_loose_domain(frozen.snapshot)),
                post.disk.persistent.restrict(post.frozen_loose_domain(frozen.snapshot)),
                addr => {}
            );
        }
    }

    pub open spec fn i_abstract(self) -> AbstractCrashAwareJournal::State {
        self.i().i()
    }

    pub open spec fn label_i(self, post: Self, lbl: CrashAwareCachingDiskJournal::Label)
        -> AllocationCrashAwareJournal::Label
    {
        match lbl {
            CrashAwareCachingDiskJournal::Label::LoadEphemeral =>
                AllocationCrashAwareJournal::Label::LoadEphemeralFromPersistent,
            CrashAwareCachingDiskJournal::Label::ReadForRecovery{records} =>
                AllocationCrashAwareJournal::Label::ReadForRecovery{records},
            CrashAwareCachingDiskJournal::Label::QueryEndLsn{end_lsn} =>
                AllocationCrashAwareJournal::Label::QueryEndLsn{end_lsn},
            CrashAwareCachingDiskJournal::Label::Put{records} =>
                AllocationCrashAwareJournal::Label::Put{records},
            CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus} =>
                AllocationCrashAwareJournal::Label::Internal{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                },
            CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus} =>
                AllocationCrashAwareJournal::Label::Internal{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                },
            CrashAwareCachingDiskJournal::Label::CommitPrepared =>
                AllocationCrashAwareJournal::Label::Internal{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                },
            CrashAwareCachingDiskJournal::Label::Internal =>
                AllocationCrashAwareJournal::Label::Internal{
                    allocs: Set::empty(),
                    deallocs: Set::empty(),
                },
            CrashAwareCachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus} =>
                AllocationCrashAwareJournal::Label::Internal{allocs, deallocs},
            CrashAwareCachingDiskJournal::Label::QueryLsnPersistence{sync_lsn} =>
                AllocationCrashAwareJournal::Label::QueryLsnPersistence{sync_lsn},
            CrashAwareCachingDiskJournal::Label::CommitStart{new_boundary_lsn, snapshot, seq_end} =>
                AllocationCrashAwareJournal::Label::CommitStart{
                    new_boundary_lsn,
                    frozen_journal: JournalMetadata{
                        boundary_lsn: snapshot.boundary_lsn,
                        seq_end,
                        freshest_rec: snapshot.freshest_rec(),
                        first: snapshot.first(),
                    },
                },
            CrashAwareCachingDiskJournal::Label::CommitComplete{require_end, discarded} =>
                AllocationCrashAwareJournal::Label::CommitComplete{
                    require_end,
                    discarded,
                },
            CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight} =>
                AllocationCrashAwareJournal::Label::Crash{keep_in_flight},
        }
    }

    pub open spec fn label_i_abstract(self, post: Self, lbl: CrashAwareCachingDiskJournal::Label)
        -> AbstractCrashAwareJournal::Label
    {
        self.i().label_i(self.label_i(post, lbl))
    }

    pub proof fn load_ephemeral_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::load_ephemeral(self, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::load_ephemeral);
        let image = self.persistent->image;
        let loaded = CachingDiskJournal::State::load_from_persistent(
            image.snapshot,
            image.persistent,
        );
        assert(post.ephemeral == EphemeralCachingDiskJournal::Known{v: loaded});
        CachingDiskJournal::State::load_from_persistent_refines_image(
            image.snapshot,
            image.persistent,
            image.i(),
        );
        assert(self.i().persistent_image.unwrap() == image.i());
        assert(AllocationJournal::State::initialize(loaded.i(), image.i()));
        assert(loaded.i().mini_allocator == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
        assert(loaded.i().mini_allocator.curr is None);
        assert(loaded.i().mini_allocator.all_aus() =~= Set::<AU>::empty());
        assert(loaded.i().mini_allocator.all_aus().disjoint(image.i().accessible_aus()));
        assert(self.i().persistent_image.unwrap().init_by(loaded.i()));
        Self::loaded_materialized_persistent_image_refines(image);
        let domain = loaded.frozen_loose_domain(image.snapshot);
        assert(loaded.disk.cache == Map::<Address, RawPage>::empty());
        assert(loaded.disk.visible() == loaded.disk.persistent) by {
            assert_maps_equal!(loaded.disk.visible(), loaded.disk.persistent, addr => {
                if loaded.disk.visible().contains_key(addr) {
                    assert(!loaded.disk.cache.contains_key(addr));
                }
                if loaded.disk.persistent.contains_key(addr) {
                    assert(loaded.disk.visible().contains_key(addr));
                }
            });
        }
        assert(loaded.persistent_visible_agree_on(domain)) by {
            assert_maps_equal!(
                loaded.disk.persistent.restrict(domain),
                loaded.disk.visible().restrict(domain),
                addr => {}
            );
        }
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::load_ephemeral_from_persistent(loaded.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn read_for_recovery_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::read_for_recovery(self, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::read_for_recovery);
        let records = lbl.arrow_ReadForRecovery_records();
        let cj_lbl = CachingDiskJournal::Label::ReadForRecovery{messages: records};
        self.ephemeral->v.next_refines(self.ephemeral->v, cj_lbl);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::read_for_recovery(),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn query_end_lsn_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::query_end_lsn(self, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::query_end_lsn);
        let end_lsn = lbl.arrow_QueryEndLsn_end_lsn();
        let cj_lbl = CachingDiskJournal::Label::QueryEndLsn{end_lsn};
        self.ephemeral->v.next_refines(self.ephemeral->v, cj_lbl);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::query_end_lsn(),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn put_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::put(self, post, lbl, new_ephemeral),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::put);
        let records = lbl.arrow_Put_records();
        let cj_lbl = CachingDiskJournal::Label::Put{messages: records};
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        self.ephemeral->v.put_requires_loaded(new_ephemeral, records);
        CachingDiskJournal::State::put_preserves_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            records,
        );
        self.ephemeral->v.put_preserves_clean_watermark_records_bounded(
            new_ephemeral,
            records,
        );
        self.ephemeral->v.put_preserves_frozen_materialization_certificate(
            new_ephemeral,
            records,
            self.persistent.metadata().snapshot,
            self.persistent.metadata().seq_end,
        );
        if self.prepared && self.frozen is Some {
            self.ephemeral->v.put_preserves_frozen_materialization_certificate(
                new_ephemeral,
                records,
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            );
        }
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::put(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        self.semantic_inv_implies_i_inv();
        AllocationCrashAwareJournal::State::inv_next(self.i(), post.i(), self.label_i(post, lbl));
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn query_lsn_persistence_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::query_lsn_persistence(self, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::query_lsn_persistence);
        assert(lbl.arrow_QueryLsnPersistence_sync_lsn() <= self.i().persistent.seq_end);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::query_lsn_persistence(),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post == self);
        assert(post.refinement_inv());
    }

    pub proof fn commit_start_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_start(self, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::commit_start);
        let snapshot = lbl.arrow_CommitStart_snapshot();
        let seq_end = lbl.arrow_CommitStart_seq_end();
        let cj_lbl = CachingDiskJournal::Label::FreezeForCommit{frozen: snapshot, seq_end};
        let frozen = CachingDiskJournalFrozenMetadata{snapshot, seq_end};
        self.ephemeral->v.next_refines(self.ephemeral->v, cj_lbl);
        self.ephemeral->v.freeze_for_commit_image_valid(snapshot, seq_end);
        self.ephemeral->v.frozen_snapshot_valid_implies_i_metadata_valid(snapshot, seq_end);
        assert(self.ephemeral->v.frozen_metadata(snapshot) == frozen_image_metadata_i(frozen));
        assert(cj_lbl.i(self.ephemeral->v)
            == AllocationJournal::Label::FreezeForCommit{
                frozen_journal: frozen_image_metadata_i(frozen),
            });
        assert(self.ephemeral->v.i().frozen_metadata_valid(
            frozen_image_metadata_i(frozen),
        ));
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::commit_start(),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn commit_prepared_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_prepared(self, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::commit_prepared);
        let frozen = self.frozen.unwrap();
        let cj_lbl = CachingDiskJournal::Label::CommitPrepared{
            frozen: frozen.snapshot,
            seq_end: frozen.seq_end,
        };
        self.ephemeral->v.next_refines(self.ephemeral->v, cj_lbl);
        self.prepared_materialized_image_refines(frozen);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(self.i().ephemeral->v),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn commit_complete_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_complete(
                self,
                post,
                lbl,
                new_ephemeral,
            ),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::commit_complete);
        let frozen = self.frozen.unwrap();
        let meta = frozen_image_metadata_i(frozen);
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: frozen.snapshot.boundary_lsn,
            require_end: lbl.arrow_CommitComplete_require_end(),
            deallocs: lbl.arrow_CommitComplete_discarded(),
        };
        CachingDiskJournal::State::discard_old_preserves_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            frozen.snapshot.boundary_lsn,
            lbl.arrow_CommitComplete_require_end(),
            lbl.arrow_CommitComplete_discarded(),
        );
        self.ephemeral->v.discard_old_preserves_frozen_materialization_certificate_at_boundary(
            new_ephemeral,
            cj_lbl,
            frozen.snapshot,
            frozen.seq_end,
        );
        self.ephemeral->v.discard_old_preserves_clean_watermark_records_bounded(
            new_ephemeral,
            frozen.snapshot.boundary_lsn,
            lbl.arrow_CommitComplete_require_end(),
            lbl.arrow_CommitComplete_discarded(),
        );
        assert(cj_lbl.i(self.ephemeral->v).arrow_DiscardOld_deallocs()
            == lbl.arrow_CommitComplete_discarded());
        assert(new_ephemeral.i().frozen_image(meta)
            == self.ephemeral->v.i().frozen_image(meta));
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::commit_complete(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn crash_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::crash(self, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::crash);
        let prepared_image = if lbl.arrow_Crash_keep_in_flight() {
            CachingDiskJournalImage::materialized_from_persistent(
                self.ephemeral->v,
                self.frozen.unwrap(),
            )
        } else if self.ephemeral is Unknown {
            self.persistent->image
        } else {
            CachingDiskJournalImage::materialized_from_persistent(
                self.ephemeral->v,
                self.persistent.metadata(),
            )
        };
        if self.ephemeral is Known {
            let metadata = if lbl.arrow_Crash_keep_in_flight() {
                frozen_image_metadata_i(self.frozen.unwrap())
            } else {
                frozen_image_metadata_i(self.persistent.metadata())
            };
            let frozen = if lbl.arrow_Crash_keep_in_flight() {
                self.frozen.unwrap()
            } else {
                self.persistent.metadata()
            };
            if lbl.arrow_Crash_keep_in_flight() || self.ephemeral->v.journal.status is Some {
                Self::materialization_certificate_implies_materialized_image_refines(
                    self.ephemeral->v,
                    frozen,
                );
            } else {
                Self::unloaded_materialized_persistent_image_refines(
                    self.ephemeral->v,
                    frozen,
                );
            }
            assert(self.ephemeral->v.i().acceptable_frozen_image(metadata, prepared_image.i()));
            assert(prepared_image.i().valid_image());
            assert(prepared_image.seq_end == frozen.seq_end);
            assert(frozen_image_metadata_i(frozen).seq_end == frozen.seq_end);
            assert(prepared_image.i().tj.seq_end() == metadata.seq_end);
            prepared_image.i_valid_image_seq_end_implies_wf();
            if lbl.arrow_Crash_keep_in_flight() {
                assert(metadata == frozen_image_metadata_i(self.frozen.unwrap()));
            } else {
                assert(metadata == frozen_image_metadata_i(self.persistent.metadata()));
                assert(self.i().acceptable_persistent_image(prepared_image.i()));
            }
        } else {
            assert(!lbl.arrow_Crash_keep_in_flight());
            assert(prepared_image == self.persistent->image);
            assert(self.i().acceptable_persistent_image(prepared_image.i()));
        }
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::crash(prepared_image.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn load_index_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::load_index(self, post, lbl, new_ephemeral),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::load_index);
        let discovered_aus = lbl.arrow_LoadIndex_discovered_aus();
        let cj_lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
        CrashAwareCachingDiskJournal::State::load_index_requires_recovery_phase(
            self,
            post,
            lbl,
            new_ephemeral,
        );
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        CachingDiskJournal::State::load_index_requires_unloaded(
            self.ephemeral->v,
            new_ephemeral,
            discovered_aus,
        );
        assert(self.ephemeral->v.journal.status is None);
        assert(self.ephemeral->v.disk.addrs_clean_or_evictable(
            self.ephemeral->v.disk.cache.dom(),
        ));
        CachingDiskJournal::State::load_index_recovery_clean_cache_implies_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            discovered_aus,
        );
        self.ephemeral->v.load_index_establishes_clean_watermark_records_bounded(
            new_ephemeral,
            discovered_aus,
        );
        assert(self.ephemeral->v.frozen_loose_persistence_certificate(
            self.persistent.metadata().snapshot,
        ));
        self.ephemeral->v.load_index_promotes_frozen_loose_to_materialization_certificate(
            new_ephemeral,
            discovered_aus,
            self.persistent.metadata().snapshot,
            self.persistent.metadata().seq_end,
        );
        assert(self.frozen is None);
        let aj_lbl = cj_lbl.i(self.ephemeral->v);
        assert(self.label_i(post, lbl) is Internal);
        assert(self.label_i(post, lbl).arrow_Internal_allocs()
            .disjoint(caching_disk_journal_accessible_aus(self.ephemeral->v))) by {
            match lbl {
                CrashAwareCachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus} => {
                    assert(allocs.disjoint(caching_disk_journal_accessible_aus(self.ephemeral->v))) by {
                        reveal(CrashAwareCachingDiskJournal::State::internal_alloc);
                    }
                },
                _ => {}
            }
        }
        self.internal_allocs_disjoint_implies_fresh_label(post, lbl);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn observe_clean_aus_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::observe_clean_aus(
                self,
                post,
                lbl,
                new_ephemeral,
            ),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::observe_clean_aus);
        let aus = lbl.arrow_ObserveCleanAUs_aus();
        let cj_lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        self.ephemeral->v.observe_clean_aus_requires_loaded(new_ephemeral, aus);
        CachingDiskJournal::State::observe_clean_aus_preserves_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            aus,
        );
        self.ephemeral->v.observe_clean_aus_preserves_clean_watermark_records_bounded(
            new_ephemeral,
            aus,
        );
        self.ephemeral->v.observe_clean_aus_preserves_frozen_materialization_certificate(
            new_ephemeral,
            aus,
            self.persistent.metadata().snapshot,
            self.persistent.metadata().seq_end,
        );
        let aj_lbl = cj_lbl.i(self.ephemeral->v);
        if self.frozen is Some {
            if self.prepared {
                self.ephemeral->v.observe_clean_aus_preserves_frozen_materialization_certificate(
                    new_ephemeral,
                    aus,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            } else {
                self.ephemeral->v.observe_clean_aus_preserves_frozen_snapshot_and_prefix(
                    new_ephemeral,
                    aus,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
                new_ephemeral.frozen_snapshot_valid_implies_i_metadata_valid(
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            }
        }
        assert(self.label_i(post, lbl) is Internal);
        assert(self.label_i(post, lbl).arrow_Internal_allocs()
            .disjoint(caching_disk_journal_accessible_aus(self.ephemeral->v)));
        self.internal_allocs_disjoint_implies_fresh_label(post, lbl);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn internal_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::internal(self, post, lbl, new_ephemeral),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::internal);
        let cj_lbl = CachingDiskJournal::Label::Internal;
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        if self.ephemeral->v.journal.status is Some {
            self.ephemeral->v.internal_preserves_clean_watermark_au_page_bounds_clean(
                new_ephemeral,
            );
            self.ephemeral->v.internal_preserves_clean_watermark_records_bounded(
                new_ephemeral,
            );
            self.ephemeral->v.internal_preserves_frozen_materialization_certificate(
                new_ephemeral,
                self.persistent.metadata().snapshot,
                self.persistent.metadata().seq_end,
            );
        } else {
            CachingDiskJournal::State::internal_unloaded_preserves_cache_clean_or_evictable(
                self.ephemeral->v,
                new_ephemeral,
            );
            self.ephemeral->v.internal_unloaded_preserves_frozen_loose_persistence_certificate(
                new_ephemeral,
                self.persistent.metadata().snapshot,
                self.persistent.metadata().seq_end,
            );
            assert(new_ephemeral.journal.status is None);
        }
        if self.frozen is Some {
            if self.prepared {
                self.ephemeral->v.internal_preserves_frozen_materialization_certificate(
                    new_ephemeral,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            } else {
                self.ephemeral->v.internal_preserves_frozen_snapshot(
                    new_ephemeral,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            }
            new_ephemeral.frozen_snapshot_valid_implies_i_metadata_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            );
        }
        let aj_lbl = cj_lbl.i(self.ephemeral->v);
        assert(self.label_i(post, lbl) is Internal);
        assert(self.label_i(post, lbl).arrow_Internal_allocs()
            .disjoint(caching_disk_journal_accessible_aus(self.ephemeral->v)));
        self.internal_allocs_disjoint_implies_fresh_label(post, lbl);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn internal_alloc_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::internal_alloc(
                self,
                post,
                lbl,
                new_ephemeral,
            ),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::internal_alloc);
        let allocs = lbl.arrow_InternalAlloc_allocs();
        let deallocs = lbl.arrow_InternalAlloc_deallocs();
        let prune_aus = lbl.arrow_InternalAlloc_prune_aus();
        let cj_lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        CachingDiskJournal::State::internal_alloc_requires_loaded(
            self.ephemeral->v,
            new_ephemeral,
            allocs,
            deallocs,
            prune_aus,
        );
        CachingDiskJournal::State::internal_alloc_preserves_clean_watermark_au_page_bounds_clean(
            self.ephemeral->v,
            new_ephemeral,
            allocs,
            deallocs,
            prune_aus,
        );
        self.ephemeral->v.internal_alloc_preserves_clean_watermark_records_bounded(
            new_ephemeral,
            allocs,
            deallocs,
            prune_aus,
        );
        self.ephemeral->v.internal_alloc_preserves_frozen_materialization_certificate(
            new_ephemeral,
            allocs,
            deallocs,
            prune_aus,
            self.persistent.metadata().snapshot,
            self.persistent.metadata().seq_end,
        );
        if self.frozen is Some {
            if self.prepared {
                self.ephemeral->v.internal_alloc_preserves_frozen_materialization_certificate(
                    new_ephemeral,
                    allocs,
                    deallocs,
                    prune_aus,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            } else {
                self.ephemeral->v.internal_alloc_preserves_frozen_snapshot(
                    new_ephemeral,
                    allocs,
                    deallocs,
                    prune_aus,
                    self.frozen.unwrap().snapshot,
                    self.frozen.unwrap().seq_end,
                );
            }
            new_ephemeral.frozen_snapshot_valid_implies_i_metadata_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            );
        }
        let aj_lbl = cj_lbl.i(self.ephemeral->v);
        assert(self.label_i(post, lbl) is Internal);
        assert(self.label_i(post, lbl).arrow_Internal_allocs()
            .disjoint(caching_disk_journal_accessible_aus(self.ephemeral->v))) by {
            assert(allocs.disjoint(caching_disk_journal_accessible_aus(self.ephemeral->v)));
        }
        self.internal_allocs_disjoint_implies_fresh_label(post, lbl);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
        assert(post.semantic_inv());
        assert(post.refinement_inv());
    }

    pub proof fn next_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            CrashAwareCachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        CrashAwareCachingDiskJournal::State::inv_next(self, post, lbl);
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);
        let step = choose |step: CrashAwareCachingDiskJournal::Step| #![auto]
            CrashAwareCachingDiskJournal::State::next_by(self, post, lbl, step);
        match step {
            CrashAwareCachingDiskJournal::Step::load_ephemeral() => {
                self.load_ephemeral_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::read_for_recovery() => {
                self.read_for_recovery_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::query_end_lsn() => {
                self.query_end_lsn_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {
                self.put_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::query_lsn_persistence() => {
                self.query_lsn_persistence_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_start() => {
                self.commit_start_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_prepared() => {
                self.commit_prepared_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral) => {
                self.commit_complete_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::crash() => {
                self.crash_refines(post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) => {
                self.load_index_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::observe_clean_aus(new_ephemeral) => {
                self.observe_clean_aus_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) => {
                self.internal_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {
                self.internal_alloc_refines(post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

    pub proof fn allocation_next_refines_abstract(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
        ensures
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        self.semantic_inv_implies_i_inv();
        AllocationCrashAwareJournal::State::inv_next(self.i(), post.i(), self.label_i(post, lbl));
        post.semantic_inv_implies_i_inv();
        self.i().next_refines(post.i(), self.label_i(post, lbl));
    }

    pub proof fn next_refines_abstract(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.refinement_inv(),
            CrashAwareCachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.refinement_inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        self.next_refines(post, lbl);
        self.allocation_next_refines_abstract(post, lbl);
    }

    pub proof fn init_refines(self)
        requires
            CrashAwareCachingDiskJournal::State::initialize(self),
        ensures
            self.refinement_inv(),
            AllocationCrashAwareJournal::State::initialize(self.i()),
    {
        CrashAwareCachingDiskJournal::State::initialize_inductive(self);
        JournalImage::empty_is_valid_image();
        assert(self.persistent is Image);
        assert(self.persistent->image == CachingDiskJournalImage::empty());
        assert(self.persistent->image.i() == JournalImage::empty());
        assert(self.persistent->image.wf());
        assert(self.semantic_inv());
        assert(self.refinement_inv());
        assert(AllocationCrashAwareJournal::State::initialize(self.i())) by {
            reveal(AllocationCrashAwareJournal::State::initialize);
        }
    }

    pub proof fn init_refines_abstract(self)
        requires
            CrashAwareCachingDiskJournal::State::initialize(self),
        ensures
            AbstractCrashAwareJournal::State::initialize(self.i_abstract()),
    {
        self.init_refines();
        self.i().init_refines();
    }
}

} // verus!
