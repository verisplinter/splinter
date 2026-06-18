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
    AllocationJournal, JournalMetadata, JournalImage, maps_agree_on,
};
use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::CachingDiskRawPage as RawPage;
use crate::implementation::CachingDiskJournal_v::{
    CachingDiskJournal, cj_lsn_au_index, snapshot_tight_image_restrict_domain_same,
    snapshot_tight_tj, snapshot_tight_tj_matches_path_build_tight,
};
use crate::implementation::CachingDiskJournalRefinement_v::*;
use crate::implementation::CrashAwareCachingDiskJournal_v::*;
use crate::implementation::JournalTypes_v::to_journal_records;
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

pub open spec fn frozen_image_metadata_i(frozen: CachingDiskJournalFrozenImage)
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
    frozen: Option<CachingDiskJournalFrozenImage>,
) -> Option<JournalMetadata> {
    if frozen is None {
        Option::None
    } else {
        Option::Some(frozen_image_metadata_i(frozen.unwrap()))
    }
}

impl CrashAwareCachingDiskJournal::State {
    pub open spec fn i(self) -> AllocationCrashAwareJournal::State {
        AllocationCrashAwareJournal::State{
            persistent: self.persistent.i(),
            ephemeral: self.ephemeral.i(),
            frozen: option_frozen_metadata_i(self.frozen),
        }
    }

    pub open spec fn semantic_inv(self) -> bool {
        &&& self.persistent.wf()
        &&& self.ephemeral is Known ==> self.ephemeral->v.refinement_inv()
        &&& self.frozen is Some && self.ephemeral is Known ==>
            self.ephemeral->v.i().frozen_metadata_valid(
                frozen_image_metadata_i(self.frozen.unwrap()),
            )
        &&& self.frozen is Some && self.ephemeral is Known ==>
            self.ephemeral->v.frozen_snapshot_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            )
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
        self.label_i(post, lbl).i()
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
        let loaded = CachingDiskJournal::State::load_from_persistent(
            self.persistent.snapshot,
            self.persistent.live_persistent(),
        );
        let disk = CachingDiskJournal::State::disk_from_persistent(
            self.persistent.live_persistent(),
        );
        assert(post.ephemeral == EphemeralCachingDiskJournal::Known{v: loaded});
        assert(loaded.disk == disk);

        // The native load uses the image's stable tight backing domain.
        let full_records = to_journal_records(self.persistent.persistent);
        let live_domain = self.persistent.live_persistent_domain();
        assert(loaded.raw_visible_records() == full_records.restrict(live_domain)) by {
            assert_maps_equal!(
                loaded.raw_visible_records(),
                full_records.restrict(live_domain),
                addr => {
                    if loaded.raw_visible_records().contains_key(addr) {
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(self.persistent.live_persistent().contains_key(addr));
                        assert(self.persistent.persistent.contains_key(addr));
                        assert(live_domain.contains(addr));
                        assert(loaded.disk.visible()[addr] == self.persistent.live_persistent()[addr]);
                        assert(self.persistent.live_persistent()[addr]
                            == self.persistent.persistent[addr]);
                    }
                    if full_records.restrict(live_domain).contains_key(addr) {
                        assert(full_records.contains_key(addr));
                        assert(self.persistent.persistent.contains_key(addr));
                        assert(live_domain.contains(addr));
                        assert(self.persistent.live_persistent().contains_key(addr));
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(loaded.disk.visible()[addr] == self.persistent.live_persistent()[addr]);
                    }
                }
            );
        }
        assert(to_journal_records(self.persistent.live_persistent())
            == full_records.restrict(live_domain)) by {
            assert_maps_equal!(
                to_journal_records(self.persistent.live_persistent()),
                full_records.restrict(live_domain),
                addr => {
                    if to_journal_records(self.persistent.live_persistent()).contains_key(addr) {
                        assert(self.persistent.live_persistent().contains_key(addr));
                        assert(self.persistent.persistent.contains_key(addr));
                        assert(live_domain.contains(addr));
                        assert(self.persistent.live_persistent()[addr]
                            == self.persistent.persistent[addr]);
                    }
                    if full_records.restrict(live_domain).contains_key(addr) {
                        assert(full_records.contains_key(addr));
                        assert(self.persistent.persistent.contains_key(addr));
                        assert(live_domain.contains(addr));
                        assert(self.persistent.live_persistent().contains_key(addr));
                    }
                }
            );
        }
        assert(self.persistent.i().tj.disk_view.entries == full_records.restrict(live_domain)) by {
            assert(self.persistent.i().tj.disk_view.entries
                == to_journal_records(self.persistent.live_persistent()));
        }
        assert(loaded.journal_backing_tj() == self.persistent.i().tj);
        assert(loaded.backing_journal_image() == self.persistent.i());
        assert(self.persistent.i().tj.disk_view == loaded.journal_backing_disk_view());
        assert(self.persistent.i().tj.freshest_rec == self.persistent.snapshot.freshest_rec());
        assert(self.persistent.i().first == self.persistent.snapshot.first());
        let load_base = CachingDiskJournal::State{
            journal: CachedJournal::State{
                snapshot: self.persistent.snapshot,
                status: Option::None,
            },
            disk: loaded.disk,
            mini_allocator: crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty(),
            au_page_bounds: Map::empty(),
        };
        let loaded_bounds = load_base.journal_backing_disk_view().path_build_au_page_bounds_au_walk(
            self.persistent.snapshot.freshest_rec(),
            self.persistent.snapshot.first(),
        );
        let image_bounds = self.persistent.i().tj.disk_view.path_build_au_page_bounds_au_walk(
            self.persistent.i().tj.freshest_rec,
            self.persistent.i().first,
        );
        assert(loaded.au_page_bounds == loaded_bounds);
        assert(load_base.journal_backing_disk_view() == loaded.journal_backing_disk_view());
        assert(loaded.i().au_page_bounds == loaded.au_page_bounds);
        assert(loaded_bounds == image_bounds);
        assert(loaded.i().au_page_bounds == image_bounds);

        assert(AllocationJournal::State::initialize(loaded.i(), self.persistent.i())) by {
            reveal(AllocationJournal::State::initialize);
            assert(loaded.i().freshest_rec == self.persistent.i().tj.freshest_rec);
            assert(loaded.i().unmarshalled_tail
                == MsgHistory::empty_history_at(self.persistent.i().tj.seq_end()));
            assert(loaded.i().disk_view == self.persistent.i().tj.disk_view);
            assert(loaded.i().mini_allocator == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
        }
        loaded.init_refines(self.persistent.snapshot, loaded.disk);
        assert(loaded.refinement_inv());
        assert(self.i().persistent.init_by(loaded.i()));
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
        assert(lbl.arrow_QueryLsnPersistence_sync_lsn() <= self.i().persistent.tj.seq_end()) by {
            assert(self.persistent.wf());
            assert(self.persistent.seq_end() == self.persistent.i().tj.seq_end());
        }
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
        self.ephemeral->v.next_refines(self.ephemeral->v, cj_lbl);
        self.ephemeral->v.freeze_for_commit_image_valid(snapshot, seq_end);
        assert(cj_lbl.i(self.ephemeral->v)
            == AllocationJournal::Label::FreezeForCommit{
                frozen_journal: frozen_image_metadata_i(CachingDiskJournalFrozenImage{snapshot, seq_end}),
            });
        assert(self.ephemeral->v.i().frozen_metadata_valid(
            frozen_image_metadata_i(CachingDiskJournalFrozenImage{snapshot, seq_end}),
        )) by {
            reveal(AllocationJournal::State::next);
            reveal(AllocationJournal::State::next_by);
        }
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
        prepared_image: CachingDiskJournalImage,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_complete(
                self,
                post,
                lbl,
                new_ephemeral,
                prepared_image,
            ),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::commit_complete);
        let frozen = self.frozen.unwrap();
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: prepared_image.snapshot.boundary_lsn,
            require_end: lbl.arrow_CommitComplete_require_end(),
        };
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        let meta = frozen_image_metadata_i(frozen);
        assert(self.ephemeral->v.i().acceptable_frozen_image(meta, prepared_image.i()));
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::commit_complete(new_ephemeral.i(), prepared_image.i()),
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
        prepared_image: CachingDiskJournalImage,
    )
        requires
            self.refinement_inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::crash(self, post, lbl, prepared_image),
        ensures
            post.refinement_inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        reveal(CrashAwareCachingDiskJournal::State::crash);
        if lbl.arrow_Crash_keep_in_flight() {
            let meta = frozen_image_metadata_i(self.frozen.unwrap());
            assert(self.ephemeral->v.i().acceptable_frozen_image(meta, prepared_image.i()));
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
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral, prepared_image) => {
                self.commit_complete_refines(post, lbl, new_ephemeral, prepared_image);
            },
            CrashAwareCachingDiskJournal::Step::crash(prepared_image) => {
                self.crash_refines(post, lbl, prepared_image);
            },
            CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) |
            CrashAwareCachingDiskJournal::Step::observe_clean_aus(new_ephemeral) |
            CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) |
            CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {
                // These cases need the allocation-internal frozen-preservation bridge.
                assert(false);
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
        assert(self.persistent == CachingDiskJournalImage::empty());
        assert(self.persistent.i() == JournalImage::empty());
        assert(self.persistent.wf());
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
