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
    CachingDiskJournal, cj_lsn_au_index,
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
            persistent: frozen_image_metadata_i(self.persistent),
            persistent_image: if self.ephemeral is Unknown {
                Option::Some(self.persistent_image.unwrap().i())
            } else {
                Option::None
            },
            ephemeral: self.ephemeral.i(),
            frozen: option_frozen_metadata_i(self.frozen),
        }
    }

    pub open spec fn semantic_inv(self) -> bool {
        &&& self.persistent_image is Some ==> self.persistent_image.unwrap().wf()
        &&& self.ephemeral is Known ==> self.ephemeral->v.refinement_inv()
        &&& self.ephemeral is Known ==>
            self.ephemeral->v.i().frozen_metadata_valid(frozen_image_metadata_i(self.persistent))
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
        let persistent_meta = frozen_image_metadata_i(self.persistent);
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

    pub proof fn active_step_preserves_image_refines(
        self,
        new_ephemeral: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenImage,
    )
        requires
            self.refinement_inv(),
            self.ephemeral is Known,
            new_ephemeral.refinement_inv(),
            self.ephemeral->v.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end),
            self.ephemeral->v.frozen_snapshot_preserved_by(
                new_ephemeral,
                frozen.snapshot,
                frozen.seq_end,
            ),
        ensures
            new_ephemeral.i().frozen_metadata_valid(frozen_image_metadata_i(frozen)),
            new_ephemeral.i().frozen_image(frozen_image_metadata_i(frozen))
                == self.ephemeral->v.i().frozen_image(frozen_image_metadata_i(frozen)),
    {
        let meta = frozen_image_metadata_i(frozen);
        new_ephemeral.frozen_snapshot_valid_implies_i_metadata_valid(
            frozen.snapshot,
            frozen.seq_end,
        );
        new_ephemeral.frozen_tj_matches_i_frozen_tj(frozen.snapshot, frozen.seq_end);
        self.ephemeral->v.frozen_tj_matches_i_frozen_tj(frozen.snapshot, frozen.seq_end);
        assert(new_ephemeral.i().frozen_tj(meta) == new_ephemeral.frozen_tj(frozen.snapshot));
        assert(self.ephemeral->v.i().frozen_tj(meta) == self.ephemeral->v.frozen_tj(frozen.snapshot));
        assert(new_ephemeral.frozen_tj(frozen.snapshot)
            == self.ephemeral->v.frozen_tj(frozen.snapshot));
        assert(new_ephemeral.i().frozen_image(meta)
            == self.ephemeral->v.i().frozen_image(meta));
    }

    pub proof fn concrete_materialized_frozen_image_refines(
        self,
        frozen: CachingDiskJournalFrozenImage,
        image: CachingDiskJournalImage,
    )
        requires
            self.refinement_inv(),
            self.ephemeral is Known,
            concrete_materialized_frozen_image(self.ephemeral->v, frozen, image),
        ensures
            self.ephemeral->v.i().acceptable_frozen_image(
                frozen_image_metadata_i(frozen),
                image.i(),
            ),
    {
        let state = self.ephemeral->v;
        let meta = frozen_image_metadata_i(frozen);
        let concrete_prefix = state.frozen_prefix_domain(frozen.snapshot);
        let allocation_prefix = state.i().frozen_prefix_domain(meta);

        state.frozen_tj_matches_i_frozen_tj(frozen.snapshot, frozen.seq_end);
        state.frozen_prefix_domain_matches_i(frozen.snapshot, frozen.seq_end);
        state.persistent_visible_eq_on_clean_or_evictable(concrete_prefix);

        assert(image.i().valid_image());
        assert(image.i().first == meta.first);
        assert(image.i().tj.freshest_rec == meta.freshest_rec);
        assert(image.i().tj.disk_view.boundary_lsn == meta.boundary_lsn);
        assert(image.i().tj.seq_end() == meta.seq_end);
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
                        assert(state.disk.persistent.contains_key(addr));
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
        let image = self.persistent_image.unwrap();
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
        let frozen = CachingDiskJournalFrozenImage{snapshot, seq_end};
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
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: frozen.snapshot.boundary_lsn,
            require_end: lbl.arrow_CommitComplete_require_end(),
        };
        let meta = frozen_image_metadata_i(frozen);
        self.ephemeral->v.discard_old_next_preserves_i_frozen_metadata_at_boundary(
            new_ephemeral,
            cj_lbl,
            meta,
        );
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
            self.persistent_image.unwrap()
        } else {
            CachingDiskJournalImage::materialized_from_persistent(
                self.ephemeral->v,
                self.persistent,
            )
        };
        if self.ephemeral is Known {
            let metadata = if lbl.arrow_Crash_keep_in_flight() {
                self.frozen.unwrap().metadata()
            } else {
                self.persistent.metadata()
            };
            let frozen = if lbl.arrow_Crash_keep_in_flight() {
                self.frozen.unwrap()
            } else {
                self.persistent
            };
            self.concrete_materialized_frozen_image_refines(frozen, prepared_image);
            assert(self.ephemeral->v.i().acceptable_frozen_image(metadata, prepared_image.i()));
            if lbl.arrow_Crash_keep_in_flight() {
                assert(metadata == frozen_image_metadata_i(self.frozen.unwrap()));
            } else {
                assert(metadata == frozen_image_metadata_i(self.persistent));
                assert(self.i().acceptable_persistent_image(prepared_image.i()));
            }
        } else {
            assert(!lbl.arrow_Crash_keep_in_flight());
            assert(prepared_image == self.persistent_image.unwrap());
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
            CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) |
            CrashAwareCachingDiskJournal::Step::observe_clean_aus(new_ephemeral) |
            CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) |
            CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {
                let cj_lbl = match lbl {
                    CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus} =>
                        CachingDiskJournal::Label::LoadIndex{discovered_aus},
                    CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus} =>
                        CachingDiskJournal::Label::ObserveCleanAUs{aus},
                    CrashAwareCachingDiskJournal::Label::Internal =>
                        CachingDiskJournal::Label::Internal,
                    CrashAwareCachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus} =>
                        CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
                    _ => {
                        assert(false);
                        arbitrary()
                    },
                };
                self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
                assert(self.active_step_preserves_images(new_ephemeral));
                let aj_lbl = cj_lbl.i(self.ephemeral->v);
                let persistent_meta = frozen_image_metadata_i(self.persistent);
                AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
                    self.ephemeral->v.i(),
                    new_ephemeral.i(),
                    aj_lbl,
                    persistent_meta,
                );
                if self.frozen is Some {
                    AllocationJournal::State::internal_allocations_preserves_frozen_metadata_tight(
                        self.ephemeral->v.i(),
                        new_ephemeral.i(),
                        aj_lbl,
                        frozen_image_metadata_i(self.frozen.unwrap()),
                    );
                    self.active_step_preserves_image_refines(new_ephemeral, self.frozen.unwrap());
                }
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
        assert(self.persistent == CachingDiskJournalImage::empty().metadata());
        assert(self.persistent_image is Some);
        assert(self.persistent_image.unwrap() == CachingDiskJournalImage::empty());
        assert(self.persistent_image.unwrap().i() == JournalImage::empty());
        assert(self.persistent_image.unwrap().wf());
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
