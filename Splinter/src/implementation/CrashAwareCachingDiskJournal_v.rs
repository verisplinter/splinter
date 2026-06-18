// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Crash-aware wrapper for CachingDiskJournal.

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::map::*;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::{
    JournalImage, JournalMetadata, LsnAUIndex, lsn_au_index_discard_up_to,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus};
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::{addresses_in_aus, CachingDisk, CachingDiskRawPage as RawPage};
use crate::implementation::CachingDiskJournal_v::{
    CachingDiskJournal, cj_lsn_au_index,
};
use crate::implementation::CachingDiskJournalRefinement_v::*;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::journal::LinkedJournalRefinement_v::*;
use crate::journal::LinkedJournal_v::*;

verus!{

#[verifier::ext_equal]
pub struct CachingDiskJournalImage {
    pub persistent: Map<Address, RawPage>,
    pub snapshot: JournalSnapshot,
    pub seq_end: LSN,
}

#[verifier::ext_equal]
pub struct CachingDiskJournalFrozenImage {
    pub snapshot: JournalSnapshot,
    pub seq_end: LSN,
}

impl CachingDiskJournalFrozenImage {
    pub open spec fn metadata(self) -> JournalMetadata {
        JournalMetadata{
            boundary_lsn: self.snapshot.boundary_lsn,
            seq_end: self.seq_end,
            freshest_rec: self.snapshot.freshest_rec(),
            first: self.snapshot.first(),
        }
    }
}

pub open spec fn concrete_materialized_frozen_image(
    state: CachingDiskJournal::State,
    frozen: CachingDiskJournalFrozenImage,
    image: CachingDiskJournalImage,
) -> bool
{
    &&& image.wf()
    &&& state.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end)
    &&& image.snapshot == frozen.snapshot
    &&& image.seq_end == frozen.seq_end
    &&& image.persistent == state.disk.persistent.restrict(
        state.frozen_loose_domain(frozen.snapshot),
    )
    &&& state.disk.addrs_clean_or_evictable(state.frozen_prefix_domain(frozen.snapshot))
    &&& CachingDiskJournal::State::next(
        state,
        state,
        CachingDiskJournal::Label::CommitPrepared{
            frozen: frozen.snapshot,
            seq_end: frozen.seq_end,
        },
    )
}

impl CachingDiskJournalImage {
    pub open spec fn empty() -> Self {
        Self{
            persistent: Map::empty(),
            snapshot: JournalSnapshot{boundary_lsn: 0, root: None},
            seq_end: 0,
        }
    }

    pub open spec fn materialized_from_persistent(
        state: CachingDiskJournal::State,
        frozen: CachingDiskJournalFrozenImage,
    ) -> Self {
        Self{
            persistent: state.disk.persistent.restrict(
                state.frozen_loose_domain(frozen.snapshot),
            ),
            snapshot: frozen.snapshot,
            seq_end: frozen.seq_end,
        }
    }

    pub open spec fn metadata(self) -> CachingDiskJournalFrozenImage {
        CachingDiskJournalFrozenImage{
            snapshot: self.snapshot,
            seq_end: self.seq_end,
        }
    }

    pub open spec fn stable_tj(self) -> TruncatedJournal {
        let dv = DiskView{
            boundary_lsn: self.snapshot.boundary_lsn,
            entries: to_journal_records(self.persistent),
        };
        TruncatedJournal{
            freshest_rec: self.snapshot.freshest_rec(),
            disk_view: dv.path_build_tight(self.snapshot.freshest_rec()),
        }
    }

    pub open spec fn tj(self) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: self.snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: self.snapshot.boundary_lsn,
                entries: to_journal_records(self.persistent),
            },
        }
    }

    pub open spec fn tight_tj(self) -> TruncatedJournal {
        self.tj().build_tight()
    }

    pub open spec fn i(self) -> JournalImage {
        JournalImage{tj: self.tj(), first: self.snapshot.first()}
    }

    pub open spec fn seq_end(self) -> LSN {
        self.seq_end
    }

    pub open spec fn valid_image(self) -> bool {
        &&& self.i().valid_image()
        &&& self.stable_tj().disk_view.entries <= to_journal_records(self.persistent)
        &&& self.seq_end == self.i().tj.seq_end()
    }

    pub open spec fn wf(self) -> bool {
        self.valid_image()
    }

    pub open spec fn accessible_aus(self) -> Set<AU> {
        to_aus(self.persistent.dom())
    }
}

pub open spec fn caching_disk_journal_accessible_aus(state: CachingDiskJournal::State) -> Set<AU> {
    state.accessible_aus()
}

pub enum EphemeralCachingDiskJournal {
    Unknown,
    Known{v: CachingDiskJournal::State},
}

state_machine!{ CrashAwareCachingDiskJournal {
    fields {
        pub persistent: CachingDiskJournalFrozenImage,
        pub persistent_image: Option<CachingDiskJournalImage>,
        pub ephemeral: EphemeralCachingDiskJournal,
        pub frozen: Option<CachingDiskJournalFrozenImage>,
        pub prepared: bool,
    }

    pub enum Label {
        LoadEphemeral,
        ReadForRecovery{records: MsgHistory},
        QueryEndLsn{end_lsn: LSN},
        Put{records: MsgHistory},
        LoadIndex{discovered_aus: Set<AU>},
        ObserveCleanAUs{aus: Set<AU>},
        CommitPrepared,
        Internal,
        InternalAlloc{allocs: Set<AU>, deallocs: Set<AU>, prune_aus: Set<AU>},
        QueryLsnPersistence{sync_lsn: LSN},
        CommitStart{new_boundary_lsn: LSN, snapshot: JournalSnapshot, seq_end: LSN},
        CommitComplete{require_end: LSN, discarded: Set<AU>},
        Crash{keep_in_flight: bool},
    }

    pub open spec fn active_step_preserves_images(self, new_ephemeral: CachingDiskJournal::State) -> bool
        recommends self.ephemeral is Known
    {
        let persistent = self.persistent;
        &&& self.ephemeral->v.frozen_snapshot_valid(
            persistent.snapshot,
            persistent.seq_end,
        )
        &&& self.ephemeral->v.frozen_snapshot_preserved_by(
            new_ephemeral,
            persistent.snapshot,
            persistent.seq_end,
        )
        &&& self.frozen is Some ==> {
            &&& self.ephemeral->v.frozen_snapshot_valid(
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            )
            &&& self.ephemeral->v.frozen_snapshot_preserved_by(
                new_ephemeral,
                self.frozen.unwrap().snapshot,
                self.frozen.unwrap().seq_end,
            )
        }
    }

    init!{ initialize() {
        init persistent = CachingDiskJournalImage::empty().metadata();
        init persistent_image = Option::Some(CachingDiskJournalImage::empty());
        init ephemeral = EphemeralCachingDiskJournal::Unknown;
        init frozen = Option::None;
        init prepared = false;
    }}

    transition!{ load_ephemeral(lbl: Label) {
        require lbl is LoadEphemeral;
        require pre.ephemeral is Unknown;
        require pre.persistent_image is Some;

        update ephemeral = EphemeralCachingDiskJournal::Known{
            v: CachingDiskJournal::State::load_from_persistent(
                pre.persistent_image.unwrap().snapshot,
                pre.persistent_image.unwrap().persistent,
            ),
        };
        update persistent_image = Option::None;
    }}

    transition!{ read_for_recovery(lbl: Label) {
        require let Label::ReadForRecovery{records} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::ReadForRecovery{messages: records},
        );
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require let Label::QueryEndLsn{end_lsn} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::QueryEndLsn{end_lsn},
        );
    }}

    transition!{ put(lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        require let Label::Put{records} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::Put{messages: records},
        );

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ load_index(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require let Label::LoadIndex{discovered_aus} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::LoadIndex{discovered_aus},
        );
        require pre.active_step_preserves_images(new_ephemeral);

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ observe_clean_aus(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require let Label::ObserveCleanAUs{aus} = lbl;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::ObserveCleanAUs{aus},
        );
        require pre.active_step_preserves_images(new_ephemeral);

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ internal(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require lbl is Internal;
        require pre.ephemeral is Known;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::Internal,
        );
        require pre.active_step_preserves_images(new_ephemeral);

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ internal_alloc(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require let Label::InternalAlloc{allocs, deallocs, prune_aus} = lbl;
        require pre.ephemeral is Known;
        require allocs.disjoint(caching_disk_journal_accessible_aus(pre.ephemeral->v));
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus},
        );
        require pre.active_step_preserves_images(new_ephemeral);

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ query_lsn_persistence(lbl: Label) {
        require let Label::QueryLsnPersistence{sync_lsn} = lbl;
        require sync_lsn <= pre.persistent.seq_end;
    }}

    transition!{ commit_prepared(lbl: Label) {
        require lbl is CommitPrepared;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require !pre.prepared;
        let frozen = pre.frozen.unwrap();
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::CommitPrepared{
                frozen: frozen.snapshot,
                seq_end: frozen.seq_end,
            },
        );

        update prepared = true;
    }}

    transition!{ commit_start(lbl: Label) {
        require let Label::CommitStart{new_boundary_lsn, snapshot, seq_end} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is None;
        require snapshot.boundary_lsn == new_boundary_lsn;
        require pre.persistent.seq_end <= new_boundary_lsn;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::FreezeForCommit{
                frozen: snapshot,
                seq_end,
            },
        );

        update frozen = Option::Some(CachingDiskJournalFrozenImage{snapshot, seq_end});
    }}

    transition!{ commit_complete(
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        require let Label::CommitComplete{require_end, discarded} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require pre.prepared;
        let frozen_image = pre.frozen.unwrap();
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::CommitPrepared{
                frozen: frozen_image.snapshot,
                seq_end: frozen_image.seq_end,
            },
        );
        let old_au_index = cj_lsn_au_index(pre.ephemeral->v.journal);
        let new_au_index = lsn_au_index_discard_up_to(
            old_au_index,
            frozen_image.snapshot.boundary_lsn,
        );
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::DiscardOld{
                start_lsn: frozen_image.snapshot.boundary_lsn,
                require_end,
            },
        );
        require discarded == old_au_index.values().difference(new_au_index.values());

        update persistent = frozen_image;
        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
        update frozen = Option::None;
        update prepared = false;
    }}

    transition!{ crash(lbl: Label) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.frozen is Some;
        require keep_in_flight ==> pre.prepared;
        require keep_in_flight ==> pre.ephemeral is Known;
        require !keep_in_flight && pre.ephemeral is Unknown ==> pre.persistent_image is Some;
        let prepared_image = if keep_in_flight {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.frozen.unwrap(),
            )
        } else if pre.ephemeral is Unknown {
            pre.persistent_image.unwrap()
        } else {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.persistent,
            )
        };
        require prepared_image.wf();
        require keep_in_flight ==> concrete_materialized_frozen_image(
            pre.ephemeral->v,
            pre.frozen.unwrap(),
            prepared_image,
        );
        require !keep_in_flight && pre.ephemeral is Unknown ==> {
            &&& pre.persistent_image is Some
            &&& prepared_image == pre.persistent_image.unwrap()
        };
        require !keep_in_flight && pre.ephemeral is Known ==> {
            concrete_materialized_frozen_image(
                pre.ephemeral->v,
                pre.persistent,
                prepared_image,
            )
        };

        update persistent = if keep_in_flight {
            prepared_image.metadata()
        } else {
            pre.persistent
        };
        update persistent_image = Option::Some(prepared_image);
        update ephemeral = EphemeralCachingDiskJournal::Unknown;
        update frozen = Option::None;
        update prepared = false;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.frozen is None && !self.prepared
        &&& self.ephemeral is Unknown <==> self.persistent_image is Some
        &&& self.persistent_image is Some ==> {
            &&& self.persistent_image.unwrap().metadata() == self.persistent
            &&& self.persistent_image.unwrap().wf()
        }
        &&& self.ephemeral is Known ==> self.ephemeral->v.inv()
        &&& self.frozen is Some && self.ephemeral is Known ==> self.ephemeral->v.journal.status is Some
        &&& self.prepared ==> self.frozen is Some
        &&& self.prepared ==> self.ephemeral is Known
        &&& self.prepared && self.ephemeral is Known ==> self.ephemeral->v.journal.status is Some
        &&& self.prepared && self.ephemeral is Known && self.frozen is Some ==>
            self.frozen.unwrap().snapshot.freshest_rec() is Some ==>
                self.frozen.unwrap().seq_end <= self.ephemeral->v.journal.clean_watermark()
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self) {
        JournalImage::empty_is_valid_image();
        TruncatedJournal::mkfs_ensures();
        assert(post.persistent_image is Some);
        assert(post.persistent_image.unwrap() == CachingDiskJournalImage::empty());
        assert(post.persistent_image.unwrap().i() == JournalImage::empty());
        assert(post.persistent_image.unwrap().tj() == TruncatedJournal::mkfs());
        assert(post.persistent_image.unwrap().wf());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label) {
        let image = pre.persistent_image.unwrap();
        let loaded = CachingDiskJournal::State::load_from_persistent(
            image.snapshot,
            image.persistent,
        );
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == loaded);
        assert(loaded.disk.visible() =~= image.persistent) by {
            assert forall |addr: Address| #[trigger] loaded.disk.visible().contains_key(addr)
                implies image.persistent.contains_key(addr) by {
                assert(loaded.disk.cache == Map::<Address, RawPage>::empty());
            }
            assert forall |addr: Address| #[trigger] image.persistent.contains_key(addr)
                implies loaded.disk.visible().contains_key(addr) by {
                assert(loaded.disk.persistent.contains_key(addr));
            }
        }
        assert(loaded.journal_disk_view().entries.dom() =~= image.persistent.dom()) by {
            assert forall |addr: Address| #[trigger] loaded.journal_disk_view().entries.dom().contains(addr)
                implies image.persistent.dom().contains(addr) by {
                assert(loaded.journal_disk_view().entries.contains_key(addr));
                assert(loaded.disk.visible().contains_key(addr));
            }
            assert forall |addr: Address| #[trigger] image.persistent.dom().contains(addr)
                implies loaded.journal_disk_view().entries.dom().contains(addr) by {
                assert(image.persistent.contains_key(addr));
                assert(loaded.disk.visible().contains_key(addr));
                assert(loaded.journal_disk_view().entries.contains_key(addr));
            }
        }
        let snapshot = image.snapshot;
        let full_records = to_journal_records(image.persistent);
        let live_domain = image.persistent.dom();
        assert(loaded.journal_disk_view().entries == full_records.restrict(live_domain)) by {
            assert_maps_equal!(
                loaded.journal_disk_view().entries,
                full_records.restrict(live_domain),
                addr => {
                    if loaded.journal_disk_view().entries.contains_key(addr) {
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(image.persistent.contains_key(addr));
                        assert(live_domain.contains(addr));
                        assert(loaded.disk.visible()[addr] == image.persistent[addr]);
                    }
                    if full_records.restrict(live_domain).contains_key(addr) {
                        assert(full_records.contains_key(addr));
                        assert(image.persistent.contains_key(addr));
                        assert(live_domain.contains(addr));
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(loaded.disk.visible()[addr] == image.persistent[addr]);
                    }
                }
            );
        }
        assert(loaded.journal_tj()
            == TruncatedJournal{
                freshest_rec: snapshot.freshest_rec(),
                disk_view: (DiskView{
                    boundary_lsn: snapshot.boundary_lsn,
                    entries: loaded.journal_disk_view().entries,
                }).path_build_tight(snapshot.freshest_rec()),
            });
        assert(loaded.journal.wf());
        assert(loaded.disk.inv());
        assert(loaded.mini_allocator.wf());
        assert(loaded.inv());
    }

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::Put{messages: lbl.arrow_Put_records()};
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        if pre.frozen is Some {
            CachingDiskJournal::State::put_loaded_status_and_clean_watermark_unchanged(
                pre.ephemeral->v,
                new_ephemeral,
                lbl.arrow_Put_records(),
            );
        }
        if pre.prepared && pre.frozen is Some && pre.frozen.unwrap().snapshot.freshest_rec() is Some {
            assert(pre.frozen.unwrap().seq_end <= pre.ephemeral->v.journal.clean_watermark());
            assert(new_ephemeral.journal.clean_watermark() == pre.ephemeral->v.journal.clean_watermark());
        }
    }

    #[inductive(load_index)]
    fn load_index_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::LoadIndex{
            discovered_aus: lbl.arrow_LoadIndex_discovered_aus(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        CachingDiskJournal::State::load_index_visible_unchanged(
            pre.ephemeral->v,
            new_ephemeral,
            lbl.arrow_LoadIndex_discovered_aus(),
        );
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
        if pre.frozen is Some {
            assert(pre.active_step_preserves_images(new_ephemeral));
            assert(new_ephemeral.frozen_snapshot_valid(
                pre.frozen.unwrap().snapshot,
                pre.frozen.unwrap().seq_end,
            ));
        }
        if pre.prepared {
            CachingDiskJournal::State::load_index_requires_unloaded(
                pre.ephemeral->v,
                new_ephemeral,
                lbl.arrow_LoadIndex_discovered_aus(),
            );
            assert(false);
        }
    }

    #[inductive(observe_clean_aus)]
    fn observe_clean_aus_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::ObserveCleanAUs{
            aus: lbl.arrow_ObserveCleanAUs_aus(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        CachingDiskJournal::State::observe_clean_aus_visible_unchanged(
            pre.ephemeral->v,
            new_ephemeral,
            lbl.arrow_ObserveCleanAUs_aus(),
        );
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
        if pre.frozen is Some {
            assert(pre.active_step_preserves_images(new_ephemeral));
            assert(new_ephemeral.frozen_snapshot_valid(
                pre.frozen.unwrap().snapshot,
                pre.frozen.unwrap().seq_end,
            ));
        }
        if pre.prepared && pre.frozen is Some
            && pre.frozen.unwrap().snapshot.freshest_rec() is Some {
            CachingDiskJournal::State::observe_clean_aus_loaded_status_and_clean_watermark_monotonic(
                pre.ephemeral->v,
                new_ephemeral,
                lbl.arrow_ObserveCleanAUs_aus(),
            );
            assert(pre.frozen.unwrap().seq_end
                <= pre.ephemeral->v.journal.clean_watermark());
            assert(pre.ephemeral->v.journal.clean_watermark()
                <= new_ephemeral.journal.clean_watermark());
        }
    }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        assert(CrashAwareCachingDiskJournal::State::internal(pre, post, lbl, new_ephemeral));
        assert(post.ephemeral == EphemeralCachingDiskJournal::Known{v: new_ephemeral});
        assert(post.frozen == pre.frozen);
        let cj_lbl = CachingDiskJournal::Label::Internal;
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        if pre.frozen is Some {
            assert(pre.active_step_preserves_images(new_ephemeral));
            assert(new_ephemeral.frozen_snapshot_valid(
                pre.frozen.unwrap().snapshot,
                pre.frozen.unwrap().seq_end,
            ));
            if pre.prepared {
                let frozen = pre.frozen.unwrap();
                CachingDiskJournal::State::internal_loaded_status_and_clean_watermark_monotonic(
                    pre.ephemeral->v,
                    new_ephemeral,
                );
                if frozen.snapshot.freshest_rec() is Some {
                    assert(frozen.seq_end <= pre.ephemeral->v.journal.clean_watermark());
                    assert(pre.ephemeral->v.journal.clean_watermark()
                        <= new_ephemeral.journal.clean_watermark());
                }
                assert(post.frozen.unwrap() == frozen);
                assert(post.ephemeral->v == new_ephemeral);
            }
        }
    }

    #[inductive(internal_alloc)]
    fn internal_alloc_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::InternalAlloc{
            allocs: lbl.arrow_InternalAlloc_allocs(),
            deallocs: lbl.arrow_InternalAlloc_deallocs(),
            prune_aus: lbl.arrow_InternalAlloc_prune_aus(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        CachingDiskJournal::State::internal_alloc_preserves_journal(
            pre.ephemeral->v,
            new_ephemeral,
            lbl.arrow_InternalAlloc_allocs(),
            lbl.arrow_InternalAlloc_deallocs(),
            lbl.arrow_InternalAlloc_prune_aus(),
        );
        assert(new_ephemeral.journal == pre.ephemeral->v.journal);
        if pre.prepared && pre.frozen is Some && pre.frozen.unwrap().snapshot.freshest_rec() is Some {
            assert(new_ephemeral.journal.clean_watermark()
                == pre.ephemeral->v.journal.clean_watermark());
        }
    }

    #[inductive(query_lsn_persistence)]
    fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label) {
        let frozen_image = CachingDiskJournalFrozenImage{
            snapshot: lbl.arrow_CommitStart_snapshot(),
            seq_end: lbl.arrow_CommitStart_seq_end(),
        };
        let cj_lbl = CachingDiskJournal::Label::FreezeForCommit{
            frozen: frozen_image.snapshot,
            seq_end: frozen_image.seq_end,
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, pre.ephemeral->v, cj_lbl);
        pre.ephemeral->v.freeze_for_commit_image_valid(
            frozen_image.snapshot,
            frozen_image.seq_end,
        );
        assert(frozen_image.seq_end == pre.ephemeral->v.frozen_seq_end(frozen_image.snapshot));
    }

    #[inductive(commit_prepared)]
    fn commit_prepared_inductive(pre: Self, post: Self, lbl: Label) {
        let frozen = pre.frozen.unwrap();
        let cj_lbl = CachingDiskJournal::Label::CommitPrepared{
            frozen: frozen.snapshot,
            seq_end: frozen.seq_end,
        };
        assert(CrashAwareCachingDiskJournal::State::commit_prepared(pre, post, lbl));
        assert(CachingDiskJournal::State::next(pre.ephemeral->v, pre.ephemeral->v, cj_lbl));
        assert(post.persistent == pre.persistent);
        assert(post.ephemeral == pre.ephemeral);
        assert(post.frozen == pre.frozen);
        assert(post.prepared);
        CachingDiskJournal::State::commit_prepared_effect(
            pre.ephemeral->v,
            frozen.snapshot,
            frozen.seq_end,
        );
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    ) {
        let frozen_image = pre.frozen.unwrap();
        let frozen = pre.frozen.unwrap();
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: frozen_image.snapshot.boundary_lsn,
            require_end: lbl.arrow_CommitComplete_require_end(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) {
        let keep_in_flight = lbl.arrow_Crash_keep_in_flight();
        let prepared_image = if keep_in_flight {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.frozen.unwrap(),
            )
        } else if pre.ephemeral is Unknown {
            pre.persistent_image.unwrap()
        } else {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.persistent,
            )
        };
        if keep_in_flight {
            assert(post.persistent == prepared_image.metadata());
        } else {
            assert(post.persistent == pre.persistent);
        }
        assert(post.persistent_image == Option::Some(prepared_image));
    }

    pub proof fn inv_next(pre: Self, post: Self, lbl: Label)
        requires
            pre.inv(),
            CrashAwareCachingDiskJournal::State::next(pre, post, lbl),
        ensures
            post.inv(),
    {
        reveal(CrashAwareCachingDiskJournal::State::next);
        reveal(CrashAwareCachingDiskJournal::State::next_by);

        let step = choose |step| CrashAwareCachingDiskJournal::State::next_by(pre, post, lbl, step);
        match step {
            CrashAwareCachingDiskJournal::Step::load_ephemeral() => {
                assert(CrashAwareCachingDiskJournal::State::load_ephemeral(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::load_ephemeral_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::read_for_recovery() => {
                assert(CrashAwareCachingDiskJournal::State::read_for_recovery(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::read_for_recovery_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::query_end_lsn() => {
                assert(CrashAwareCachingDiskJournal::State::query_end_lsn(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::query_end_lsn_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::put(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::put(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::put_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::load_index(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::load_index(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::load_index_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::observe_clean_aus(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::observe_clean_aus(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::observe_clean_aus_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::internal(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::internal(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::internal_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::internal_alloc(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::internal_alloc(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::internal_alloc_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::query_lsn_persistence() => {
                assert(CrashAwareCachingDiskJournal::State::query_lsn_persistence(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::query_lsn_persistence_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_start() => {
                assert(CrashAwareCachingDiskJournal::State::commit_start(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::commit_start_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_prepared() => {
                assert(CrashAwareCachingDiskJournal::State::commit_prepared(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::commit_prepared_inductive(pre, post, lbl);
            },
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral) => {
                assert(CrashAwareCachingDiskJournal::State::commit_complete(pre, post, lbl, new_ephemeral)) by {
                }
                CrashAwareCachingDiskJournal::State::commit_complete_inductive(pre, post, lbl, new_ephemeral);
            },
            CrashAwareCachingDiskJournal::Step::crash() => {
                assert(CrashAwareCachingDiskJournal::State::crash(pre, post, lbl)) by {
                }
                CrashAwareCachingDiskJournal::State::crash_inductive(pre, post, lbl);
            },
            _ => {
                assert(post.inv());
            },
        }
    }

    pub proof fn crash_persistent_image_accessible_aus(
        pre: Self,
        post: Self,
        lbl: Label,
    )
        requires
            pre.inv(),
            CrashAwareCachingDiskJournal::State::crash(pre, post, lbl),
        ensures
            post.persistent_image is Some,
            pre.ephemeral is Known ==>
                post.persistent_image.unwrap().accessible_aus()
                    <= caching_disk_journal_accessible_aus(pre.ephemeral->v),
            pre.ephemeral is Unknown ==> post.persistent_image == pre.persistent_image,
    {
        reveal(CrashAwareCachingDiskJournal::State::crash);
        let keep_in_flight = lbl.arrow_Crash_keep_in_flight();
        let prepared_image = if keep_in_flight {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.frozen.unwrap(),
            )
        } else if pre.ephemeral is Unknown {
            pre.persistent_image.unwrap()
        } else {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.persistent,
            )
        };
        assert(post.persistent_image == Option::Some(prepared_image));
        if pre.ephemeral is Known {
            let frozen = if keep_in_flight {
                pre.frozen.unwrap()
            } else {
                pre.persistent
            };
            pre.ephemeral->v.frozen_loose_domain_persistent_aus_accessible(frozen.snapshot);
            assert(prepared_image.accessible_aus()
                <= caching_disk_journal_accessible_aus(pre.ephemeral->v));
        }
    }
}}

} // verus!
