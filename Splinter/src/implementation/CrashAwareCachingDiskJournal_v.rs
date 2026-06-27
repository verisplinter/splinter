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
    JournalImage, JournalMetadata,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus};
use crate::implementation::CachedJournal_v::*;
use crate::implementation::CachingDisk_v::{addresses_in_aus, CachingDisk, CachingDiskRawPage as RawPage};
use crate::implementation::CachingDiskJournal_v::{
    CachingDiskJournal,
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
pub struct CachingDiskJournalFrozenMetadata {
    pub snapshot: JournalSnapshot,
    pub seq_end: LSN,
}

impl CachingDiskJournalFrozenMetadata {
    pub open spec fn metadata(self) -> JournalMetadata {
        JournalMetadata{
            boundary_lsn: self.snapshot.boundary_lsn,
            seq_end: self.seq_end,
            freshest_rec: self.snapshot.freshest_rec(),
            first: self.snapshot.first(),
        }
    }
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
        frozen: CachingDiskJournalFrozenMetadata,
    ) -> Self {
        Self{
            persistent: state.disk.persistent.restrict(
                state.persistent_frozen_loose_domain(frozen),
            ),
            snapshot: frozen.snapshot,
            seq_end: frozen.seq_end,
        }
    }

    pub open spec fn metadata(self) -> CachingDiskJournalFrozenMetadata {
        CachingDiskJournalFrozenMetadata{
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

    pub proof fn i_valid_image_seq_end_implies_wf(self)
        requires
            self.i().valid_image(),
            self.seq_end == self.i().tj.seq_end(),
        ensures
            self.wf(),
    {
        let image = self.i();
        image.valid_image_implies_tight_valid_image();
        image.tj.disk_view.path_build_tight_is_sub_disk(image.tj.freshest_rec);
        assert(self.stable_tj() == image.tight_tj());
        assert(image.tj.disk_view.entries == to_journal_records(self.persistent));
        assert(self.stable_tj().disk_view.entries <= to_journal_records(self.persistent)) by {
            assert(image.tight_tj().disk_view.is_sub_disk(image.tj.disk_view));
        }
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

pub enum PersistentCachingDiskJournal {
    Metadata{meta: CachingDiskJournalFrozenMetadata},
    Image{image: CachingDiskJournalImage},
}

impl PersistentCachingDiskJournal {
    pub open spec fn metadata(self) -> CachingDiskJournalFrozenMetadata {
        match self {
            PersistentCachingDiskJournal::Metadata{meta} => meta,
            PersistentCachingDiskJournal::Image{image} => image.metadata(),
        }
    }

    pub open spec fn image(self) -> CachingDiskJournalImage
        recommends
            self is Image,
    {
        self->image
    }
}

state_machine!{ CrashAwareCachingDiskJournal {
    fields {
        pub persistent: PersistentCachingDiskJournal,
        pub ephemeral: EphemeralCachingDiskJournal,
        pub frozen: Option<CachingDiskJournalFrozenMetadata>,
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

    init!{ initialize() {
        init persistent = PersistentCachingDiskJournal::Image{
            image: CachingDiskJournalImage::empty(),
        };
        init ephemeral = EphemeralCachingDiskJournal::Unknown;
        init frozen = Option::None;
        init prepared = false;
    }}

    transition!{ load_ephemeral(lbl: Label) {
        require lbl is LoadEphemeral;
        require pre.ephemeral is Unknown;
        require pre.persistent is Image;
        let image = pre.persistent->image;

        update ephemeral = EphemeralCachingDiskJournal::Known{
            v: CachingDiskJournal::State::load_from_persistent(
                image.snapshot,
                image.persistent,
            ),
        };
        update persistent = PersistentCachingDiskJournal::Metadata{
            meta: image.metadata(),
        };
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

        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
    }}

    transition!{ query_lsn_persistence(lbl: Label) {
        require let Label::QueryLsnPersistence{sync_lsn} = lbl;
        require sync_lsn <= pre.persistent.metadata().seq_end;
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
        require pre.persistent.metadata().seq_end <= new_boundary_lsn;
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::FreezeForCommit{
                frozen: snapshot,
                seq_end,
            },
        );

        update frozen = Option::Some(CachingDiskJournalFrozenMetadata{snapshot, seq_end});
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
            new_ephemeral,
            CachingDiskJournal::Label::DiscardOld{
                start_lsn: frozen_image.snapshot.boundary_lsn,
                require_end,
                deallocs: discarded,
            },
        );

        update persistent = PersistentCachingDiskJournal::Metadata{
            meta: frozen_image,
        };
        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
        update frozen = Option::None;
        update prepared = false;
    }}

    transition!{ crash(lbl: Label) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.frozen is Some;
        require keep_in_flight ==> pre.prepared;

        let prepared_image = if keep_in_flight {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.frozen.unwrap(),
            )
        } else if pre.ephemeral is Unknown {
            pre.persistent->image
        } else {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.persistent.metadata(),
            )
        };

        update persistent = PersistentCachingDiskJournal::Image{
            image: prepared_image,
        };
        update ephemeral = EphemeralCachingDiskJournal::Unknown;
        update frozen = Option::None;
        update prepared = false;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.frozen is None && !self.prepared
        &&& self.ephemeral is Unknown <==> self.persistent is Image
        &&& self.ephemeral is Known <==> self.persistent is Metadata
        &&& self.ephemeral is Known ==> self.ephemeral->v.inv()
        &&& self.frozen is Some ==> self.ephemeral is Known
        &&& self.frozen is Some ==> self.ephemeral->v.journal.status is Some
        &&& self.prepared ==> self.frozen is Some
        &&& self.prepared && self.frozen is Some ==>
            self.frozen.unwrap().snapshot.freshest_rec() is Some ==>
                self.frozen.unwrap().seq_end <= self.ephemeral->v.journal.clean_watermark()
    }

    #[inductive(initialize)]
    pub fn initialize_inductive(post: Self) {
        JournalImage::empty_is_valid_image();
        TruncatedJournal::mkfs_ensures();
        assert(post.persistent is Image);
        assert(post.persistent->image == CachingDiskJournalImage::empty());
        assert(post.persistent->image.i() == JournalImage::empty());
        assert(post.persistent->image.tj() == TruncatedJournal::mkfs());
        assert(post.persistent->image.wf());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label) {
        let image = pre.persistent->image;
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

    pub proof fn load_index_requires_recovery_phase(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            pre.inv(),
            Self::load_index(pre, post, lbl, new_ephemeral),
        ensures
            pre.frozen is None,
            !pre.prepared,
    {
        reveal(CrashAwareCachingDiskJournal::State::load_index);
        CachingDiskJournal::State::load_index_requires_unloaded(
            pre.ephemeral->v,
            new_ephemeral,
            lbl.arrow_LoadIndex_discovered_aus(),
        );
        assert(pre.ephemeral->v.journal.status is None);
        if pre.frozen is Some {
            assert(pre.ephemeral->v.journal.status is Some);
            assert(false);
        }
        if pre.prepared {
            assert(pre.frozen is Some);
            assert(false);
        }
    }

    #[inductive(load_index)]
    fn load_index_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::LoadIndex{
            discovered_aus: lbl.arrow_LoadIndex_discovered_aus(),
        };
        Self::load_index_requires_recovery_phase(pre, post, lbl, new_ephemeral);
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        CachingDiskJournal::State::load_index_visible_unchanged(
            pre.ephemeral->v,
            new_ephemeral,
            lbl.arrow_LoadIndex_discovered_aus(),
        );
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
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
            CachingDiskJournal::State::observe_clean_aus_requires_loaded(
                pre.ephemeral->v,
                new_ephemeral,
                lbl.arrow_ObserveCleanAUs_aus(),
            );
            assert(new_ephemeral.journal.status is Some);
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
            CachingDiskJournal::State::internal_loaded_status_and_clean_watermark_monotonic(
                pre.ephemeral->v,
                new_ephemeral,
            );
            assert(new_ephemeral.journal.status is Some);
            if pre.prepared {
                let frozen = pre.frozen.unwrap();
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
        if pre.frozen is Some {
            assert(new_ephemeral.journal.status is Some);
        }
        if pre.prepared && pre.frozen is Some && pre.frozen.unwrap().snapshot.freshest_rec() is Some {
            assert(new_ephemeral.journal.clean_watermark()
                == pre.ephemeral->v.journal.clean_watermark());
        }
    }

    #[inductive(query_lsn_persistence)]
    fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label) {
        let frozen_image = CachingDiskJournalFrozenMetadata{
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
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: frozen_image.snapshot.boundary_lsn,
            require_end: lbl.arrow_CommitComplete_require_end(),
            deallocs: lbl.arrow_CommitComplete_discarded(),
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
            pre.persistent->image
        } else {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.persistent.metadata(),
            )
        };
        assert(post.persistent == PersistentCachingDiskJournal::Image{image: prepared_image});
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
            pre.ephemeral is Known ==> {
                let keep_in_flight = lbl.arrow_Crash_keep_in_flight();
                let frozen = if keep_in_flight {
                    pre.frozen.unwrap()
                } else {
                    pre.persistent.metadata()
                };
                (keep_in_flight || pre.ephemeral->v.journal.status is Some) ==>
                    CachingDiskJournalImage::materialized_from_persistent(
                    pre.ephemeral->v,
                    frozen,
                ).accessible_aus() <= caching_disk_journal_accessible_aus(pre.ephemeral->v)
            },
        ensures
            post.persistent is Image,
            pre.ephemeral is Known ==>
                post.persistent->image.accessible_aus()
                    <= caching_disk_journal_accessible_aus(pre.ephemeral->v),
            pre.ephemeral is Unknown ==> post.persistent == pre.persistent,
    {
        reveal(CrashAwareCachingDiskJournal::State::crash);
        let keep_in_flight = lbl.arrow_Crash_keep_in_flight();
        let prepared_image = if keep_in_flight {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.frozen.unwrap(),
            )
        } else if pre.ephemeral is Unknown {
            pre.persistent->image
        } else {
            CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                pre.persistent.metadata(),
            )
        };
        assert(post.persistent == PersistentCachingDiskJournal::Image{image: prepared_image});
        if pre.ephemeral is Known {
            let frozen = if keep_in_flight {
                pre.frozen.unwrap()
            } else {
                pre.persistent.metadata()
            };
            assert(CachingDiskJournalImage::materialized_from_persistent(
                pre.ephemeral->v,
                frozen,
            ).accessible_aus() <= caching_disk_journal_accessible_aus(pre.ephemeral->v)) by {
                if keep_in_flight || pre.ephemeral->v.journal.status is Some {
                } else {
                    pre.ephemeral->v.persistent_frozen_loose_domain_persistent_aus_accessible(frozen);
                    assert(CachingDiskJournalImage::materialized_from_persistent(
                        pre.ephemeral->v,
                        frozen,
                    ).persistent == pre.ephemeral->v.disk.persistent.restrict(
                        pre.ephemeral->v.persistent_frozen_loose_domain(frozen),
                    ));
                }
            };
            assert(prepared_image.accessible_aus()
                <= caching_disk_journal_accessible_aus(pre.ephemeral->v));
        }
    }
}}

} // verus!
