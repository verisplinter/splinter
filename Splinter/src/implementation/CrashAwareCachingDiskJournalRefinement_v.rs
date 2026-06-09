// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Refinement from CrashAwareCachingDiskJournal to AllocationCrashAwareJournal.

#![allow(unused_imports)]
use vstd::prelude::*;

use crate::abstract_system::AbstractCrashAwareJournal_v::AbstractCrashAwareJournal;
use crate::abstract_system::MsgHistory_v::*;
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationCrashAwareJournal_v::{
    AllocationCrashAwareJournal, Ephemeral as AllocationEphemeral,
};
use crate::allocation_layer::AllocationCrashAwareJournalRefinement_v::*;
use crate::allocation_layer::AllocationJournal_v::{AllocationJournal, JournalImage};
use crate::disk::GenericDisk_v::{Address, AU, to_aus, to_aus_preserves_lte};
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

pub proof fn image_accessible_aus_matches_i(image: CachingDiskJournalImage)
    ensures
        image.i().accessible_aus() <= image.accessible_aus(),
{
    assert(to_journal_records(image.persistent).dom() =~= image.persistent.dom()) by {
        assert forall |addr: Address| #[trigger] to_journal_records(image.persistent).dom().contains(addr)
            implies image.persistent.dom().contains(addr) by {
            assert(to_journal_records(image.persistent).contains_key(addr));
        }
        assert forall |addr: Address| #[trigger] image.persistent.dom().contains(addr)
            implies to_journal_records(image.persistent).dom().contains(addr) by {
            assert(image.persistent.contains_key(addr));
            assert(to_journal_records(image.persistent).contains_key(addr));
        }
    }
    to_aus_preserves_lte(image.i().tj.disk_view.entries.dom(), image.persistent.dom());
}

pub proof fn frozen_tj_native_matches_i(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
)
    requires
        state.inv(),
    ensures
        concrete_frozen_tj(state, snapshot) == state.frozen_tj_i(snapshot),
{
    state.interpreted_inv();
    assert(state.i().lsn_au_index == state.lsn_au_index_or_empty());
    assert(state.i().tj().disk_view == state.journal_tj().disk_view);
    assert(state.frozen_seq_end(snapshot) == state.frozen_seq_end_i(snapshot));
    assert(state.frozen_lsns(snapshot) =~= state.frozen_lsns_i(snapshot));
    assert(concrete_frozen_tj(state, snapshot) == state.frozen_tj_i(snapshot));
}

impl EphemeralCachingDiskJournal {
    pub open spec fn i(self) -> AllocationEphemeral {
        match self {
            EphemeralCachingDiskJournal::Unknown => AllocationEphemeral::Unknown,
            EphemeralCachingDiskJournal::Known{v} => AllocationEphemeral::Known{v: v.i()},
        }
    }
}

pub open spec fn option_image_i(
    frozen: Option<CachingDiskJournalFrozenImage>,
    ephemeral: EphemeralCachingDiskJournal,
) -> Option<JournalImage> {
    if frozen is None {
        Option::None
    } else if ephemeral is Known {
        Option::Some(snapshot_tight_image(
            ephemeral->v.journal_disk_view().entries,
            frozen.unwrap().snapshot,
        ))
    } else {
        Option::Some(JournalImage::empty())
    }
}

pub proof fn unprepared_frozen_image_stable_by_extension(
    pre: CachingDiskJournal::State,
    post: CachingDiskJournal::State,
    frozen: CachingDiskJournalFrozenImage,
)
    requires
        pre.inv(),
        post.inv(),
        pre.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end),
        pre.journal_disk_view().entries <= post.journal_disk_view().entries,
    ensures
        snapshot_tight_image(pre.journal_disk_view().entries, frozen.snapshot)
            == snapshot_tight_image(post.journal_disk_view().entries, frozen.snapshot),
{
    pre.frozen_snapshot_valid_image(frozen.snapshot, frozen.seq_end);
    let base = JournalImage{
        tj: pre.frozen_tj(frozen.snapshot),
        first: frozen.snapshot.first(),
    };
    base.valid_image_implies_tight_valid_image();
    visible_snapshot_image_matches_concrete_frozen(pre, frozen.snapshot, frozen.seq_end);
    let pre_image = snapshot_tight_image(pre.journal_disk_view().entries, frozen.snapshot);
    assert(pre_image == concrete_frozen_image(pre, frozen.snapshot));
    assert(concrete_frozen_image(pre, frozen.snapshot).valid_image());
    assert(pre_image.valid_image());
    assert(pre_image.tj.disk_view.entries <= post.journal_disk_view().entries) by {
        assert forall |addr: Address| #[trigger] pre_image.tj.disk_view.entries.contains_key(addr)
            implies post.journal_disk_view().entries.contains_key(addr)
                && pre_image.tj.disk_view.entries[addr] == post.journal_disk_view().entries[addr] by {
            assert(pre_image.tj.disk_view.entries.contains_key(addr));
            assert(pre_image.tj.disk_view.entries[addr]
                == pre.journal_disk_view().entries[addr]);
            assert(post.journal_disk_view().entries.contains_key(addr));
            assert(post.journal_disk_view().entries[addr]
                == pre.journal_disk_view().entries[addr]);
        }
    }
    snapshot_tight_image_extends_same(
        pre.journal_disk_view().entries,
        post.journal_disk_view().entries,
        frozen.snapshot,
    );
}

impl CrashAwareCachingDiskJournal::State {
    pub open spec fn i(self) -> AllocationCrashAwareJournal::State {
        AllocationCrashAwareJournal::State{
            persistent: self.persistent.i(),
            ephemeral: self.ephemeral.i(),
            frozen: option_image_i(self.frozen, self.ephemeral),
        }
    }

    pub proof fn image_valid_i(image: CachingDiskJournalImage)
        requires
            image.wf(),
        ensures
            image.i().valid_image(),
    {
        image.valid_image_implies_tight_structure();
    }

    pub proof fn interpreted_inv(self)
        requires
            self.inv(),
        ensures
            self.i().inv(),
    {
        Self::image_valid_i(self.persistent);
        if self.ephemeral is Known {
            self.ephemeral->v.interpreted_inv();
        }
        if self.frozen is Some && self.ephemeral is Known {
            let frozen = self.frozen.unwrap();
            self.ephemeral->v.frozen_snapshot_valid_image(frozen.snapshot, frozen.seq_end);
            let base = JournalImage{
                tj: self.ephemeral->v.frozen_tj(frozen.snapshot),
                first: frozen.snapshot.first(),
            };
            base.valid_image_implies_tight_valid_image();
            visible_snapshot_image_matches_concrete_frozen(
                self.ephemeral->v,
                frozen.snapshot,
                frozen.seq_end,
            );
            assert(snapshot_tight_image(
                self.ephemeral->v.journal_disk_view().entries,
                frozen.snapshot,
            ) == concrete_frozen_image(self.ephemeral->v, frozen.snapshot));
            assert(concrete_frozen_image(self.ephemeral->v, frozen.snapshot).valid_image());
            assert(snapshot_tight_image(
                self.ephemeral->v.journal_disk_view().entries,
                frozen.snapshot,
            ).valid_image());
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
                AllocationCrashAwareJournal::Label::Internal{allocs, deallocs: prune_aus},
            CrashAwareCachingDiskJournal::Label::QueryLsnPersistence{sync_lsn} =>
                AllocationCrashAwareJournal::Label::QueryLsnPersistence{sync_lsn},
            CrashAwareCachingDiskJournal::Label::CommitStart{new_boundary_lsn, snapshot, seq_end} =>
                AllocationCrashAwareJournal::Label::CommitStart{
                    new_boundary_lsn,
                    frozen_journal: if post.frozen is Some {
                        option_image_i(post.frozen, post.ephemeral).unwrap()
                    } else {
                        JournalImage::empty()
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

    pub proof fn image_seq_end(self, image: CachingDiskJournalImage)
        requires
            image.wf(),
        ensures
            image.i().tj.seq_end() == image.seq_end(),
    {
    }

    pub proof fn load_ephemeral_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::load_ephemeral(
                self,
                post,
                lbl,
            ),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        let new_ephemeral = CachingDiskJournal::State::load_from_persistent(
            self.persistent.snapshot,
            self.persistent.live_persistent(),
        );
        let persistent = self.persistent.live_persistent();
        assert(self.label_i(post, lbl) == AllocationCrashAwareJournal::Label::LoadEphemeralFromPersistent);
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.disk.visible() =~= persistent) by {
            assert forall |addr: Address| #[trigger] new_ephemeral.disk.visible().contains_key(addr)
                implies persistent.contains_key(addr) by {
                assert(new_ephemeral.disk.cache == Map::<Address, RawPage>::empty());
            }
            assert forall |addr: Address| #[trigger] persistent.contains_key(addr)
                implies new_ephemeral.disk.visible().contains_key(addr) by {
                assert(new_ephemeral.disk.persistent.contains_key(addr));
            }
        }
        assert(to_journal_records(new_ephemeral.disk.visible())
            =~= to_journal_records(persistent)) by {
            assert forall |addr: Address| #[trigger] to_journal_records(new_ephemeral.disk.visible()).contains_key(addr)
                implies to_journal_records(persistent).contains_key(addr) by {
                assert(new_ephemeral.disk.visible().contains_key(addr));
            }
            assert forall |addr: Address| #[trigger] to_journal_records(persistent).contains_key(addr)
                implies to_journal_records(new_ephemeral.disk.visible()).contains_key(addr) by {
                assert(persistent.contains_key(addr));
            }
            assert forall |addr: Address| #[trigger] to_journal_records(new_ephemeral.disk.visible())[addr]
                == to_journal_records(persistent)[addr] by {
                assert(new_ephemeral.disk.visible()[addr] == persistent[addr]);
            }
        }
        assert(new_ephemeral.journal_tj() == self.persistent.live_tj());
        self.persistent.valid_image_implies_live_valid_image();
        assert(new_ephemeral.inv());
        new_ephemeral.interpreted_inv();
        assert(new_ephemeral.i().inv());
        assert(self.persistent.i().init_by(new_ephemeral.i()));
        assert(self.i().ephemeral is Unknown);
        assert(post.i().ephemeral is Known);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::load_ephemeral_from_persistent(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn read_for_recovery_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::read_for_recovery(self, post, lbl),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
            post.i() == self.i(),
    {
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
    }

    pub proof fn query_end_lsn_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::query_end_lsn(self, post, lbl),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
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
    }

    pub proof fn put_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::put(self, post, lbl, new_ephemeral),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        let records = lbl.arrow_Put_records();
        let cj_lbl = CachingDiskJournal::Label::Put{messages: records};
        reveal(CrashAwareCachingDiskJournal::State::put);
        assert(CachingDiskJournal::State::put(
            self.ephemeral->v,
            new_ephemeral,
            cj_lbl,
            new_ephemeral.journal,
        )) by {
            reveal(CachingDiskJournal::State::next);
            reveal(CachingDiskJournal::State::next_by);
            let cj_step = choose |step| CachingDiskJournal::State::next_by(
                self.ephemeral->v,
                new_ephemeral,
                cj_lbl,
                step,
            );
            match cj_step {
                CachingDiskJournal::Step::put(new_cached_journal) => {
                    reveal(CachingDiskJournal::State::put);
                },
                _ => { assert(false); },
            }
        }
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.inv());
        self.ephemeral->v.put_refines(new_ephemeral, cj_lbl, new_ephemeral.journal);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::put(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn internal_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::internal(self, post, lbl, new_ephemeral),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        let cj_lbl = CachingDiskJournal::Label::Internal;
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.inv());
        if self.frozen is Some {
            let frozen = self.frozen.unwrap();
            CachingDiskJournal::State::internal_extends_journal_view(self.ephemeral->v, new_ephemeral);
            unprepared_frozen_image_stable_by_extension(self.ephemeral->v, new_ephemeral, frozen);
            assert(post.frozen == self.frozen);
            assert(post.prepared == self.prepared);
            assert(option_image_i(post.frozen, post.ephemeral)
                == option_image_i(self.frozen, self.ephemeral));
            assert(post.i().frozen == self.i().frozen);
        }
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn load_index_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::load_index(self, post, lbl, new_ephemeral),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        let discovered_aus = lbl.arrow_LoadIndex_discovered_aus();
        let cj_lbl = CachingDiskJournal::Label::LoadIndex{discovered_aus};
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.inv());
        if self.frozen is Some {
            let frozen = self.frozen.unwrap();
            CachingDiskJournal::State::load_index_visible_unchanged(
                self.ephemeral->v,
                new_ephemeral,
                discovered_aus,
            );
            assert(self.ephemeral->v.journal_disk_view().entries
                <= new_ephemeral.journal_disk_view().entries);
            unprepared_frozen_image_stable_by_extension(self.ephemeral->v, new_ephemeral, frozen);
            assert(post.frozen == self.frozen);
            assert(post.prepared == self.prepared);
            assert(post.i().frozen == self.i().frozen);
        }
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn observe_clean_aus_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::observe_clean_aus(self, post, lbl, new_ephemeral),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        let aus = lbl.arrow_ObserveCleanAUs_aus();
        let cj_lbl = CachingDiskJournal::Label::ObserveCleanAUs{aus};
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.inv());
        if self.frozen is Some {
            let frozen = self.frozen.unwrap();
            CachingDiskJournal::State::observe_clean_aus_visible_unchanged(
                self.ephemeral->v,
                new_ephemeral,
                aus,
            );
            assert(self.ephemeral->v.journal_disk_view().entries
                <= new_ephemeral.journal_disk_view().entries);
            unprepared_frozen_image_stable_by_extension(self.ephemeral->v, new_ephemeral, frozen);
            assert(post.frozen == self.frozen);
            assert(post.prepared == self.prepared);
            assert(post.i().frozen == self.i().frozen);
        }
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn internal_alloc_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::internal_alloc(self, post, lbl, new_ephemeral),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        let allocs = lbl.arrow_InternalAlloc_allocs();
        let deallocs = lbl.arrow_InternalAlloc_deallocs();
        let prune_aus = lbl.arrow_InternalAlloc_prune_aus();
        let cj_lbl = CachingDiskJournal::Label::InternalAlloc{allocs, deallocs, prune_aus};
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        image_accessible_aus_matches_i(self.persistent);
        assert(self.ephemeral->v.i().accessible_aus()
            <= caching_disk_journal_accessible_aus(self.ephemeral->v)) by {
            self.ephemeral->v.journal_disk_aus_match_index_values();
            assert forall |au: AU| #[trigger] self.ephemeral->v.i().accessible_aus().contains(au)
                implies caching_disk_journal_accessible_aus(self.ephemeral->v).contains(au) by {
                if self.ephemeral->v.mini_allocator.all_aus().contains(au) {
                } else {
                    assert(to_aus(self.ephemeral->v.journal_disk_view().entries.dom()).contains(au));
                    assert(self.ephemeral->v.accessible_aus().contains(au));
                }
            }
        }
        assert(self.i().persistent.accessible_aus()
            <= caching_disk_journal_accessible_aus(self.ephemeral->v)) by {
            self.ephemeral->v.journal_disk_aus_match_index_values();
            assert(self.i().persistent.tj.disk_view.entries.dom()
                == self.persistent.live_tj().disk_view.entries.dom());
            assert(self.persistent.live_tj().disk_view.entries.dom()
                <= self.ephemeral->v.journal_disk_view().entries.dom());
            to_aus_preserves_lte(
                self.i().persistent.tj.disk_view.entries.dom(),
                self.ephemeral->v.journal_disk_view().entries.dom(),
            );
            assert forall |au: AU| #[trigger] self.i().persistent.accessible_aus().contains(au)
                implies caching_disk_journal_accessible_aus(self.ephemeral->v).contains(au) by {
                assert(to_aus(self.i().persistent.tj.disk_view.entries.dom()).contains(au));
                assert(to_aus(self.ephemeral->v.journal_disk_view().entries.dom()).contains(au));
                assert(self.ephemeral->v.accessible_aus().contains(au));
            }
        }
        reveal(CrashAwareCachingDiskJournal::State::internal_alloc);
        assert(allocs.disjoint(caching_disk_journal_accessible_aus(self.ephemeral->v)));
        assert(new_ephemeral.inv());
        if self.frozen is Some {
            let frozen = self.frozen.unwrap();
            CachingDiskJournal::State::internal_alloc_visible_unchanged(
                self.ephemeral->v,
                new_ephemeral,
                allocs,
                deallocs,
                prune_aus,
            );
            assert(self.ephemeral->v.journal_disk_view().entries
                <= new_ephemeral.journal_disk_view().entries);
            unprepared_frozen_image_stable_by_extension(self.ephemeral->v, new_ephemeral, frozen);
            assert(post.frozen == self.frozen);
            assert(post.prepared == self.prepared);
            assert(post.i().frozen == self.i().frozen);
        }
        assert(self.i().fresh_label(self.label_i(post, lbl)));
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn query_lsn_persistence_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::query_lsn_persistence(self, post, lbl),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        self.image_seq_end(self.persistent);
        assert(post == self);
        assert(lbl.arrow_QueryLsnPersistence_sync_lsn() <= self.i().persistent.tj.seq_end());
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::query_lsn_persistence(),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn commit_start_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_start(self, post, lbl),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        let new_boundary_lsn = lbl->new_boundary_lsn;
        let frozen_image = CachingDiskJournalFrozenImage{
            snapshot: lbl->snapshot,
            seq_end: lbl->seq_end,
        };
        let i_frozen = snapshot_tight_image(
            self.ephemeral->v.journal_disk_view().entries,
            frozen_image.snapshot,
        );
        let cj_lbl = CachingDiskJournal::Label::FreezeForCommit{
            frozen: frozen_image.snapshot,
            seq_end: frozen_image.seq_end,
        };
        caching_disk_journal_freeze_image_facts(
            self.ephemeral->v,
            frozen_image,
        );
        self.ephemeral->v.frozen_snapshot_valid_image(
            frozen_image.snapshot,
            frozen_image.seq_end,
        );
        let base_frozen = JournalImage{
            tj: self.ephemeral->v.frozen_tj(frozen_image.snapshot),
            first: frozen_image.snapshot.first(),
        };
        base_frozen.valid_image_implies_tight_valid_image();
        self.image_seq_end(self.persistent);
        assert(self.i().persistent == self.persistent.i());
        assert(self.i().persistent.tj.seq_end() == self.persistent.seq_end());
        frozen_tj_native_matches_i(self.ephemeral->v, frozen_image.snapshot);
        visible_snapshot_image_matches_concrete_frozen(
            self.ephemeral->v,
            frozen_image.snapshot,
            frozen_image.seq_end,
        );
        assert(i_frozen == concrete_frozen_image(self.ephemeral->v, frozen_image.snapshot));
        assert(concrete_frozen_image(self.ephemeral->v, frozen_image.snapshot).valid_image());
        assert(i_frozen.valid_image());
        assert(i_frozen.tj.seq_end() == frozen_image.seq_end);
        assert(self.i().persistent.tj.seq_end() <= i_frozen.tj.seq_end());
        assert(i_frozen == JournalImage{
            tj: self.ephemeral->v.frozen_tj_i(frozen_image.snapshot),
            first: frozen_image.snapshot.first(),
        });
        assert(cj_lbl.i(self.ephemeral->v) == AllocationJournal::Label::FreezeForCommit{
            frozen_journal: i_frozen,
        });
        self.ephemeral->v.interpreted_inv();
        assert(self.ephemeral->v.i().inv());
        self.ephemeral->v.next_refines(self.ephemeral->v, cj_lbl);
        AllocationJournal::State::frozen_journal_is_valid_image(
            self.ephemeral->v.i(),
            self.ephemeral->v.i(),
            cj_lbl.i(self.ephemeral->v),
        );
        assert(post.i().frozen == Option::Some(i_frozen));
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::commit_start(),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn commit_prepared_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_prepared(self, post, lbl),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
            post.i() == self.i(),
    {
        reveal(CrashAwareCachingDiskJournal::State::commit_prepared);
        let frozen = self.frozen.unwrap();
        let cj_lbl = CachingDiskJournal::Label::CommitPrepared{
            frozen: frozen.snapshot,
            seq_end: frozen.seq_end,
        };
        reveal(CrashAwareCachingDiskJournal::State::commit_prepared);
        self.ephemeral->v.next_refines(self.ephemeral->v, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(self.ephemeral->v, self.ephemeral->v, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::commit_prepared() => {
                reveal(CachingDiskJournal::State::commit_prepared);
            },
            _ => { assert(false); },
        }
        assert(post.i() == self.i());
        assert(cj_lbl.i(self.ephemeral->v) == AllocationJournal::Label::InternalAllocations{
            allocs: Set::empty(),
            deallocs: Set::empty(),
        });
        assert(self.i().fresh_label(self.label_i(post, lbl)));
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::internal(self.i().ephemeral->v),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn commit_complete_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        new_ephemeral: CachingDiskJournal::State,
        prepared_image: CachingDiskJournalImage,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::commit_complete(
                self,
                post,
                lbl,
                new_ephemeral,
                prepared_image,
            ),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        let frozen_image = prepared_image;
        let require_end = lbl.arrow_CommitComplete_require_end();
        let discarded = lbl.arrow_CommitComplete_discarded();
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: frozen_image.snapshot.boundary_lsn,
            require_end,
        };
        self.ephemeral->v.next_refines(new_ephemeral, cj_lbl);
        assert(cj_lbl.i(self.ephemeral->v) == AllocationJournal::Label::DiscardOld{
            start_lsn: frozen_image.snapshot.boundary_lsn,
            require_end,
            deallocs: discarded,
        });
        let frozen = self.frozen.unwrap();
        assert(prepared_image.snapshot == frozen.snapshot);
        assert(prepared_image.seq_end == frozen.seq_end);
        assert(prepared_image.persistent == self.ephemeral->v.disk.persistent);
        assert(self.ephemeral->v.frozen_snapshot_valid(frozen.snapshot, frozen.seq_end));
        prepared_snapshot_image_matches_visible(self.ephemeral->v, prepared_image, frozen.seq_end);
        assert(prepared_image.i()
            == snapshot_tight_image(self.ephemeral->v.journal_disk_view().entries, frozen.snapshot));
        assert(post.i().persistent == prepared_image.i());
        assert(post.i().ephemeral == AllocationEphemeral::Known{v: new_ephemeral.i()});
        assert(post.i().frozen == Option::<JournalImage>::None);
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::commit_complete(new_ephemeral.i()),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn crash_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
        prepared_image: CachingDiskJournalImage,
    )
        requires
            self.inv(),
            post.inv(),
            CrashAwareCachingDiskJournal::State::crash(self, post, lbl, prepared_image),
        ensures
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        if lbl.arrow_Crash_keep_in_flight() {
            assert(self.frozen is Some);
            assert(self.prepared);
            let frozen = self.frozen.unwrap();
            assert(prepared_image.snapshot == frozen.snapshot);
            assert(prepared_image.seq_end == frozen.seq_end);
            assert(prepared_image.persistent == self.ephemeral->v.disk.persistent);
            prepared_snapshot_image_matches_visible(self.ephemeral->v, prepared_image, frozen.seq_end);
            assert(prepared_image.i()
                == snapshot_tight_image(self.ephemeral->v.journal_disk_view().entries, frozen.snapshot));
        }
        assert(AllocationCrashAwareJournal::State::next_by(
            self.i(),
            post.i(),
            self.label_i(post, lbl),
            AllocationCrashAwareJournal::Step::crash(),
        )) by {
            reveal(AllocationCrashAwareJournal::State::next_by);
        }
        reveal(AllocationCrashAwareJournal::State::next);
    }

    pub proof fn next_refines(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.inv(),
            CrashAwareCachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
    {
        CrashAwareCachingDiskJournal::State::inv_next(self, post, lbl);
        self.interpreted_inv();
        post.interpreted_inv();
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
            self.inv(),
            AllocationCrashAwareJournal::State::next(self.i(), post.i(), self.label_i(post, lbl)),
        ensures
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        self.interpreted_inv();
        AllocationCrashAwareJournal::State::inv_next(self.i(), post.i(), self.label_i(post, lbl));
        self.i().next_refines(post.i(), self.label_i(post, lbl));
    }

    pub proof fn next_refines_abstract(
        self,
        post: Self,
        lbl: CrashAwareCachingDiskJournal::Label,
    )
        requires
            self.inv(),
            CrashAwareCachingDiskJournal::State::next(self, post, lbl),
        ensures
            post.inv(),
            AbstractCrashAwareJournal::State::next(
                self.i_abstract(),
                post.i_abstract(),
                self.label_i_abstract(post, lbl),
            ),
    {
        self.next_refines(post, lbl);
        self.allocation_next_refines_abstract(post, lbl);
    }

    pub proof fn init_refines(
        self,
    )
        requires
            CrashAwareCachingDiskJournal::State::initialize(self),
        ensures
            AllocationCrashAwareJournal::State::initialize(self.i()),
    {
        JournalImage::empty_is_valid_image();
        assert(self.i().persistent == JournalImage::empty());
    }

    pub proof fn init_refines_abstract(
        self,
    )
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
