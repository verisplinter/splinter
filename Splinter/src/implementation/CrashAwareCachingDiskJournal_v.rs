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
    AllocationJournal, JournalImage, LsnAUIndex, lsn_au_index_append_record,
    lsn_au_index_discard_up_to, lsn_au_index_discard_up_to_ensures, singleton_index,
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

pub open spec fn snapshot_walk_ptr(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
) -> Pointer
{
    crate::implementation::CachingDiskJournal_v::snapshot_walk_ptr(
        records,
        boundary_lsn,
        root,
        depth,
    )
}

pub open spec fn snapshot_walk_domain(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
) -> Set<Address> {
    crate::implementation::CachingDiskJournal_v::snapshot_walk_domain(
        records,
        boundary_lsn,
        root,
    )
}

pub open spec fn snapshot_tight_tj(
    records: Map<Address, JournalRecord>,
    snapshot: JournalSnapshot,
) -> TruncatedJournal {
    crate::implementation::CachingDiskJournal_v::snapshot_tight_tj(records, snapshot)
}

pub open spec fn snapshot_tight_image(
    records: Map<Address, JournalRecord>,
    snapshot: JournalSnapshot,
) -> JournalImage {
    crate::implementation::CachingDiskJournal_v::snapshot_tight_image(records, snapshot)
}

pub proof fn snapshot_walk_restrict_domain_same(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    ensures
        snapshot_walk_ptr(
            records.restrict(snapshot_walk_domain(records, boundary_lsn, root)),
            boundary_lsn,
            root,
            depth,
        ) == snapshot_walk_ptr(records, boundary_lsn, root, depth),
    decreases depth,
{
    crate::implementation::CachingDiskJournal_v::snapshot_walk_restrict_domain_same(
        records,
        boundary_lsn,
        root,
        depth,
    );
}

pub proof fn snapshot_walk_domain_restrict_domain_same(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
)
    ensures
        snapshot_walk_domain(
            records.restrict(snapshot_walk_domain(records, boundary_lsn, root)),
            boundary_lsn,
            root,
        ) =~= snapshot_walk_domain(records, boundary_lsn, root),
{
    crate::implementation::CachingDiskJournal_v::snapshot_walk_domain_restrict_domain_same(
        records,
        boundary_lsn,
        root,
    );
}

pub proof fn snapshot_walk_ptr_in_disk_view(
    dv: DiskView,
    root: Pointer,
    depth: nat,
)
    requires
        dv.wf(),
        dv.acyclic(),
        dv.is_nondangling_pointer(root),
    ensures
        snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth) is Some ==>
            dv.entries.contains_key(snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth).unwrap()),
    decreases depth,
{
    crate::implementation::CachingDiskJournal_v::snapshot_walk_ptr_in_disk_view(dv, root, depth);
}

pub proof fn snapshot_walk_ptr_step(
    records: Map<Address, JournalRecord>,
    boundary_lsn: LSN,
    root: Pointer,
    depth: nat,
)
    ensures
        root is Some && records.contains_key(root.unwrap()) ==>
            snapshot_walk_ptr(records, boundary_lsn, root, depth + 1)
            == snapshot_walk_ptr(
                records,
                boundary_lsn,
                records[root.unwrap()].cropped_prior(boundary_lsn),
                depth,
            ),
    decreases depth,
{
    crate::implementation::CachingDiskJournal_v::snapshot_walk_ptr_step(
        records,
        boundary_lsn,
        root,
        depth,
    );
}

pub proof fn snapshot_walk_ptr_extends_same(
    base_dv: DiskView,
    records: Map<Address, JournalRecord>,
    root: Pointer,
    depth: nat,
)
    requires
        base_dv.wf(),
        base_dv.acyclic(),
        base_dv.is_nondangling_pointer(root),
        base_dv.entries <= records,
    ensures
        snapshot_walk_ptr(base_dv.entries, base_dv.boundary_lsn, root, depth)
            == snapshot_walk_ptr(records, base_dv.boundary_lsn, root, depth),
    decreases depth,
{
    crate::implementation::CachingDiskJournal_v::snapshot_walk_ptr_extends_same(
        base_dv,
        records,
        root,
        depth,
    );
}

pub proof fn snapshot_tight_image_restrict_domain_same(
    records: Map<Address, JournalRecord>,
    snapshot: JournalSnapshot,
)
    ensures
        snapshot_tight_image(records, snapshot)
            == snapshot_tight_image(
                records.restrict(snapshot_walk_domain(
                    records,
                    snapshot.boundary_lsn,
                    snapshot.freshest_rec(),
                )),
                snapshot,
            ),
{
    crate::implementation::CachingDiskJournal_v::snapshot_tight_image_restrict_domain_same(
        records,
        snapshot,
    );
}

pub proof fn build_tight_entry_has_walk_depth(
    dv: DiskView,
    root: Pointer,
    addr: Address,
) -> (depth: nat)
    requires
        dv.decodable(root),
        dv.acyclic(),
        dv.build_tight(root).entries.contains_key(addr),
    ensures
        snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth) == Some(addr),
    decreases dv.the_rank_of(root),
{
    if root is Some {
        let root_addr = root.unwrap();
        if addr == root_addr {
            0
        } else {
            dv.build_tight_shape(root);
            assert(dv.build_tight(dv.next(root)).entries.contains_key(addr));
            let inner_depth = build_tight_entry_has_walk_depth(dv, dv.next(root), addr);
            assert(snapshot_walk_ptr(dv.entries, dv.boundary_lsn, dv.next(root), inner_depth)
                == Some(addr));
            snapshot_walk_ptr_step(dv.entries, dv.boundary_lsn, root, inner_depth);
            assert(snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, inner_depth + 1)
                == Some(addr));
            inner_depth + 1
        }
    } else {
        assert(false);
        0
    }
}

pub proof fn snapshot_walk_ptr_in_build_tight(
    dv: DiskView,
    root: Pointer,
    depth: nat,
)
    requires
        dv.decodable(root),
        dv.acyclic(),
    ensures
        snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth) is Some ==>
            dv.build_tight(root).entries.contains_key(
                snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, depth).unwrap(),
            ),
    decreases depth,
{
    dv.build_tight_is_awesome(root);
    let tight = dv.build_tight(root);
    if depth == 0 {
        if root is Some {
            assert(tight.entries.contains_key(root.unwrap()));
        }
    } else {
        snapshot_walk_ptr_in_build_tight(dv, root, (depth - 1) as nat);
        let prev = snapshot_walk_ptr(dv.entries, dv.boundary_lsn, root, (depth - 1) as nat);
        if prev is Some {
            assert(tight.entries.contains_key(prev.unwrap()));
            assert(tight.entries[prev.unwrap()] == dv.entries[prev.unwrap()]);
            let next = dv.entries[prev.unwrap()].cropped_prior(dv.boundary_lsn);
            if next is Some {
                assert(tight.wf());
                assert(tight.nondangling_pointers());
                assert(tight.entries[prev.unwrap()].cropped_prior(tight.boundary_lsn) == next);
                assert(tight.entries.contains_key(next.unwrap()));
            }
        }
    }
}

pub proof fn build_tight_entry_not_after_root(
    dv: DiskView,
    root: Pointer,
    first: AU,
    addr: Address,
)
    requires
        dv.pointer_is_upstream(root, first),
        root is Some,
        dv.build_tight(root).entries.contains_key(addr),
    ensures
        !root.unwrap().after_page(addr),
    decreases dv.the_rank_of(root),
{
    let root_addr = root.unwrap();
    if addr == root_addr {
        assert(!root_addr.after_page(addr));
    } else {
        dv.build_tight_shape(root);
        let next = dv.next(root);
        assert(dv.build_tight(next).entries.contains_key(addr));
        if next is Some {
            let next_addr = next.unwrap();
            dv.build_tight_ensures(next);
            dv.build_tight_is_awesome(next);
            assert(dv.build_tight(next).entries <= dv.entries);
            assert(dv.entries.contains_key(addr));
            if root_addr.after_page(addr) {
                assert(addr.au == root_addr.au);
                assert(root_addr.page < addr.page);
                assert(addr.wf());
                reveal(DiskView::pages_allocated_in_lsn_order);
                assert(dv.pages_allocated_in_lsn_order());
                assert(dv.entries[root_addr].message_seq.seq_end
                    <= dv.entries[addr].message_seq.seq_start);
                assert(dv.entries[root_addr].message_seq.wf());
                assert(dv.entries[addr].message_seq.wf());
                assert(dv.entries[addr].message_seq.seq_start
                    < dv.entries[addr].message_seq.seq_end);
                assert(dv.this_block_can_concat(root_addr));
                assert(dv.entries[next_addr].message_seq.can_concat(
                    dv.entries[root_addr].message_seq,
                ));
                assert(dv.entries[root_addr].message_seq.seq_start
                    == dv.entries[next_addr].message_seq.seq_end);
                assert(dv.boundary_lsn < dv.entries[root_addr].message_seq.seq_start) by {
                    assert(next == dv.entries[root_addr].cropped_prior(dv.boundary_lsn));
                }
                assert(dv.upstream(next_addr));
                assert(dv.decodable(next));
                assert(dv.acyclic());
                assert(dv.internal_au_pages_fully_linked());
                assert(dv.has_unique_lsns());
                assert(dv.valid_first_au(first));
                assert(dv.pointer_is_upstream(next, first));
                dv.build_tight_entry_active_bounded(next, addr);
                assert(dv.build_tight(next).entries[addr].message_seq.seq_end
                    <= dv.seq_end(next));
                assert(dv.build_tight(next).entries[addr] == dv.entries[addr]);
                assert(dv.seq_end(next) == dv.entries[next_addr].message_seq.seq_end);
                assert(dv.entries[addr].message_seq.seq_end
                    <= dv.entries[root_addr].message_seq.seq_start);
                assert(dv.entries[root_addr].message_seq.seq_start
                    < dv.entries[root_addr].message_seq.seq_end);
                assert(false);
            }
        } else {
            assert(false);
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

    pub open spec fn stable_persistent_domain(self) -> Set<Address> {
        self.stable_tj().disk_view.entries.dom()
    }

    pub open spec fn stable_tj(self) -> TruncatedJournal {
        crate::implementation::CachingDiskJournal_v::snapshot_tight_tj(
            to_journal_records(self.persistent),
            self.snapshot,
        )
    }

    pub open spec fn stable_lsn_au_index(self) -> LsnAUIndex {
        self.stable_tj().build_lsn_au_index_from_first(self.snapshot.first())
    }

    pub open spec fn live_persistent_domain(self) -> Set<Address> {
        self.stable_persistent_domain() + addresses_in_aus(self.stable_lsn_au_index().values())
    }

    pub open spec fn live_persistent(self) -> Map<Address, RawPage> {
        self.persistent.restrict(self.live_persistent_domain())
    }

    pub open spec fn tj(self) -> TruncatedJournal {
        TruncatedJournal{
            freshest_rec: self.snapshot.freshest_rec(),
            disk_view: DiskView{
                boundary_lsn: self.snapshot.boundary_lsn,
                entries: to_journal_records(self.live_persistent()),
            },
        }
    }

    pub open spec fn live_tj(self) -> TruncatedJournal {
        self.tj()
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

pub open spec fn concrete_frozen_seq_end(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
) -> LSN {
    state.frozen_seq_end(snapshot)
}

pub open spec fn concrete_frozen_lsns(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
) -> Set<LSN> {
    state.frozen_lsns(snapshot)
}

pub open spec fn caching_disk_journal_lsn_au_index(state: CachingDiskJournal::State) -> LsnAUIndex {
    if state.journal.status is Some {
        cj_lsn_au_index(state.journal)
    } else {
        state.journal_tj().build_lsn_au_index_from_first(state.journal.snapshot.first())
    }
}

pub open spec fn caching_disk_journal_accessible_aus(state: CachingDiskJournal::State) -> Set<AU> {
    state.accessible_aus()
}

pub open spec fn concrete_frozen_tj(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
) -> TruncatedJournal {
    state.frozen_tj(snapshot).build_tight()
}

pub open spec fn concrete_frozen_image(
    state: CachingDiskJournal::State,
    snapshot: JournalSnapshot,
) -> JournalImage {
    JournalImage{tj: concrete_frozen_tj(state, snapshot), first: snapshot.first()}
}

pub proof fn caching_disk_journal_freeze_image_facts(
    state: CachingDiskJournal::State,
    frozen: CachingDiskJournalFrozenImage,
)
    requires
        CachingDiskJournal::State::next(
            state,
            state,
            CachingDiskJournal::Label::FreezeForCommit{
                frozen: frozen.snapshot,
                seq_end: frozen.seq_end,
            },
        ),
    ensures
        frozen.seq_end == state.frozen_seq_end(frozen.snapshot),
{
    let lbl = CachingDiskJournal::Label::FreezeForCommit{
        frozen: frozen.snapshot,
        seq_end: frozen.seq_end,
    };
    reveal(CachingDiskJournal::State::next);
    reveal(CachingDiskJournal::State::next_by);
    let step = choose |step: CachingDiskJournal::Step|
        CachingDiskJournal::State::next_by(state, state, lbl, step);
    match step {
        CachingDiskJournal::Step::freeze_for_commit(reads) => {
            reveal(CachingDiskJournal::State::freeze_for_commit);
        },
        _ => {
            assert(false);
        },
    }
}

pub enum EphemeralCachingDiskJournal {
    Unknown,
    Known{v: CachingDiskJournal::State},
}

state_machine!{ CrashAwareCachingDiskJournal {
    fields {
        pub persistent: CachingDiskJournalImage,
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

    init!{ initialize() {
        init persistent = CachingDiskJournalImage::empty();
        init ephemeral = EphemeralCachingDiskJournal::Unknown;
        init frozen = Option::None;
        init prepared = false;
    }}

    transition!{ load_ephemeral(lbl: Label) {
        require lbl is LoadEphemeral;
        require pre.ephemeral is Unknown;

        update ephemeral = EphemeralCachingDiskJournal::Known{
            v: CachingDiskJournal::State::load_from_persistent(
                pre.persistent.snapshot,
                pre.persistent.live_persistent(),
            ),
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
        require sync_lsn <= pre.persistent.seq_end();
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
        require pre.persistent.seq_end() <= new_boundary_lsn;
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
        prepared_image: CachingDiskJournalImage,
    ) {
        require let Label::CommitComplete{require_end, discarded} = lbl;
        require pre.ephemeral is Known;
        require pre.frozen is Some;
        require pre.prepared;
        let frozen_image = pre.frozen.unwrap();
        require prepared_image.snapshot == frozen_image.snapshot;
        require prepared_image.seq_end == frozen_image.seq_end;
        require prepared_image.persistent == pre.ephemeral->v.disk.persistent.restrict(
            pre.ephemeral->v.frozen_loose_domain(frozen_image.snapshot),
        );
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
            prepared_image.snapshot.boundary_lsn,
        );
        require CachingDiskJournal::State::next(
            pre.ephemeral->v,
            new_ephemeral,
            CachingDiskJournal::Label::DiscardOld{
                start_lsn: prepared_image.snapshot.boundary_lsn,
                require_end,
            },
        );
        require discarded == old_au_index.values().difference(new_au_index.values());

        update persistent = prepared_image;
        update ephemeral = EphemeralCachingDiskJournal::Known{v: new_ephemeral};
        update frozen = Option::None;
        update prepared = false;
    }}

    transition!{ crash(lbl: Label, prepared_image: CachingDiskJournalImage) {
        require let Label::Crash{keep_in_flight} = lbl;
        require keep_in_flight ==> pre.frozen is Some;
        require keep_in_flight ==> pre.prepared;
        require keep_in_flight ==> pre.ephemeral is Known;
        require keep_in_flight ==> prepared_image.snapshot == pre.frozen.unwrap().snapshot;
        require keep_in_flight ==> prepared_image.seq_end == pre.frozen.unwrap().seq_end;
        require keep_in_flight ==> prepared_image.persistent == pre.ephemeral->v.disk.persistent.restrict(
            pre.ephemeral->v.frozen_loose_domain(pre.frozen.unwrap().snapshot),
        );
        require keep_in_flight ==> CachingDiskJournal::State::next(
            pre.ephemeral->v,
            pre.ephemeral->v,
            CachingDiskJournal::Label::CommitPrepared{
                frozen: pre.frozen.unwrap().snapshot,
                seq_end: pre.frozen.unwrap().seq_end,
            },
        );

        update persistent = if keep_in_flight {
            prepared_image
        } else {
            pre.persistent
        };
        update ephemeral = EphemeralCachingDiskJournal::Unknown;
        update frozen = Option::None;
        update prepared = false;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool {
        &&& self.ephemeral is Unknown ==> self.frozen is None && !self.prepared
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
        assert(post.persistent.i() == JournalImage::empty());
        assert(post.persistent.tj() == TruncatedJournal::mkfs());
        assert(post.persistent.wf());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label) {
        let loaded = CachingDiskJournal::State::load_from_persistent(
            pre.persistent.snapshot,
            pre.persistent.live_persistent(),
        );
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == loaded);
        assert(loaded.disk.visible() =~= pre.persistent.live_persistent()) by {
            assert forall |addr: Address| #[trigger] loaded.disk.visible().contains_key(addr)
                implies pre.persistent.live_persistent().contains_key(addr) by {
                assert(loaded.disk.cache == Map::<Address, RawPage>::empty());
            }
            assert forall |addr: Address| #[trigger] pre.persistent.live_persistent().contains_key(addr)
                implies loaded.disk.visible().contains_key(addr) by {
                assert(loaded.disk.persistent.contains_key(addr));
            }
        }
        assert(loaded.visible_records().dom() =~= pre.persistent.live_persistent().dom()) by {
            assert forall |addr: Address| #[trigger] loaded.visible_records().dom().contains(addr)
                implies pre.persistent.live_persistent().dom().contains(addr) by {
                assert(loaded.visible_records().contains_key(addr));
                assert(loaded.disk.visible().contains_key(addr));
            }
            assert forall |addr: Address| #[trigger] pre.persistent.live_persistent().dom().contains(addr)
                implies loaded.visible_records().dom().contains(addr) by {
                assert(pre.persistent.live_persistent().contains_key(addr));
                assert(loaded.disk.visible().contains_key(addr));
                assert(loaded.visible_records().contains_key(addr));
            }
        }
        let snapshot = pre.persistent.snapshot;
        let full_records = to_journal_records(pre.persistent.persistent);
        let live_domain = pre.persistent.live_persistent_domain();
        assert(loaded.raw_visible_records() == full_records.restrict(live_domain)) by {
            assert_maps_equal!(
                loaded.raw_visible_records(),
                full_records.restrict(live_domain),
                addr => {
                    if loaded.raw_visible_records().contains_key(addr) {
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(pre.persistent.live_persistent().contains_key(addr));
                        assert(pre.persistent.persistent.contains_key(addr));
                        assert(live_domain.contains(addr));
                        assert(loaded.disk.visible()[addr] == pre.persistent.live_persistent()[addr]);
                        assert(pre.persistent.live_persistent()[addr] == pre.persistent.persistent[addr]);
                    }
                    if full_records.restrict(live_domain).contains_key(addr) {
                        assert(full_records.contains_key(addr));
                        assert(pre.persistent.persistent.contains_key(addr));
                        assert(live_domain.contains(addr));
                        assert(pre.persistent.live_persistent().contains_key(addr));
                        assert(loaded.disk.visible().contains_key(addr));
                        assert(loaded.disk.visible()[addr] == pre.persistent.live_persistent()[addr]);
                    }
                }
            );
        }
        crate::implementation::CachingDiskJournal_v::snapshot_tight_tj_matches_path_build_tight(
            loaded.raw_visible_records(),
            snapshot,
        );
        assert(loaded.journal_tj()
            == crate::implementation::CachingDiskJournal_v::snapshot_tight_tj(
                loaded.raw_visible_records(),
                snapshot,
            )) by {
            loaded.journal_tj_matches_snapshot_tight();
        }
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
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::put(new_journal) => {
                reveal(CachingDiskJournal::State::put);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_lbl = CachedJournal::Label::Put{messages: lbl.arrow_Put_records()};
                let journal_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(
                        pre.ephemeral->v.journal,
                        new_ephemeral.journal,
                        journal_lbl,
                        step,
                    );
                match journal_step {
                    CachedJournal::Step::put() => {
                        reveal(CachedJournal::State::put);
                    },
                    _ => {
                        assert(false);
                    },
                }
                CachedJournal::State::put_effect(
                    pre.ephemeral->v.journal,
                    new_ephemeral.journal,
                    lbl.arrow_Put_records(),
                );
                assert(pre.ephemeral->v.journal.seq_end() <= new_ephemeral.journal.seq_end()) by {
                    assert(lbl.arrow_Put_records().wf());
                    assert(lbl.arrow_Put_records().seq_start == pre.ephemeral->v.journal.seq_end());
                    assert(lbl.arrow_Put_records().seq_start <= lbl.arrow_Put_records().seq_end);
                    assert(new_ephemeral.journal.status.unwrap().unmarshalled_tail
                        == pre.ephemeral->v.journal.status.unwrap().unmarshalled_tail.concat(
                            lbl.arrow_Put_records(),
                        ));
                    assert(new_ephemeral.journal.seq_end() == lbl.arrow_Put_records().seq_end);
                }
            },
            _ => {
                assert(false);
            },
        }
        if pre.prepared && pre.frozen is Some && pre.frozen.unwrap().snapshot.freshest_rec() is Some {
            assert(pre.frozen.unwrap().seq_end <= pre.ephemeral->v.journal.clean_watermark());
            assert(new_ephemeral.journal.clean_watermark() == pre.ephemeral->v.journal.clean_watermark());
        }
        assert(caching_disk_journal_accessible_aus(pre.ephemeral->v)
            <= caching_disk_journal_accessible_aus(new_ephemeral)) by {
            assert forall |au: AU| #[trigger] caching_disk_journal_accessible_aus(pre.ephemeral->v).contains(au)
                implies caching_disk_journal_accessible_aus(new_ephemeral).contains(au) by {
                assert(new_ephemeral.disk == pre.ephemeral->v.disk);
                assert(new_ephemeral.mini_allocator == pre.ephemeral->v.mini_allocator);
                assert(new_ephemeral.journal.snapshot == pre.ephemeral->v.journal.snapshot);
                assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
            }
        }
    }

    #[inductive(load_index)]
    fn load_index_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::LoadIndex{
            discovered_aus: lbl.arrow_LoadIndex_discovered_aus(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::load_index(new_journal, reads) => {
                reveal(CachingDiskJournal::State::load_index);
                CachedJournal::State::load_index_effect(
                    pre.ephemeral->v.journal,
                    new_ephemeral.journal,
                    to_journal_records(reads),
                    lbl.arrow_LoadIndex_discovered_aus(),
                );
            },
            _ => {
                assert(false);
            },
        }
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.disk == pre.ephemeral->v.disk);
        assert(new_ephemeral.journal.snapshot == pre.ephemeral->v.journal.snapshot);
        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
        if pre.prepared {
            assert(false);
        }
    }

    #[inductive(observe_clean_aus)]
    fn observe_clean_aus_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        let cj_lbl = CachingDiskJournal::Label::ObserveCleanAUs{
            aus: lbl.arrow_ObserveCleanAUs_aus(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::observe_clean_aus(new_journal) => {
                reveal(CachingDiskJournal::State::observe_clean_aus);
                CachedJournal::State::observe_clean_aus_effect(
                    pre.ephemeral->v.journal,
                    new_journal,
                    lbl.arrow_ObserveCleanAUs_aus(),
                );
                if pre.prepared && pre.frozen is Some
                    && pre.frozen.unwrap().snapshot.freshest_rec() is Some {
                    assert(pre.frozen.unwrap().seq_end
                        <= pre.ephemeral->v.journal.clean_watermark());
                    assert(pre.ephemeral->v.journal.clean_watermark()
                        <= new_journal.clean_watermark());
                }
            },
            _ => {
                assert(false);
            },
        }
        assert(post.ephemeral is Known);
        assert(post.ephemeral->v == new_ephemeral);
        assert(new_ephemeral.disk == pre.ephemeral->v.disk);
        assert(new_ephemeral.journal.snapshot == pre.ephemeral->v.journal.snapshot);
        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
    }

    #[inductive(internal)]
    fn internal_inductive(pre: Self, post: Self, lbl: Label, new_ephemeral: CachingDiskJournal::State) {
        assert(CrashAwareCachingDiskJournal::State::internal(pre, post, lbl, new_ephemeral));
        assert(post.ephemeral == EphemeralCachingDiskJournal::Known{v: new_ephemeral});
        assert(post.frozen == pre.frozen);
        let cj_lbl = CachingDiskJournal::Label::Internal;
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        assert(pre.ephemeral->v.i().disk_view == pre.ephemeral->v.journal_disk_view());
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        assert(to_aus(pre.ephemeral->v.journal_disk_view().entries.dom())
            <= to_aus(new_ephemeral.journal_disk_view().entries.dom())) by {
            assert forall |au: AU| #[trigger] to_aus(pre.ephemeral->v.journal_disk_view().entries.dom()).contains(au)
                implies to_aus(new_ephemeral.journal_disk_view().entries.dom()).contains(au) by {
                let addr = choose |addr: Address|
                    pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr) && addr.au == au;
                match step {
                    CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                        reveal(CachingDiskJournal::State::caching_disk_internal);
                        CachingDisk::State::internal_visible_unchanged(pre.ephemeral->v.disk, new_ephemeral.disk);
                        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
                    },
                    CachingDiskJournal::Step::load_index(new_journal, reads) => {
                        reveal(CachingDiskJournal::State::load_index);
                        assert(false);
                    },
                    CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, new_addr, writes) => {
                        reveal(CachingDiskJournal::State::journal_marshal);
                        CachingDisk::State::access_visible_effect(
                            pre.ephemeral->v.disk,
                            new_ephemeral.disk,
                            Map::empty(),
                            writes,
                        );
                        assert(pre.ephemeral->v.visible_records().contains_key(addr));
                        assert(pre.ephemeral->v.disk.visible().contains_key(addr));
                        assert(new_ephemeral.disk.visible().contains_key(addr));
                        assert(new_ephemeral.visible_records().contains_key(addr));
                        assert(new_ephemeral.journal_disk_view().entries.dom().contains(addr));
                    },
                    CachingDiskJournal::Step::internal_noop() => {
                        reveal(CachingDiskJournal::State::internal_noop);
                        assert(new_ephemeral == pre.ephemeral->v);
                    },
                    _ => {
                        assert(false);
                    },
                }
                assert(to_aus(new_ephemeral.journal_disk_view().entries.dom()).contains(au)) by {
                    let m = Map::new(
                        |addr| new_ephemeral.journal_disk_view().entries.dom().contains(addr),
                        |addr: Address| addr.au,
                    );
                    assert(m.contains_key(addr));
                    assert(m[addr] == au);
                    assert(m.values().contains(au));
                }
            }
        }
        assert(pre.ephemeral->v.journal_disk_view().entries.dom()
            <= new_ephemeral.journal_disk_view().entries.dom()) by {
            assert forall |addr: Address| #[trigger] pre.ephemeral->v.journal_disk_view().entries.dom().contains(addr)
                implies new_ephemeral.journal_disk_view().entries.dom().contains(addr) by {
                match step {
                    CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                        reveal(CachingDiskJournal::State::caching_disk_internal);
                        CachingDisk::State::internal_visible_unchanged(pre.ephemeral->v.disk, new_ephemeral.disk);
                        assert(new_ephemeral.journal_disk_view() == pre.ephemeral->v.journal_disk_view());
                    },
                    CachingDiskJournal::Step::load_index(new_journal, reads) => {
                        reveal(CachingDiskJournal::State::load_index);
                        assert(false);
                    },
                    CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, new_addr, writes) => {
                        reveal(CachingDiskJournal::State::journal_marshal);
                        CachingDisk::State::access_visible_effect(
                            pre.ephemeral->v.disk,
                            new_ephemeral.disk,
                            Map::empty(),
                            writes,
                        );
                        assert(pre.ephemeral->v.visible_records().contains_key(addr));
                        assert(pre.ephemeral->v.disk.visible().contains_key(addr));
                        assert(new_ephemeral.disk.visible().contains_key(addr));
                        assert(new_ephemeral.visible_records().contains_key(addr));
                    },
                    CachingDiskJournal::Step::internal_noop() => {
                        reveal(CachingDiskJournal::State::internal_noop);
                        assert(new_ephemeral == pre.ephemeral->v);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        }
        if pre.frozen is Some {
            assert(pre.ephemeral->v.journal.status is Some);
            assert(new_ephemeral.journal.status is Some) by {
                match step {
                    CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                        reveal(CachingDiskJournal::State::caching_disk_internal);
                        assert(new_ephemeral.journal == pre.ephemeral->v.journal);
                        assert(new_ephemeral.journal.status == pre.ephemeral->v.journal.status);
                    },
                    CachingDiskJournal::Step::load_index(new_journal, reads) => {
                        reveal(CachingDiskJournal::State::load_index);
                        assert(false);
                    },
                    CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, new_addr, writes) => {
                        reveal(CachingDiskJournal::State::journal_marshal);
                        reveal(CachedJournal::State::next);
                        reveal(CachedJournal::State::next_by);
                        let journal_lbl = CachedJournal::Label::JournalMarshal{
                            writes: to_journal_records(writes),
                        };
                        let cj_step = choose |step: CachedJournal::Step|
                            CachedJournal::State::next_by(pre.ephemeral->v.journal, new_ephemeral.journal, journal_lbl, step);
                        match cj_step {
                            CachedJournal::Step::internal_journal_marshal(cut, addr) => {
                                reveal(CachedJournal::State::internal_journal_marshal);
                                assert(new_ephemeral.journal.status is Some);
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    },
                    CachingDiskJournal::Step::internal_noop() => {
                        reveal(CachingDiskJournal::State::internal_noop);
                        assert(new_ephemeral == pre.ephemeral->v);
                        assert(new_ephemeral.journal.status == pre.ephemeral->v.journal.status);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
            if pre.prepared {
                let frozen = pre.frozen.unwrap();
                match step {
                    CachingDiskJournal::Step::caching_disk_internal(new_disk) => {
                        reveal(CachingDiskJournal::State::caching_disk_internal);
                        CachingDisk::State::internal_visible_unchanged(pre.ephemeral->v.disk, new_ephemeral.disk);
                        assert(new_ephemeral.journal == pre.ephemeral->v.journal);
                    },
                    CachingDiskJournal::Step::internal_noop() => {
                        reveal(CachingDiskJournal::State::internal_noop);
                        assert(new_ephemeral == pre.ephemeral->v);
                    },
                    CachingDiskJournal::Step::journal_marshal(new_journal, new_disk, new_addr, writes) => {
                        reveal(CachingDiskJournal::State::journal_marshal);
                        reveal(CachedJournal::State::next);
                        reveal(CachedJournal::State::next_by);
                        let journal_lbl = CachedJournal::Label::JournalMarshal{
                            writes: to_journal_records(writes),
                        };
                        let cj_step = choose |step: CachedJournal::Step|
                            CachedJournal::State::next_by(pre.ephemeral->v.journal, new_ephemeral.journal, journal_lbl, step);
                        let (cut, addr) = match cj_step {
                            CachedJournal::Step::internal_journal_marshal(cut, addr) => {
                                reveal(CachedJournal::State::internal_journal_marshal);
                                (cut, addr)
                            },
                            _ => {
                                assert(false);
                                arbitrary()
                            },
                        };
                        let marshalled_msgs = pre.ephemeral->v.journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
                        assert(new_ephemeral.journal.status.unwrap().lsn_au_index
                            == lsn_au_index_append_record(
                                pre.ephemeral->v.journal.status.unwrap().lsn_au_index,
                                marshalled_msgs,
                                addr.au,
                            ));
                        assert(new_ephemeral.journal.status is Some);
                        if pre.prepared && frozen.snapshot.freshest_rec() is Some {
                            assert(frozen.seq_end <= pre.ephemeral->v.journal.clean_watermark());
                            assert(new_ephemeral.journal.clean_watermark()
                                == pre.ephemeral->v.journal.clean_watermark());
                        }
                    },
                    _ => {
                        assert(false);
                    },
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
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::mini_allocator_fill(new_disk) => {
                reveal(CachingDiskJournal::State::mini_allocator_fill);
            },
            CachingDiskJournal::Step::mini_allocator_prune(new_disk) => {
                reveal(CachingDiskJournal::State::mini_allocator_prune);
            },
            _ => {
                assert(false);
            },
        }
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
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, pre.ephemeral->v, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::freeze_for_commit(reads) => {
                reveal(CachingDiskJournal::State::freeze_for_commit);
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let journal_lbl = CachedJournal::Label::FreezeForCommit{
                    frozen: frozen_image.snapshot,
                    reads: to_journal_records(reads),
                };
                let cj_step = choose |step: CachedJournal::Step|
                    CachedJournal::State::next_by(pre.ephemeral->v.journal, pre.ephemeral->v.journal, journal_lbl, step);
                match cj_step {
                    CachedJournal::Step::freeze_for_commit() => {
                        reveal(CachedJournal::State::freeze_for_commit);
                    },
                    _ => {
                        assert(false);
                    },
                }
            },
            _ => {
                assert(false);
            },
        }
        assert(pre.ephemeral->v.journal.status is Some);
        pre.ephemeral->v.freeze_for_commit_image_valid(
            frozen_image.snapshot,
            frozen_image.seq_end,
        );
        caching_disk_journal_freeze_image_facts(pre.ephemeral->v, frozen_image);
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
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, pre.ephemeral->v, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::commit_prepared() => {
                if frozen.snapshot.freshest_rec() is Some {
                    assert(frozen.seq_end <= pre.ephemeral->v.journal.clean_watermark());
                }
            },
            _ => { assert(false); },
        }
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_ephemeral: CachingDiskJournal::State,
        prepared_image: CachingDiskJournalImage,
    ) {
        let frozen_image = prepared_image;
        let frozen = pre.frozen.unwrap();
        let cj_lbl = CachingDiskJournal::Label::DiscardOld{
            start_lsn: frozen_image.snapshot.boundary_lsn,
            require_end: lbl.arrow_CommitComplete_require_end(),
        };
        CachingDiskJournal::State::inv_next(pre.ephemeral->v, new_ephemeral, cj_lbl);
        reveal(CachingDiskJournal::State::next);
        reveal(CachingDiskJournal::State::next_by);
        let step = choose |step: CachingDiskJournal::Step|
            CachingDiskJournal::State::next_by(pre.ephemeral->v, new_ephemeral, cj_lbl, step);
        match step {
            CachingDiskJournal::Step::discard_old(new_journal, new_disk) => {
                reveal(CachingDiskJournal::State::discard_old);
                let old_au_index = cj_lsn_au_index(pre.ephemeral->v.journal);
                let new_au_index = lsn_au_index_discard_up_to(
                    old_au_index,
                    frozen_image.snapshot.boundary_lsn,
                );
                let deallocs = old_au_index.values().difference(new_au_index.values());
                CachingDisk::State::forget_effect(
                    pre.ephemeral->v.disk,
                    new_ephemeral.disk,
                    deallocs,
                );
                lsn_au_index_discard_up_to_ensures(
                    old_au_index,
                    frozen_image.snapshot.boundary_lsn,
                );
            },
            _ => {
                assert(false);
            },
        }
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label, prepared_image: CachingDiskJournalImage) {
        let keep_in_flight = lbl.arrow_Crash_keep_in_flight();
        if keep_in_flight {
            assert(post.persistent == prepared_image);
        } else {
            assert(post.persistent == pre.persistent);
        }
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
            CrashAwareCachingDiskJournal::Step::commit_complete(new_ephemeral, prepared_image) => {
                assert(CrashAwareCachingDiskJournal::State::commit_complete(pre, post, lbl, new_ephemeral, prepared_image)) by {
                }
                CrashAwareCachingDiskJournal::State::commit_complete_inductive(pre, post, lbl, new_ephemeral, prepared_image);
            },
            CrashAwareCachingDiskJournal::Step::crash(prepared_image) => {
                assert(CrashAwareCachingDiskJournal::State::crash(pre, post, lbl, prepared_image)) by {
                }
                CrashAwareCachingDiskJournal::State::crash_inductive(pre, post, lbl, prepared_image);
            },
            _ => {
                assert(post.inv());
            },
        }
    }
}}

} // verus!
