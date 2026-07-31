// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Journal component state used by the unified shared-cache model.
//
// This model keeps journal and branch fields present from initialization, but
// service readiness is represented by their internal status fields.

#![allow(unused_imports)]

use vstd::prelude::*;
use vstd::multiset::*;
use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to;
use crate::allocation_layer::AllocationBranch_v::{BranchNode, Summary};
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{Address, AU, Pointer, to_aus};
use crate::implementation::AllocationBranchStack_v::normalize_value;
use crate::implementation::AllocationBranchStackRefinement_v::append_puts;
use crate::implementation::Cache_v::{addr_maps_to_req, Cache, Entry, Slot, Status};
use crate::implementation::CachedBranch_v::{
    CachedBranch, LoadedBranch, LoadedPathReceipt,
    root_summary_from_read, root_summary_read_valid,
};
use crate::implementation::CachedJournal_v::{CachedJournal, JournalSnapshot};
use crate::implementation::CachingDiskBranch_v::{sealed_summary_aus_between, split_read_addrs};
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, empty_abstract_superblock_image, superblock_matches,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::journal::LinkedJournal_v::JournalRecord;
use crate::marshalling::IBranchNodeFormat_v::raw_page_to_branch_node;
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{ID, Input, MapSpec, Reply, Request, SyncReqId};
use crate::spec::Messages_t::{Message, Value, nop_delta};

verus! {
#[verifier::ext_equal]
pub struct AtomicJournalImage {
    pub snapshot: JournalSnapshot,
    pub seq_end: LSN,
}

impl AtomicJournalImage {
    pub open spec fn wf(self) -> bool
    {
        self.snapshot.boundary_lsn <= self.seq_end
    }
}

state_machine!{ AtomicJournalState {
    fields {
        pub journal: CachedJournal::State,
        pub mini_allocator: MiniAllocator,
        pub persistent_seq_end: LSN,
        pub in_flight: Option<AtomicJournalImage>,
    }

    pub enum Label {
        Put{ messages: MsgHistory },
        LoadIndex{ reads: Map<Address, JournalRecord>, discovered_aus: Set<AU> },
        ReadForRecovery{ messages: MsgHistory, reads: Map<Address, JournalRecord> },
        JournalMarshal{ addr: Address, writes: Map<Address, JournalRecord> },
        ObserveCleanAUs{ aus: Set<AU> },
        FillAUs{ aus: Set<AU> },
        QueryEndLsn{ end_lsn: LSN },
        CommitStart{
            snapshot: JournalSnapshot,
            seq_end: LSN,
            reads: Map<Address, JournalRecord>,
        },
        CommitPrepared,
        CommitComplete{
            require_end: LSN,
            discarded_aus: Set<AU>,
        },
    }

    init!{ initialize(snapshot: JournalSnapshot, initial_persistent_seq_end: LSN) {
        init journal = CachedJournal::State{
            snapshot,
            status: None,
        };
        init mini_allocator = MiniAllocator::empty();
        init persistent_seq_end = initial_persistent_seq_end;
        init in_flight = None;
    }}

    transition!{ put(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::Put{messages} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::Put{messages},
        );

        update journal = new_journal;
    }}

    transition!{ load_index(
        lbl: Label,
        new_journal: CachedJournal::State,
        au_depth: nat,
        page_depth: nat,
    ) {
        require let Label::LoadIndex{reads, discovered_aus} = lbl;
        require CachedJournal::State::load_index(
            pre.journal,
            new_journal,
            CachedJournal::Label::LoadIndex{reads, discovered_aus},
            au_depth,
            page_depth,
        );
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::LoadIndex{reads, discovered_aus},
        );

        update journal = new_journal;
    }}

    transition!{ read_for_recovery(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::ReadForRecovery{messages, reads} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::ReadForRecovery{messages, reads},
        );

        update journal = new_journal;
    }}

    transition!{ journal_marshal(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::JournalMarshal{addr, writes} = lbl;
        require pre.mini_allocator.tight_next_addr(pre.journal.snapshot.freshest_rec(), addr);
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::JournalMarshal{writes},
        );

        update journal = new_journal;
        update mini_allocator = pre.mini_allocator.allocate(addr);
    }}

    transition!{ observe_clean_aus(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::ObserveCleanAUs{aus} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::ObserveCleanAUs{aus},
        );

        update journal = new_journal;
    }}

    transition!{ fill_aus(lbl: Label) {
        require let Label::FillAUs{aus} = lbl;

        update mini_allocator = pre.mini_allocator.add_aus(aus);
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require let Label::QueryEndLsn{end_lsn} = lbl;
        require CachedJournal::State::next(
            pre.journal,
            pre.journal,
            CachedJournal::Label::QueryEndLsn{end_lsn},
        );
    }}

    transition!{ commit_start(lbl: Label) {
        require let Label::CommitStart{snapshot, seq_end, reads} = lbl;
        require pre.in_flight is None;
        require pre.persistent_seq_end <= seq_end;
        require snapshot.boundary_lsn <= seq_end;
        require seq_end == journal_snapshot_seq_end_from_reads(snapshot, reads);
        require CachedJournal::State::next(
            pre.journal,
            pre.journal,
            CachedJournal::Label::FreezeForCommit{frozen: snapshot, reads},
        );

        update in_flight = Option::Some(AtomicJournalImage{snapshot, seq_end});
    }}

    transition!{ commit_prepared(lbl: Label) {
        require lbl is CommitPrepared;
        require pre.in_flight is Some;
        let image = pre.in_flight.unwrap();
        require pre.journal.status is Some;
        require image.snapshot.freshest_rec() is Some ==>
            image.seq_end <= pre.journal.clean_watermark();
    }}

    transition!{ commit_complete(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::CommitComplete{
            require_end,
            discarded_aus,
        } = lbl;
        require pre.in_flight is Some;
        let image = pre.in_flight.unwrap();
        require CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::DiscardOld{
                start_lsn: image.snapshot.boundary_lsn,
                require_end,
                deallocs: discarded_aus,
            },
        );

        update journal = new_journal;
        update persistent_seq_end = image.seq_end;
        update mini_allocator = pre.mini_allocator.prune(discarded_aus);
        update in_flight = Option::None;
    }}
}}

pub open spec fn journal_snapshot_seq_end_from_reads(
    snapshot: JournalSnapshot,
    reads: Map<Address, JournalRecord>,
) -> LSN
{
    if snapshot.freshest_rec() is Some {
        reads[snapshot.freshest_rec().unwrap()].message_seq.seq_end
    } else {
        snapshot.boundary_lsn
    }
}

impl AtomicJournalState::State {
    pub open spec fn internal_access_next(
        pre: Self,
        post: Self,
        lbl: AtomicJournalState::Label,
        reads: Map<Address, RawPage>,
        raw_writes: Map<Address, RawPage>,
    ) -> bool {
        match lbl {
            AtomicJournalState::Label::JournalMarshal{
                addr,
                writes,
            } => {
                &&& reads.is_empty()
                &&& raw_writes.dom() == set![addr]
                &&& to_journal_records(raw_writes) == writes
                &&& AtomicJournalState::State::journal_marshal(
                    pre,
                    post,
                    lbl,
                    post.journal,
                )
            },
            _ => false,
        }
    }

    pub open spec fn empty() -> Self
    {
        AtomicJournalState::State{
            journal: CachedJournal::State{
                snapshot: JournalSnapshot{boundary_lsn: 0, root: None},
                status: None,
            },
            mini_allocator: MiniAllocator::empty(),
            persistent_seq_end: 0,
            in_flight: None,
        }
    }

    pub open spec fn ready(self) -> bool
    {
        self.journal.status is Some
    }

    pub open spec fn loaded_index_aus(self) -> Set<AU>
    {
        if self.journal.status is Some {
            self.journal.status.unwrap().lsn_au_index.values()
        } else {
            Set::empty()
        }
    }

    pub open spec fn owned_aus(self) -> Set<AU>
    {
        self.loaded_index_aus() + self.mini_allocator.all_aus()
    }

    pub open spec fn wf(self) -> bool
    {
        &&& self.journal.wf()
        &&& self.mini_allocator.wf()
        &&& self.in_flight is Some ==> self.in_flight.unwrap().wf()
    }

    pub proof fn wf_next(pre: Self, post: Self, lbl: AtomicJournalState::Label)
        requires
            pre.wf(),
            AtomicJournalState::State::next(pre, post, lbl),
        ensures
            post.wf(),
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step| AtomicJournalState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicJournalState::Step::put(new_journal) => {
                assert(AtomicJournalState::State::put(pre, post, lbl, new_journal));
                let messages = match lbl {
                    AtomicJournalState::Label::Put{messages} => messages,
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::Put{
                    messages,
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::load_index(new_journal, au_depth, page_depth) => {
                assert(AtomicJournalState::State::load_index(
                    pre,
                    post,
                    lbl,
                    new_journal,
                    au_depth,
                    page_depth,
                ));
                let (reads, discovered_aus) = match lbl {
                    AtomicJournalState::Label::LoadIndex{reads, discovered_aus} => (reads, discovered_aus),
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::LoadIndex{
                    reads,
                    discovered_aus,
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::read_for_recovery(new_journal) => {
                assert(AtomicJournalState::State::read_for_recovery(pre, post, lbl, new_journal));
                let (messages, reads) = match lbl {
                    AtomicJournalState::Label::ReadForRecovery{messages, reads} => (messages, reads),
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::ReadForRecovery{
                    messages,
                    reads,
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::journal_marshal(new_journal) => {
                assert(AtomicJournalState::State::journal_marshal(pre, post, lbl, new_journal));
                let (addr, writes) = match lbl {
                    AtomicJournalState::Label::JournalMarshal{addr, writes} => (addr, writes),
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::JournalMarshal{
                    writes,
                });
                assert(pre.mini_allocator.allocate(addr).wf());
                assert(pre.mini_allocator.allocate(addr).wf());
                assert(post.wf());
            },
            AtomicJournalState::Step::observe_clean_aus(new_journal) => {
                assert(AtomicJournalState::State::observe_clean_aus(pre, post, lbl, new_journal));
                let aus = match lbl {
                    AtomicJournalState::Label::ObserveCleanAUs{aus} => aus,
                    _ => arbitrary(),
                };
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::ObserveCleanAUs{
                    aus,
                });
                assert(post.wf());
            },
            AtomicJournalState::Step::fill_aus() => {
                assert(AtomicJournalState::State::fill_aus(pre, post, lbl));
                assert(post.mini_allocator.wf());
                assert(post.wf());
            },
            AtomicJournalState::Step::query_end_lsn() => {
                assert(AtomicJournalState::State::query_end_lsn(pre, post, lbl));
                assert(post == pre);
                assert(post.wf());
            },
            AtomicJournalState::Step::commit_start() => {
                assert(AtomicJournalState::State::commit_start(pre, post, lbl));
                assert(post.wf());
            },
            AtomicJournalState::Step::commit_prepared() => {
                assert(AtomicJournalState::State::commit_prepared(pre, post, lbl));
                assert(post == pre);
                assert(post.wf());
            },
            AtomicJournalState::Step::commit_complete(new_journal) => {
                assert(AtomicJournalState::State::commit_complete(pre, post, lbl, new_journal));
                let (require_end, discarded_aus) = match lbl {
                    AtomicJournalState::Label::CommitComplete{
                        require_end,
                        discarded_aus,
                    } => (require_end, discarded_aus),
                    _ => arbitrary(),
                };
                assert(pre.in_flight is Some);
                let image = pre.in_flight.unwrap();
                CachedJournal::State::inv_next(pre.journal, post.journal, CachedJournal::Label::DiscardOld{
                    start_lsn: image.snapshot.boundary_lsn,
                    require_end,
                    deallocs: discarded_aus,
                });
                pre.mini_allocator.prune_preserves_wf(discarded_aus);
                assert(post.wf());
            },
            AtomicJournalState::Step::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

    pub proof fn commit_complete_effect(
        pre: Self,
        post: Self,
        lbl: AtomicJournalState::Label,
    )
        requires
            pre.wf(),
            AtomicJournalState::State::next(pre, post, lbl),
            lbl is CommitComplete,
        ensures
            post.journal.status is Some,
            pre.journal.status is Some,
            post.journal.seq_end() == pre.journal.seq_end(),
            pre.in_flight is Some,
            post.persistent_seq_end == pre.in_flight.unwrap().seq_end,
            post.in_flight is None,
            post.mini_allocator == pre.mini_allocator.prune(lbl->discarded_aus),
            lbl->discarded_aus == pre.journal.status.unwrap().lsn_au_index.values()
                - post.journal.status.unwrap().lsn_au_index.values(),
            lbl->discarded_aus <= pre.owned_aus(),
            post.owned_aus() <= pre.owned_aus(),
            post.owned_aus().disjoint(lbl->discarded_aus),
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step| AtomicJournalState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicJournalState::Step::commit_complete(new_journal) => {
                assert(AtomicJournalState::State::commit_complete(pre, post, lbl, new_journal));
                let cj_lbl = CachedJournal::Label::DiscardOld{
                    start_lsn: pre.in_flight.unwrap().snapshot.boundary_lsn,
                    require_end: lbl->require_end,
                    deallocs: lbl->discarded_aus,
                };
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                let cj_step = choose |cj_step|
                    CachedJournal::State::next_by(pre.journal, post.journal, cj_lbl, cj_step);
                match cj_step {
                    CachedJournal::Step::discard_old() => {
                        assert(CachedJournal::State::discard_old(pre.journal, post.journal, cj_lbl));
                        let old_index = pre.journal.status.unwrap().lsn_au_index;
                        let new_index = post.journal.status.unwrap().lsn_au_index;
                        assert(lbl->discarded_aus == old_index.values().difference(new_index.values()));
                        let start_lsn = pre.in_flight.unwrap().snapshot.boundary_lsn;
                        let new_tail = pre.journal.status.unwrap().unmarshalled_tail.bounded_discard(
                            start_lsn,
                        );
                        assert(post.journal.status.unwrap().unmarshalled_tail == new_tail);
                        if pre.journal.status.unwrap().unmarshalled_tail.seq_start <= start_lsn {
                            assert(new_tail.seq_end
                                == pre.journal.status.unwrap().unmarshalled_tail.seq_end);
                        } else {
                            assert(new_tail == pre.journal.status.unwrap().unmarshalled_tail);
                        }
                        pre.mini_allocator.prune_preserves_wf(lbl->discarded_aus);
                        assert(post.loaded_index_aus() == new_index.values());
                        assert(post.mini_allocator.all_aus()
                            == pre.mini_allocator.all_aus().difference(lbl->discarded_aus));
                        assert(lbl->discarded_aus <= pre.owned_aus());
                        assert(post.loaded_index_aus() <= pre.loaded_index_aus());
                        assert(post.mini_allocator.all_aus() <= pre.mini_allocator.all_aus());
                        assert(post.owned_aus() <= pre.owned_aus());
                        assert(post.loaded_index_aus().disjoint(lbl->discarded_aus));
                        assert(post.mini_allocator.all_aus().disjoint(lbl->discarded_aus));
                        assert(post.owned_aus().disjoint(lbl->discarded_aus));
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
    }

    pub proof fn commit_start_effect(
        pre: Self,
        post: Self,
        lbl: AtomicJournalState::Label,
    )
        requires
            AtomicJournalState::State::next(pre, post, lbl),
            lbl is CommitStart,
        ensures
            post.journal == pre.journal,
            post.mini_allocator == pre.mini_allocator,
            post.persistent_seq_end == pre.persistent_seq_end,
            post.in_flight == Option::Some(AtomicJournalImage{
                snapshot: lbl->snapshot,
                seq_end: lbl->seq_end,
            }),
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step| AtomicJournalState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicJournalState::Step::commit_start() => {
                assert(AtomicJournalState::State::commit_start(pre, post, lbl));
            },
            _ => {
                assert(false);
            },
        }
    }

    pub proof fn fill_aus_effect(pre: Self, post: Self, lbl: AtomicJournalState::Label)
        requires
            AtomicJournalState::State::next(pre, post, lbl),
            lbl is FillAUs,
        ensures
            post.journal == pre.journal,
            post.persistent_seq_end == pre.persistent_seq_end,
            post.in_flight == pre.in_flight,
            post.mini_allocator == pre.mini_allocator.add_aus(match lbl {
                AtomicJournalState::Label::FillAUs{aus} => aus,
                _ => arbitrary(),
            }),
    {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        let step = choose |step| AtomicJournalState::State::next_by(pre, post, lbl, step);
        match step {
            AtomicJournalState::Step::fill_aus() => {
                assert(AtomicJournalState::State::fill_aus(pre, post, lbl)) by {
                    reveal(AtomicJournalState::State::fill_aus);
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}


} // verus!
