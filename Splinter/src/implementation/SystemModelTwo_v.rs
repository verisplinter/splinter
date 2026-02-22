// SystemModelTwo: A bracket rearrangement of SystemModel<ConcreteProgramModel>.
//
// SystemModel has: program.state.{journal, cache, persistent_journal_seq_end, in_flight}
// and disk as separate top-level fields. SystemModelTwo groups these into
// ConcreteJournal::State, making the journal refinement boundary explicit.
//
// Fields:
//   concrete_journal: ConcreteJournal::State  (journal, cache, disk, crash state)
//   store: AbstractCrashAwareMap::State       (map component)
//   recovery_state, outstanding_cache_reqs, sync_req_map  (coordination)
//   requests, replies, sync_requests, sync_replies, id_history  (client I/O)

#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::multiset::Multiset;

use verus_state_machines_macros::state_machine;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID, SyncReqId, Request, Reply};
use crate::disk::GenericDisk_v::{Address, Pointer};
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::AbstractCrashAwareMap_v::AbstractCrashAwareMap;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::Cache_v::*;
use crate::implementation::AtomicState_v::{AtomicState, RecoveryState, InflightInfo, DiskEvent, InternalEvent, ProgramEvent, raw_page_to_record, to_journal_reads};
use crate::implementation::ConcreteJournal_v::ConcreteJournal;
use crate::implementation::JournalCoordinationSystem_v::JournalCoordinationSystem;
use crate::implementation::MultisetMapRelation_v::multiset_to_map;
use crate::trusted::ProgramModelTrait_t::{DiskLabel, DiskModel, ProgramDiskInfo, ProgramLabel, ProgramModelTrait, ProgramUserOp};
use crate::trusted::SystemModel_t::SystemModel;
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;

verus!{

state_machine!{ SystemModelTwo {
    fields {
        // Journal component (bundles journal, cache, disk, crash state)
        pub concrete_journal: ConcreteJournal::State,

        // Map component (identity refinement to abstract)
        pub store: AbstractCrashAwareMap::State,

        // Coordination state
        pub recovery_state: RecoveryState,
        pub outstanding_cache_reqs: Map<ID, Address>,
        pub sync_req_map: Map<SyncReqId, nat>,

        // Client I/O (same as SystemModel)
        pub requests: Multiset<Request>,
        pub replies: Multiset<Reply>,
        pub sync_requests: Multiset<SyncReqId>,
        pub sync_replies: Multiset<SyncReqId>,
        pub id_history: Multiset<ID>,
    }

    pub enum Label
    {
        AcceptRequest{ req: Request },
        DeliverReply{ reply: Reply },
        AcceptSyncRequest{ sync_req_id: SyncReqId },
        DeliverSyncReply{ sync_req_id: SyncReqId },
        ProgramUIOp{ op: ProgramUserOp },
        ProgramDiskOp{ info: ProgramDiskInfo },
        ProgramInternal,
        DiskInternal,
        Crash,
        Noop,
    }

    pub open spec fn fresh_id(self, id: ID) -> bool
    {
        !self.id_history.contains(id)
    }

    pub open spec fn client_ready(self) -> bool
    {
        &&& self.recovery_state is RecoveryComplete
        &&& self.concrete_journal.journal.status is Some
    }

    // ================================================================
    // Client I/O transitions (same as SystemModel, don't touch journal)
    // ================================================================

    transition!{ accept_request(lbl: Label) {
        require lbl is AcceptRequest;
        require pre.fresh_id(lbl->req.id);
        update requests = pre.requests.insert(lbl->req);
        update id_history = pre.id_history.insert(lbl->req.id);
    }}

    transition!{ deliver_reply(lbl: Label) {
        require lbl is DeliverReply;
        require pre.replies.contains(lbl->reply);
        update replies = pre.replies.remove(lbl->reply);
    }}

    transition!{ accept_sync_request(lbl: Label) {
        require let Label::AcceptSyncRequest{sync_req_id} = lbl;
        require pre.fresh_id(sync_req_id);
        update sync_requests = pre.sync_requests.insert(sync_req_id);
        update id_history = pre.id_history.insert(sync_req_id);
    }}

    transition!{ deliver_sync_reply(lbl: Label) {
        require let Label::DeliverSyncReply{sync_req_id} = lbl;
        require pre.sync_replies.contains(sync_req_id);
        update sync_replies = pre.sync_replies.remove(sync_req_id);
    }}

    // ================================================================
    // Program user I/O transitions
    // ================================================================

    transition!{ program_execute(lbl: Label, new_concrete_journal: ConcreteJournal::State, new_store: AbstractCrashAwareMap::State) {
        require lbl is ProgramUIOp;
        require lbl->op is Execute;
        require pre.requests.contains(lbl->op->req);

        // The AtomicState execute transition operates on journal + store
        require exists |program_event| AtomicState::execute_transition(
            pre.to_atomic(), Self::to_atomic_two(new_concrete_journal, new_store, pre),
            lbl->op->req, lbl->op->reply, program_event);

        // Disk unchanged by program execution (matches SM1 semantics)
        require new_concrete_journal.disk == pre.concrete_journal.disk;
        require new_concrete_journal.journal == pre.concrete_journal.journal ==>
            new_concrete_journal.persistent_image == pre.concrete_journal.persistent_image;

        update concrete_journal = new_concrete_journal;
        update store = new_store;
        update requests = pre.requests.remove(lbl->op->req);
        update replies = pre.replies.insert(lbl->op->reply);
    }}

    transition!{ program_accept_sync_request(lbl: Label, new_sync_req_map: Map<SyncReqId, nat>) {
        require lbl is ProgramUIOp;
        require let ProgramUserOp::AcceptSyncRequest{sync_req_id} = lbl->op;

        require AtomicState::accept_sync_request(
            pre.to_atomic(),
            AtomicState{ sync_req_map: new_sync_req_map, ..pre.to_atomic() },
            sync_req_id);

        require pre.sync_requests.contains(sync_req_id);
        update sync_req_map = new_sync_req_map;
        update sync_requests = pre.sync_requests.remove(sync_req_id);
    }}

    transition!{ program_deliver_sync_reply(lbl: Label, new_sync_req_map: Map<SyncReqId, nat>) {
        require lbl is ProgramUIOp;
        require let ProgramUserOp::DeliverSyncReply{sync_req_id} = lbl->op;

        require AtomicState::deliver_sync_reply(
            pre.to_atomic(),
            AtomicState{ sync_req_map: new_sync_req_map, ..pre.to_atomic() },
            sync_req_id);

        update sync_req_map = new_sync_req_map;
        update sync_replies = pre.sync_replies.insert(sync_req_id);
    }}

    // ================================================================
    // Program disk I/O transitions: journal-affecting ops go through ConcreteJournal
    // ================================================================

    transition!{ program_disk(lbl: Label, new_concrete_journal: ConcreteJournal::State, new_outstanding_cache_reqs: Map<ID, Address>, new_recovery_state: RecoveryState, new_store: AbstractCrashAwareMap::State, new_sync_req_map: Map<SyncReqId, nat>) {
        require lbl is ProgramDiskOp;

        // Use valid_disk_transition wrapper to avoid disk_transition trigger issues.
        let post_atomic = AtomicState {
            recovery_state: new_recovery_state,
            cache: new_concrete_journal.cache,
            outstanding_cache_reqs: new_outstanding_cache_reqs,
            store: new_store,
            journal: new_concrete_journal.journal,
            persistent_journal_seq_end: new_concrete_journal.persistent_journal_seq_end,
            in_flight: new_concrete_journal.in_flight,
            sync_req_map: new_sync_req_map,
        };
        require ConcreteProgramModel::valid_disk_transition(
            ConcreteProgramModel { state: pre.to_atomic() },
            ConcreteProgramModel { state: post_atomic },
            lbl->info);

        // Disk transition via SystemModel
        let disk_lbl = DiskLabel::DiskOps{
            requests: multiset_to_map(lbl->info.reqs),
            responses: multiset_to_map(lbl->info.resps),
        };
        require DiskModel::next(pre.concrete_journal.disk, new_concrete_journal.disk, disk_lbl);

        update concrete_journal = new_concrete_journal;
        update outstanding_cache_reqs = new_outstanding_cache_reqs;
        update recovery_state = new_recovery_state;
        update store = new_store;
        update sync_req_map = new_sync_req_map;
    }}

    // ================================================================
    // Program internal transitions
    // ================================================================

    transition!{ program_internal(lbl: Label, new_concrete_journal: ConcreteJournal::State, new_outstanding_cache_reqs: Map<ID, Address>, new_recovery_state: RecoveryState, new_store: AbstractCrashAwareMap::State) {
        require lbl is ProgramInternal;

        // Disk unchanged by program internal transitions (matches SM1 semantics)
        require new_concrete_journal.disk == pre.concrete_journal.disk;
        require new_concrete_journal.journal == pre.concrete_journal.journal ==>
            new_concrete_journal.persistent_image == pre.concrete_journal.persistent_image;

        // internal_transitions don't change sync_req_map
        let post_atomic = AtomicState {
            recovery_state: new_recovery_state,
            cache: new_concrete_journal.cache,
            outstanding_cache_reqs: new_outstanding_cache_reqs,
            store: new_store,
            journal: new_concrete_journal.journal,
            persistent_journal_seq_end: new_concrete_journal.persistent_journal_seq_end,
            in_flight: new_concrete_journal.in_flight,
            sync_req_map: pre.sync_req_map,
        };
        require exists |internal_event| AtomicState::internal_transitions(
            pre.to_atomic(), post_atomic, internal_event);

        update concrete_journal = new_concrete_journal;
        update outstanding_cache_reqs = new_outstanding_cache_reqs;
        update recovery_state = new_recovery_state;
        update store = new_store;
    }}

    // ================================================================
    // Disk internal transition
    // ================================================================

    transition!{ disk_internal(lbl: Label, new_disk: AsyncDisk::State) {
        require lbl is DiskInternal;
        require DiskModel::next(pre.concrete_journal.disk, new_disk, DiskLabel::Internal{});
        update concrete_journal = ConcreteJournal::State{ disk: new_disk, ..pre.concrete_journal };
    }}

    // ================================================================
    // Crash
    // ================================================================

    transition!{ crash(lbl: Label, new_concrete_journal: ConcreteJournal::State, new_disk: AsyncDisk::State, new_store: AbstractCrashAwareMap::State) {
        require lbl is Crash;
        require DiskModel::next(pre.concrete_journal.disk, new_disk, DiskLabel::Crash{});

        // Program reinitializes: all coordination fields reset
        let init_atomic = AtomicState {
            recovery_state: RecoveryState::Begin,
            cache: new_concrete_journal.cache,
            outstanding_cache_reqs: Map::empty(),
            store: new_store,
            journal: new_concrete_journal.journal,
            persistent_journal_seq_end: new_concrete_journal.persistent_journal_seq_end,
            in_flight: new_concrete_journal.in_flight,
            sync_req_map: Map::empty(),
        };
        require exists |slots: nat| init_atomic == AtomicState::init(slots);

        update concrete_journal = ConcreteJournal::State{ disk: new_disk, ..new_concrete_journal };
        update store = new_store;
        update recovery_state = RecoveryState::Begin;
        update outstanding_cache_reqs = Map::empty();
        update sync_req_map = Map::empty();
        update requests = Multiset::empty();
        update replies = Multiset::empty();
        update sync_requests = Multiset::empty();
    }}

    transition!{ noop(lbl: Label) {
        require lbl is Noop;
    }}
}}

// Helper functions for bracket conversion
impl SystemModelTwo::State {
    /// Reconstruct AtomicState from SystemModelTwo fields
    pub open spec fn to_atomic(self) -> AtomicState
    {
        AtomicState {
            recovery_state: self.recovery_state,
            cache: self.concrete_journal.cache,
            outstanding_cache_reqs: self.outstanding_cache_reqs,
            store: self.store,
            journal: self.concrete_journal.journal,
            persistent_journal_seq_end: self.concrete_journal.persistent_journal_seq_end,
            in_flight: self.concrete_journal.in_flight,
            sync_req_map: self.sync_req_map,
        }
    }

    /// Reconstruct AtomicState from new concrete_journal + store, preserving coordination from self
    pub open spec fn to_atomic_two(cj: ConcreteJournal::State, store: AbstractCrashAwareMap::State, coord: Self) -> AtomicState
    {
        AtomicState {
            recovery_state: coord.recovery_state,
            cache: cj.cache,
            outstanding_cache_reqs: coord.outstanding_cache_reqs,
            store: store,
            journal: cj.journal,
            persistent_journal_seq_end: cj.persistent_journal_seq_end,
            in_flight: cj.in_flight,
            sync_req_map: coord.sync_req_map,
        }
    }

    /// Convert from SystemModel state
    pub open spec fn from_system_model(sm: SystemModel::State<ConcreteProgramModel>) -> Self
    {
        SystemModelTwo::State {
            concrete_journal: ConcreteJournal::State {
                journal: sm.program.state.journal,
                cache: sm.program.state.cache,
                disk: sm.disk,
                persistent_journal_seq_end: sm.program.state.persistent_journal_seq_end,
                // SystemModel has no persistent_image field; keep this ghost field unconstrained in the adapter.
                persistent_image: arbitrary(),
                in_flight: sm.program.state.in_flight,
            },
            store: sm.program.state.store,
            recovery_state: sm.program.state.recovery_state,
            outstanding_cache_reqs: sm.program.state.outstanding_cache_reqs,
            sync_req_map: sm.program.state.sync_req_map,
            requests: sm.requests,
            replies: sm.replies,
            sync_requests: sm.sync_requests,
            sync_replies: sm.sync_replies,
            id_history: sm.id_history,
        }
    }
}

}
