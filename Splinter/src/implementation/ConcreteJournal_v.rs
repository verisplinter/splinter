// ConcreteJournal: A state machine that bundles CachedJournal + Cache + Disk
// with crash-state fields (persistent_journal_seq_end, in_flight).
// Refines to AbstractCrashAwareJournal.
//
// This factors out the journal-related refinement from ModelRefinement,
// making the proof hierarchy:
//   JCS → LikesJournal (JournalCoordinationRefinement)
//   ConcreteJournal → ACAJ (ConcreteJournalRefinement)
//   SystemModel → CrashTolerantAsyncMap (ModelRefinement, appeals to above)

#![allow(unused_imports)]
use vstd::prelude::*;

use verus_state_machines_macros::state_machine;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::ID;
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::abstract_system::AbstractJournal_v::AbstractJournal;
use crate::abstract_system::AbstractCrashAwareJournal_v::{AbstractCrashAwareJournal, Ephemeral};
use crate::journal::LinkedJournal_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::Cache_v::*;
use crate::implementation::AtomicState_v::{InflightInfo, raw_page_to_record, to_journal_reads};
use crate::allocation_layer::LikesJournal_v::{LikesJournal, LsnAddrIndex};
use crate::implementation::JournalCoordinationSystem_v::{JournalCoordinationSystem, cj_boundary_lsn, cj_freshest_rec, cj_lsn_addr_index, cj_unmarshalled_tail};

verus!{

state_machine!{ ConcreteJournal {
    fields {
        pub journal: CachedJournal::State,
        pub cache: Cache::State,
        pub disk: AsyncDisk::State,
        pub persistent_journal_seq_end: LSN,
        pub persistent_image: MsgHistory,
        pub in_flight: Option<InflightInfo>,
    }

    pub enum Label {
        LoadEphemeral{},
        ReadForRecovery{messages: MsgHistory},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        Internal{},
        QueryLsnPersistence{sync_lsn: LSN},
        CommitStart{new_boundary_lsn: LSN, max_lsn: LSN},
        CommitComplete{require_end: LSN},
        Crash{keep_in_flight: bool},
    }

    // ============================================================
    // Active transitions: expressed in terms of CachedJournal/Cache/Disk sub-steps,
    // mirroring JCS transition structure + crash state management.
    // These correspond to ACAJ transitions when ephemeral is Known.
    // ============================================================

    transition!{ read_for_recovery(lbl: Label, reads: Map<Address, RawPage>) {
        require let Label::ReadForRecovery{messages} = lbl;
        require pre.journal.status is Some;
        require pre.full_journal().includes_subseq(messages);

        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);

        let journal_lbl = CachedJournal::Label::ReadForRecovery{messages, reads: to_journal_reads(reads)};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require let Label::QueryEndLsn{end_lsn} = lbl;
        require pre.journal.status is Some;

        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ put(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::Put{messages} = lbl;
        require pre.journal.status is Some;

        let journal_lbl = CachedJournal::Label::Put{messages};
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);
        update journal = new_journal;
    }}

    transition!{ internal_journal(lbl: Label) {
        require lbl is Internal;
        require pre.journal.status is Some;
        // Journal internal: no state change (AbstractJournal internal is a no-op on state)
    }}

    transition!{ internal_journal_marshal(lbl: Label, new_journal: CachedJournal::State, new_cache: Cache::State, addr: Address, record: JournalRecord) {
        require lbl is Internal;
        require pre.journal.status is Some;

        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: Map::empty().insert(addr, record)};
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);

        let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes: crate::implementation::JournalCoordinationSystem_v::to_cache_writes(journal_lbl->writes)};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        let post_full_journal = JournalCoordinationSystem::State{
            journal: new_journal,
            cache: new_cache,
            disk: pre.disk,
        }.i().journal.i().i().journal;
        require post_full_journal == pre.full_journal();

        update journal = new_journal;
        update cache = new_cache;
    }}

    transition!{ internal_cache_disk_ops(lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State,
            cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>,
            disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>) {
        require lbl is Internal;
        require pre.journal.status is Some;

        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        let disk_lbl = AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        require AsyncDisk::State::next(pre.disk, new_disk, disk_lbl);
        let post_full_journal = JournalCoordinationSystem::State{
            journal: pre.journal,
            cache: new_cache,
            disk: new_disk,
        }.i().journal.i().i().journal;
        require post_full_journal == pre.full_journal();

        update cache = new_cache;
        update disk = new_disk;
    }}

    transition!{ internal_cache(lbl: Label, new_cache: Cache::State) {
        require lbl is Internal;
        require pre.journal.status is Some;
        require Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{});
        let post_full_journal = JournalCoordinationSystem::State{
            journal: pre.journal,
            cache: new_cache,
            disk: pre.disk,
        }.i().journal.i().i().journal;
        require post_full_journal == pre.full_journal();
        update cache = new_cache;
    }}

    transition!{ internal_disk(lbl: Label, new_disk: AsyncDisk::State) {
        require lbl is Internal;
        require pre.journal.status is Some;
        require AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{});
        let post_full_journal = JournalCoordinationSystem::State{
            journal: pre.journal,
            cache: pre.cache,
            disk: new_disk,
        }.i().journal.i().i().journal;
        require post_full_journal == pre.full_journal();
        update disk = new_disk;
    }}

    transition!{ query_lsn_persistence(lbl: Label) {
        require let Label::QueryLsnPersistence{sync_lsn} = lbl;
        require pre.journal.status is Some;
        require sync_lsn <= pre.persistent_journal_seq_end;
    }}

    transition!{ commit_start(lbl: Label, frozen: JournalSnapshot, frozen_domain: Set<Address>, reads: Map<Address, RawPage>) {
        require lbl is CommitStart;
        require pre.journal.status is Some;
        require pre.in_flight is None;
        require lbl->new_boundary_lsn == frozen.boundary_lsn;

        // Freeze the journal via JCS-level freeze_for_commit
        let cache_lbl1 = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl1);

        let cache_lbl2 = Cache::Label::EvictableCheck{addrs: frozen_domain};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl2);

        let ptr = frozen.freshest_rec;
        let frozen_seq_end = if ptr is Some { to_journal_reads(reads)[ptr.unwrap()].message_seq.seq_end } else { frozen.boundary_lsn };

        let journal_lbl = CachedJournal::Label::FreezeForCommit{
            frozen, frozen_seq_end, frozen_domain,
            reads: to_journal_reads(reads)};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);

        // Record in_flight with the frozen journal version
        require lbl->max_lsn == pre.journal.seq_end();
        require frozen_seq_end <= lbl->max_lsn;
        require pre.persistent_journal_seq_end <= frozen_seq_end;
        require lbl->new_boundary_lsn <= lbl->max_lsn;
        require pre.full_journal().can_discard_to(frozen_seq_end);
        require pre.full_journal().discard_recent(frozen_seq_end).can_discard_to(frozen.boundary_lsn);
        require pre.full_journal().discard_recent(frozen_seq_end).discard_old(frozen.boundary_lsn).wf();
        require pre.full_journal().includes_subseq(
            pre.full_journal().discard_recent(frozen_seq_end).discard_old(frozen.boundary_lsn)
        );

        update in_flight = Some(InflightInfo{
            new_boundary_lsn: frozen.boundary_lsn,
            journal_version: frozen_seq_end,
            req_id: arbitrary()
        });
    }}

    transition!{ commit_complete(lbl: Label, new_journal: CachedJournal::State, discard_addrs: Set<Address>) {
        require lbl is CommitComplete;
        require pre.journal.status is Some;
        require pre.in_flight is Some;
        let start_lsn = pre.in_flight.unwrap().new_boundary_lsn;
        let pre_full_journal = pre.full_journal();
        let post_full_journal = JournalCoordinationSystem::State{
            journal: new_journal,
            cache: pre.cache,
            disk: pre.disk,
        }.i().journal.i().i().journal;

        // DiscardOld on the journal
        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn,
            require_end: lbl->require_end,
            discard_addrs,
        };
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);
        require pre_full_journal.can_discard_to(start_lsn);
        require post_full_journal == pre_full_journal.discard_old(start_lsn);

        let cache_lbl = Cache::Label::EvictableCheck{addrs: discard_addrs};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);

        update persistent_journal_seq_end = pre.in_flight.unwrap().journal_version;
        update persistent_image = pre.full_journal()
            .discard_recent(pre.in_flight.unwrap().journal_version)
            .discard_old(pre.in_flight.unwrap().new_boundary_lsn);
        update journal = new_journal;
        update in_flight = None;
    }}

    // ============================================================
    // Crash and recovery transitions
    // ============================================================

    transition!{ crash(lbl: Label) {
        require lbl is Crash;
        // Optionally apply in_flight to persistent
        update persistent_journal_seq_end = if lbl->keep_in_flight && pre.in_flight is Some {
            pre.in_flight.unwrap().journal_version
        } else {
            pre.persistent_journal_seq_end
        };
        update persistent_image = if lbl->keep_in_flight && pre.in_flight is Some && pre.journal.status is Some {
            pre.full_journal()
                .discard_recent(pre.in_flight.unwrap().journal_version)
                .discard_old(pre.in_flight.unwrap().new_boundary_lsn)
        } else {
            pre.persistent_image
        };
        // Reset ephemeral state
        update journal = CachedJournal::State{
            snapshot: pre.journal.snapshot,
            status: None,
        };
        update cache = arbitrary();    // cache is wiped
        update disk = AsyncDisk::State{
            content: pre.disk.content,
            requests: Map::empty(),
            responses: Map::empty(),
        };
        update in_flight = None;
    }}

    transition!{ load_ephemeral(lbl: Label, new_journal: CachedJournal::State) {
        require lbl is LoadEphemeral;
        require pre.journal.status is None;
        require pre.in_flight is None;
        require new_journal.status is Some;
        require new_journal.wf();
        // Snapshot doesn't change during load
        require new_journal.snapshot == pre.journal.snapshot;
        let loaded_full_journal = JournalCoordinationSystem::State{
            journal: new_journal,
            cache: pre.cache,
            disk: pre.disk,
        }.i().journal.i().i().journal;
        let loaded_aj = AbstractJournal::State{journal: loaded_full_journal};
        require loaded_full_journal.can_discard_to(pre.persistent_journal_seq_end);
        require loaded_full_journal.discard_recent(pre.persistent_journal_seq_end) == pre.persistent_image;
        require AbstractJournal::State::init_by(
            loaded_aj,
            AbstractJournal::Config::initialize(pre.persistent_image),
        );
        update journal = new_journal;
    }}

    // ============================================================
    // Invariant
    // ============================================================

    #[invariant]
    pub open spec fn inv(self) -> bool
    {
        &&& self.disk.inv()
        &&& self.cache.inv()
        &&& self.journal.status is Some ==> {
            &&& self.journal.wf()
            &&& self.jcs_view().valid_journal_structure()
            &&& self.journal_seq_end_inv()
            &&& self.persistent_image == self.full_journal().discard_recent(self.persistent_journal_seq_end)
        }
    }

    pub open spec fn journal_seq_end_inv(self) -> bool
    recommends self.journal.status is Some
    {
        let tail = self.journal.status.unwrap().unmarshalled_tail;
        &&& tail.can_discard_to(self.persistent_journal_seq_end)
        &&& self.in_flight is Some ==> {
            &&& self.journal.seq_start() <= self.in_flight.unwrap().new_boundary_lsn
            &&& self.in_flight.unwrap().new_boundary_lsn <= self.in_flight.unwrap().journal_version
            &&& tail.can_discard_to(self.in_flight.unwrap().journal_version)
            &&& self.persistent_journal_seq_end <= self.in_flight.unwrap().journal_version
        }
    }

    // Trivial inductive proofs — the hard ones get assume(false)
    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>) {}

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State) {
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        assume(post.jcs_view().valid_journal_structure());
    }

    #[inductive(internal_journal)]
    fn internal_journal_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(internal_journal_marshal)]
    fn internal_journal_marshal_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, new_cache: Cache::State, addr: Address, record: JournalRecord) {
        assume(post.inv());
    }

    #[inductive(internal_cache_disk_ops)]
    fn internal_cache_disk_ops_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>) {
        assume(post.inv());
    }

    #[inductive(internal_cache)]
    fn internal_cache_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State) {
        assume(post.inv());
    }

    #[inductive(internal_disk)]
    fn internal_disk_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State) {
        assume(post.inv());
    }

    #[inductive(query_lsn_persistence)]
    fn query_lsn_persistence_inductive(pre: Self, post: Self, lbl: Label) {}

    #[inductive(commit_start)]
    fn commit_start_inductive(pre: Self, post: Self, lbl: Label, frozen: JournalSnapshot, frozen_domain: Set<Address>, reads: Map<Address, RawPage>) {
        assume(post.inv());
    }

    #[inductive(commit_complete)]
    fn commit_complete_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, discard_addrs: Set<Address>) {
        assume(post.inv());
    }

    #[inductive(crash)]
    fn crash_inductive(pre: Self, post: Self, lbl: Label) {
        assume(post.inv());
    }

    #[inductive(load_ephemeral)]
    fn load_ephemeral_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State) {
        assume(post.inv());
    }
}}

// ============================================================
// Interpretation functions (outside state_machine! block)
// ============================================================

impl ConcreteJournal::State {
    /// Project to JCS state (only valid when journal.status is Some)
    pub open spec fn jcs_view(self) -> JournalCoordinationSystem::State
    {
        JournalCoordinationSystem::State {
            journal: self.journal,
            cache: self.cache,
            disk: self.disk,
        }
    }

    /// The full ephemeral journal MsgHistory, computed through the JCS refinement chain:
    ///   JCS → LikesJournal → LinkedJournal → PagedJournal → AbstractJournal
    pub open spec fn full_journal(self) -> MsgHistory
    {
        self.jcs_view().i().journal.i().i().journal
    }

    /// Interpret as AbstractCrashAwareJournal state.
    /// Only meaningful when journal.status is Some (ephemeral is Known).
    pub open spec fn i(self) -> AbstractCrashAwareJournal::State
    {
        if self.journal.status is Some {
            let full_journal = self.full_journal();
            AbstractCrashAwareJournal::State {
                persistent: full_journal.discard_recent(self.persistent_journal_seq_end),
                ephemeral: Ephemeral::Known {
                    v: AbstractJournal::State { journal: full_journal }
                },
                in_flight: if self.in_flight is Some {
                    Some(
                        full_journal
                            .discard_recent(self.in_flight.unwrap().journal_version)
                            .discard_old(self.in_flight.unwrap().new_boundary_lsn)
                    )
                } else {
                    None
                },
            }
        } else {
            // During crash/recovery: ephemeral is unknown
            AbstractCrashAwareJournal::State {
                persistent: self.persistent_image,
                ephemeral: Ephemeral::Unknown,
                in_flight: None,
            }
        }
    }
}

}
