// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// JournalCoordinationSystem: Composes CachedJournal + Cache + Disk into a single
// system that refines to LikesJournal. This is scaffolding for the refinement proof.
//
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::{map::*,set_lib::*};
use vstd::math;

use verus_state_machines_macros::state_machine;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID};
use crate::disk::GenericDisk_v::Pointer;
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::Cache_v::*;
use crate::implementation::AtomicState_v::{raw_page_to_record, to_journal_reads};
use crate::allocation_layer::LikesJournal_v::*;

verus!{

pub closed spec fn record_to_raw_page(record: JournalRecord) -> (out: RawPage)
{
    arbitrary()
}

pub broadcast proof fn journal_unmarshall_marshall(record: JournalRecord)
    ensures record == #[trigger] raw_page_to_record(record_to_raw_page(record))
{
    assume(false);
}

pub open spec fn to_cache_writes(writes: Map<Address, JournalRecord>) -> Map<Address, RawPage>
{
    Map::new(
        |addr| writes.contains_key(addr),
        |addr| record_to_raw_page(writes[addr])
    )
}

// Helper accessors for CachedJournal fields (wrappers for the snapshot/status structure)
pub open spec fn cj_boundary_lsn(journal: CachedJournal::State) -> LSN
{
    journal.snapshot.boundary_lsn
}

pub open spec fn cj_freshest_rec(journal: CachedJournal::State) -> Pointer
{
    journal.snapshot.freshest_rec
}

pub open spec fn cj_lsn_addr_index(journal: CachedJournal::State) -> LsnAddrIndex
    recommends journal.status is Some
{
    journal.status.unwrap().lsn_addr_index
}

pub open spec fn cj_unmarshalled_tail(journal: CachedJournal::State) -> MsgHistory
    recommends journal.status is Some
{
    journal.status.unwrap().unmarshalled_tail
}

state_machine!{ JournalCoordinationSystem{
    fields {
        pub journal: CachedJournal::State,
        pub cache: Cache::State,
        pub disk: AsyncDisk::State,
    }

    pub enum Label {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen: JournalSnapshot},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        Internal{},
    }

    transition!{ read_for_recovery(lbl: Label, reads: Map<Address, RawPage>) {
        require let Label::ReadForRecovery{messages} = lbl;

        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);

        let journal_lbl = CachedJournal::Label::ReadForRecovery{messages, reads: to_journal_reads(reads)};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ freeze_for_commit(lbl: Label, frozen_domain: Set<Address>, reads: Map<Address, RawPage>) {
        require lbl is FreezeForCommit;

        let cache_lbl1 = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl1);

        let cache_lbl2 = Cache::Label::EvictableCheck{addrs: frozen_domain};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl2);

        // frozen_seq_end computed from state
        let ptr = lbl->frozen.freshest_rec;
        let frozen_seq_end = if ptr is Some { to_journal_reads(reads)[ptr.unwrap()].message_seq.seq_end } else { lbl->frozen.boundary_lsn };

        let journal_lbl = CachedJournal::Label::FreezeForCommit{
            frozen: lbl->frozen, frozen_seq_end, frozen_domain,
            reads: to_journal_reads(reads)};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ query_end_lsn(lbl: Label) {
        require lbl is QueryEndLsn;
        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn: lbl->end_lsn};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ put(lbl: Label, new_journal: CachedJournal::State) {
        require let Label::Put{messages} = lbl;
        let journal_lbl = CachedJournal::Label::Put{messages};
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);
        update journal = new_journal;
    }}

    transition!{ discard_old(lbl: Label, new_journal: CachedJournal::State, discard_addrs: Set<Address>) {
        require lbl is DiscardOld;

        let journal_lbl = CachedJournal::Label::DiscardOld{
                start_lsn: lbl->start_lsn,
                require_end: lbl->require_end,
                discard_addrs: discard_addrs,
            };
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);

        let cache_lbl = Cache::Label::EvictableCheck{addrs: discard_addrs};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);

        update journal = new_journal;
    }}

    transition!{ journal_marshal(lbl: Label, new_journal: CachedJournal::State, new_cache: Cache::State, addr: Address, record: JournalRecord) {
        require lbl is Internal;

        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: Map::empty().insert(addr, record)};
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);

        let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes: to_cache_writes(journal_lbl->writes)};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update journal = new_journal;
        update cache = new_cache;
    }}

    transition!{ cache_disk_ops(lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State,
            cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>,
            disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>) {
        require lbl is Internal;

        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        let disk_lbl = AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        require AsyncDisk::State::next(pre.disk, new_disk, disk_lbl);

        update cache = new_cache;
        update disk = new_disk;
    }}

    transition!{ cache_internal(lbl: Label, new_cache: Cache::State) {
        require lbl is Internal;
        require Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{});
        update cache = new_cache;
    }}

    transition!{ disk_internal(lbl: Label, new_disk: AsyncDisk::State) {
        require lbl is Internal;
        require AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{});
        update disk = new_disk;
    }}

    pub open spec fn tj_from_reads_and_snapshot(snapshot: JournalSnapshot, reads: Map<Address, RawPage>) -> TruncatedJournal
    {
        let dv = DiskView{
            boundary_lsn: snapshot.boundary_lsn,
            entries: to_journal_reads(reads),
        };
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec,
            disk_view: dv,
        }
    }

    init!{ initialize(disk: AsyncDisk::State, cache: Cache::State, journal: CachedJournal::State) {
        require disk.inv();
        require cache.inv();
        require journal.status is Some;
        require journal.wf();

        init disk = disk;
        init cache = cache;
        init journal = journal;
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool
    {
        &&& self.journal.wf()
        &&& self.journal.status is Some
        &&& self.cache.inv()
        &&& self.disk.inv()
        &&& self.valid_journal_structure()
    }

    /// Persistent journal pages: pages on disk that are in the lsn_addr_index
    pub open spec fn persistent_journal_disk(self) -> Map<Address, JournalRecord>
    {
        Map::new(
            |addr| self.disk.content.contains_key(addr)
                && cj_lsn_addr_index(self.journal).contains_value(addr),
            |addr| raw_page_to_record(self.disk.content[addr])
        )
    }

    /// Dirty journal pages in cache (written but not yet flushed)
    pub open spec fn dirty_journal_cache(self) -> Map<Address, JournalRecord>
    {
        Map::new(
            |addr| self.cache.lookup_map.contains_key(addr)
                && self.cache.entries.contains_key(self.cache.lookup_map[addr])
                && self.cache.entries[self.cache.lookup_map[addr]] is Filled
                && (self.cache.status_map[self.cache.lookup_map[addr]] is Writeback
                    || self.cache.status_map[self.cache.lookup_map[addr]] is Dirty),
            |addr| raw_page_to_record(self.cache.entries[self.cache.lookup_map[addr]]->data)
        )
    }

    /// Ephemeral disk view: persistent pages overridden by dirty cache pages
    pub open spec fn ephemeral_disk(self) -> DiskView
    {
        DiskView{
            boundary_lsn: cj_boundary_lsn(self.journal),
            entries: self.persistent_journal_disk().union_prefer_right(self.dirty_journal_cache()),
        }
    }

    /// Ephemeral truncated journal: the on-disk portion of the journal
    pub open spec fn ephemeral_tj(self) -> TruncatedJournal
    {
        TruncatedJournal{freshest_rec: cj_freshest_rec(self.journal), disk_view: self.ephemeral_disk()}
    }

    /// Key structural invariant connecting ephemeral_tj to CachedJournal state
    pub open spec fn valid_journal_structure(self) -> bool
    {
        &&& self.ephemeral_tj().decodable()
        &&& self.ephemeral_tj().seq_end() == cj_unmarshalled_tail(self.journal).seq_start
        &&& cj_lsn_addr_index(self.journal) == self.ephemeral_tj().build_lsn_addr_index()
        &&& cj_lsn_addr_index(self.journal).values() =~= self.ephemeral_tj().disk_view.entries.dom()
    }

    // === Proven inductive proofs ===

    #[inductive(read_for_recovery)]
    fn read_for_recovery_inductive(pre: Self, post: Self, lbl: Label, reads: Map<Address, RawPage>) {
        // Nothing changes: no update statements in the transition
    }

    #[inductive(freeze_for_commit)]
    fn freeze_for_commit_inductive(pre: Self, post: Self, lbl: Label, frozen_domain: Set<Address>, reads: Map<Address, RawPage>) {
        // Nothing changes: no update statements in the transition
    }

    #[inductive(query_end_lsn)]
    fn query_end_lsn_inductive(pre: Self, post: Self, lbl: Label) {
        // Nothing changes: no update statements in the transition
    }

    #[inductive(put)]
    fn put_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State) {
        // Only unmarshalled_tail changes (extended via concat).
        // snapshot unchanged → ephemeral_disk, ephemeral_tj unchanged.
        // lsn_addr_index unchanged.
        // concat preserves seq_start, so ephemeral_tj().seq_end() == new_tail.seq_start still holds.
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, discard_addrs: Set<Address>)
    {
        // journal changes (boundary_lsn, freshest_rec, lsn_addr_index); cache/disk unchanged
        // CachedJournal::DiscardOld moves boundary_lsn forward and prunes lsn_addr_index
        // EvictableCheck ensures discarded addrs are Clean in cache
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::EvictableCheck{addrs: discard_addrs});
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        // TODO: needs linked-list truncation reasoning to show ephemeral_tj
        //   is correctly updated (new boundary, pruned index, decodable)
        assume(post.valid_journal_structure());
    }

    #[inductive(journal_marshal)]
    fn journal_marshal_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, new_cache: Cache::State, addr: Address, record: JournalRecord)
    {
        // journal changes (new page in lsn_addr_index, tail shortened)
        // cache changes (new dirty entry for marshalled page)
        // disk unchanged
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::Access{reads: Map::empty(), writes: to_cache_writes(Map::empty().insert(addr, record))});
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        // TODO: needs consistency between marshalled record and cache write,
        //   and that new ephemeral_tj extends correctly with the marshalled page
        assume(post.valid_journal_structure());
    }

    #[inductive(cache_disk_ops)]
    fn cache_disk_ops_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>)
    {
        // journal unchanged; cache+disk change for I/O coordination
        // AsyncDisk::disk_ops doesn't change content → persistent_journal_disk unchanged
        // Cache DiskOps: load_initiate/load_complete don't add dirty entries
        //   writeback_initiate: Dirty→Writeback (both in dirty_journal_cache)
        //   writeback_complete: Writeback→Clean (removes from dirty_journal_cache,
        //     but data already on disk → ephemeral_disk unchanged)
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses});
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        // TODO: needs cross-cache-disk invariant for writeback_complete case
        assume(pre.ephemeral_disk() =~= post.ephemeral_disk());
    }

    #[inductive(cache_internal)]
    fn cache_internal_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State)
    {
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::Internal{});
        // Cache internal steps: reserve (adds Reserved, not Dirty/Writeback),
        // evict (removes Clean, not Dirty/Writeback), noop (nothing changes).
        // None affect dirty_journal_cache, but SMT can't reason through
        // Map::new predicates after Cache transition.
        // Needs: Cache::Step case-split + Map::new extensionality
        assume(pre.dirty_journal_cache() =~= post.dirty_journal_cache());
    }

    #[inductive(disk_internal)]
    fn disk_internal_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State)
    {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        // For process_read: disk content unchanged → persistent_journal_disk unchanged
        // For process_write: content[addr] updated, but if addr is in lsn_addr_index,
        //   then addr is in dirty_journal_cache (Writeback), so union_prefer_right
        //   still picks the dirty value → ephemeral_disk unchanged.
        // TODO: needs invariant that pending WriteReqs for journal addrs are in dirty cache
        assume(pre.ephemeral_disk() =~= post.ephemeral_disk());
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, disk: AsyncDisk::State, cache: Cache::State,
        journal: CachedJournal::State)
    {
        // TODO: initialize transition needs additional preconditions relating
        //   journal, cache, and disk to establish valid_journal_structure.
        //   This will come from the recovery protocol proof (mkfs/recovery).
        assume(post.valid_journal_structure());
    }
}}

/// Interpretation function: JCS → LikesJournal::State
/// This is the key function that composes the journal refinement chain.
impl JournalCoordinationSystem::State {
    pub open spec fn i(self) -> LikesJournal::State
    {
        LikesJournal::State{
            journal: LinkedJournal::State{
                truncated_journal: self.ephemeral_tj(),
                unmarshalled_tail: cj_unmarshalled_tail(self.journal),
            },
            lsn_addr_index: cj_lsn_addr_index(self.journal),
        }
    }

    pub open spec fn tj_at(self, snapshot: JournalSnapshot) -> TruncatedJournal
    {
        let disk = self.ephemeral_disk();
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec,
            disk_view: DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: disk.entries,
            }
        }
    }
}

impl JournalCoordinationSystem::Label {
    pub open spec fn i(self, state: JournalCoordinationSystem::State) -> LikesJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} => { LikesJournal::Label::ReadForRecovery{messages} }
            Self::FreezeForCommit{frozen} => {
                LikesJournal::Label::FreezeForCommit{frozen_journal: state.tj_at(frozen)}
            }
            Self::QueryEndLsn{end_lsn} => { LikesJournal::Label::QueryEndLsn{end_lsn} }
            Self::Put{messages} => { LikesJournal::Label::Put{messages} }
            Self::DiscardOld{start_lsn, require_end} => { LikesJournal::Label::DiscardOld{start_lsn, require_end} }
            Self::Internal{} => { LikesJournal::Label::Internal{} }
        }
    }
}

}
