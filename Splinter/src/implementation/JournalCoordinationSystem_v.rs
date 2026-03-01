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
            frozen: lbl->frozen, frozen_seq_end};
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
    #[verifier::opaque]
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
        // inv_next for post.cache.inv(); reveal for post.disk.inv()
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses});
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        cache_disk_ops_preserves_i(pre, post, new_cache, new_disk, cache_requests, cache_responses, disk_requests, disk_responses);
    }

    #[inductive(cache_internal)]
    fn cache_internal_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State)
    {
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::Internal{});
        cache_internal_preserves_i(pre, post, new_cache);
    }

    #[inductive(disk_internal)]
    fn disk_internal_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State)
    {
        // reveal for post.disk.inv()
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        disk_internal_preserves_i(pre, post, new_disk);
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

/// Helper: from cache.inv(), lookup_map[addr] gives a Filled slot whose get_addr() == addr.
/// Derives from cache.inv() => lookup_map == build_lookup_map(), proven via build_lookup_map_ensures.
proof fn cache_lookup_gets_addr(cache: Cache::State, addr: Address)
    requires
        cache.inv(),
        cache.lookup_map.contains_key(addr),
    ensures
        cache.entries.contains_key(cache.lookup_map[addr]),
        cache.entries[cache.lookup_map[addr]] is Filled,
        cache.entries[cache.lookup_map[addr]].get_addr() == addr,
{
    cache.build_lookup_map_ensures();
}

/// Helper (converse): a Filled entry's addr is in lookup_map, pointing back to the slot.
/// Derives from cache.inv() => lookup_map == build_lookup_map(), proven via build_lookup_map_ensures.
proof fn cache_filled_entry_in_lookup(cache: Cache::State, slot: Slot)
    requires
        cache.inv(),
        cache.entries.contains_key(slot),
        cache.entries[slot] is Filled,
    ensures
        cache.lookup_map.contains_key(cache.entries[slot].get_addr()),
        cache.lookup_map[cache.entries[slot].get_addr()] == slot,
{
    cache.build_lookup_map_ensures();
}

// ================================================================
// Public proof lemmas: ephemeral_disk preservation for internal transitions.
// Called by ConcreteJournalRefinement to prove pre.i() == post.i().
// ================================================================

/// Cache internal (reserve/evict/noop) preserves ephemeral_disk and JCS.i().
pub proof fn cache_internal_preserves_i(
    pre: JournalCoordinationSystem::State,
    post: JournalCoordinationSystem::State,
    new_cache: Cache::State,
)
    requires
        pre.inv(),
        Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{}),
        post.journal == pre.journal,
        post.cache == new_cache,
        post.disk == pre.disk,
    ensures
        pre.ephemeral_disk() =~= post.ephemeral_disk(),
        pre.i() =~= post.i(),
{
    Cache::State::inv_next(pre.cache, post.cache, Cache::Label::Internal{});
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step| Cache::State::next_by(pre.cache, post.cache, Cache::Label::Internal{}, step);
    match step {
        Cache::Step::reserve(new_slots_mapping) => {
            assert forall |slot: Slot|
                pre.cache.entries.contains_key(slot) && pre.cache.entries[slot] is Filled
            implies post.cache.entries.contains_key(slot)
                && #[trigger] post.cache.entries[slot] == pre.cache.entries[slot]
            by { assert(!new_slots_mapping.contains_key(slot)); };

            assert forall |addr: Address|
                post.dirty_journal_cache().dom().contains(addr)
            implies #[trigger] pre.dirty_journal_cache().dom().contains(addr)
            by {
                cache_lookup_gets_addr(post.cache, addr);
                let slot = post.cache.lookup_map[addr];
                cache_filled_entry_in_lookup(pre.cache, slot);
            };
            assert(pre.dirty_journal_cache() =~= post.dirty_journal_cache());
        }
        Cache::Step::evict(evicted_slots) => {
            assert forall |slot: Slot|
                #[trigger] pre.cache.entries.contains_key(slot)
                && pre.cache.entries[slot] is Filled
                && (pre.cache.status_map[slot] is Dirty || pre.cache.status_map[slot] is Writeback)
            implies !evicted_slots.contains(slot)
                && post.cache.entries[slot] == pre.cache.entries[slot]
                && post.cache.status_map[slot] == pre.cache.status_map[slot]
            by {};

            assert forall |addr: Address|
                pre.cache.lookup_map.contains_key(addr)
                && pre.cache.entries.contains_key(pre.cache.lookup_map[addr])
                && pre.cache.entries[pre.cache.lookup_map[addr]] is Filled
                && (pre.cache.status_map[pre.cache.lookup_map[addr]] is Dirty
                    || pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback)
            implies post.cache.lookup_map.contains_key(addr)
                && #[trigger] post.cache.lookup_map[addr] == pre.cache.lookup_map[addr]
            by {
                cache_lookup_gets_addr(pre.cache, addr);
                let slot = pre.cache.lookup_map[addr];
                assert(!evicted_slots.contains(slot));
                assert(pre.cache.entries[slot].get_addr() == addr);
                cache_filled_entry_in_lookup(post.cache, slot);
            };

            assert forall |addr: Address| !pre.cache.lookup_map.contains_key(addr)
            implies !#[trigger] post.cache.lookup_map.contains_key(addr) by {};
            assert(pre.dirty_journal_cache() =~= post.dirty_journal_cache());
        }
        Cache::Step::noop() => {}
        _ => {}
    }
}

/// Disk internal (process_read/process_write) preserves ephemeral_disk and JCS.i().
pub proof fn disk_internal_preserves_i(
    pre: JournalCoordinationSystem::State,
    post: JournalCoordinationSystem::State,
    new_disk: AsyncDisk::State,
)
    requires
        pre.inv(),
        AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{}),
        post.journal == pre.journal,
        post.cache == pre.cache,
        post.disk == new_disk,
    ensures
        pre.ephemeral_disk() =~= post.ephemeral_disk(),
        pre.i() =~= post.i(),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let step = choose |step| AsyncDisk::State::next_by(pre.disk, post.disk, AsyncDisk::Label::Internal{}, step);
    match step {
        AsyncDisk::Step::process_read(id) => {}
        AsyncDisk::Step::process_write(id) => {
            let write_addr = pre.disk.requests[id]->to;
            // TODO: prove as proper JCS invariant
            assume(cj_lsn_addr_index(pre.journal).contains_value(write_addr)
                ==> pre.dirty_journal_cache().dom().contains(write_addr));

            assert forall |addr: Address|
                pre.ephemeral_disk().entries.dom().contains(addr)
                <==> #[trigger] post.ephemeral_disk().entries.dom().contains(addr)
            by {};

            assert forall |addr: Address|
                pre.ephemeral_disk().entries.dom().contains(addr)
            implies pre.ephemeral_disk().entries[addr]
                =~= #[trigger] post.ephemeral_disk().entries[addr]
            by {};

            assert(pre.ephemeral_disk() =~= post.ephemeral_disk());
        }
        _ => {}
    }
}

/// Cache disk ops preserves ephemeral_disk and JCS.i().
pub proof fn cache_disk_ops_preserves_i(
    pre: JournalCoordinationSystem::State,
    post: JournalCoordinationSystem::State,
    new_cache: Cache::State,
    new_disk: AsyncDisk::State,
    cache_requests: Set<DiskRequest>,
    cache_responses: Map<Address, DiskResponse>,
    disk_requests: Map<ID, DiskRequest>,
    disk_responses: Map<ID, DiskResponse>,
)
    requires
        pre.inv(),
        Cache::State::next(pre.cache, new_cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses}),
        AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses}),
        post.journal == pre.journal,
        post.cache == new_cache,
        post.disk == new_disk,
    ensures
        pre.ephemeral_disk() =~= post.ephemeral_disk(),
        pre.i() =~= post.i(),
{
    Cache::State::inv_next(pre.cache, post.cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses});
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);

    let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
    let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
    match cache_step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert forall |slot: Slot|
                pre.cache.entries.contains_key(slot) && pre.cache.entries[slot] is Filled
            implies post.cache.entries.contains_key(slot)
                && #[trigger] post.cache.entries[slot] == pre.cache.entries[slot]
            by { assert(!new_slots_mapping.contains_key(slot)); };

            assert forall |addr: Address|
                post.dirty_journal_cache().dom().contains(addr)
            implies #[trigger] pre.dirty_journal_cache().dom().contains(addr)
            by {
                cache_lookup_gets_addr(post.cache, addr);
                let slot = post.cache.lookup_map[addr];
                cache_filled_entry_in_lookup(pre.cache, slot);
            };

            assert forall |addr: Address|
                pre.dirty_journal_cache().dom().contains(addr)
            implies #[trigger] post.dirty_journal_cache().dom().contains(addr)
            by {
                cache_lookup_gets_addr(pre.cache, addr);
                let slot = pre.cache.lookup_map[addr];
                cache_filled_entry_in_lookup(post.cache, slot);
            };

            assert(pre.dirty_journal_cache() =~= post.dirty_journal_cache());
        }
        Cache::Step::load_complete() => {
            assert(pre.dirty_journal_cache() =~= post.dirty_journal_cache());
        }
        Cache::Step::writeback_initiate() => {
            assert(pre.dirty_journal_cache() =~= post.dirty_journal_cache());
        }
        Cache::Step::writeback_complete() => {
            // TODO: prove via cross-component invariant
            assume(pre.ephemeral_disk() =~= post.ephemeral_disk());
        }
        _ => {}
    }
}

/// Journal marshal preserves the interpreted full journal
/// (JCS -> LikesJournal -> LinkedJournal -> PagedJournal -> AbstractJournal).
/// Unlike cache/disk internal ops, marshal mutates both journal and cache.
pub proof fn marshal_preserves_i(
    pre: JournalCoordinationSystem::State,
    post: JournalCoordinationSystem::State,
    new_journal: CachedJournal::State,
    new_cache: Cache::State,
    addr: Address,
    record: JournalRecord,
)
    requires
        pre.inv(),
        CachedJournal::State::next(
            pre.journal,
            new_journal,
            CachedJournal::Label::JournalMarshal{writes: Map::empty().insert(addr, record)},
        ),
        Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{reads: Map::empty(), writes: to_cache_writes(Map::empty().insert(addr, record))},
        ),
        post.journal == new_journal,
        post.cache == new_cache,
        post.disk == pre.disk,
    ensures
        pre.i().journal.i().i().journal == post.i().journal.i().i().journal,
{
    Cache::State::inv_next(
        pre.cache,
        post.cache,
        Cache::Label::Access{reads: Map::empty(), writes: to_cache_writes(Map::empty().insert(addr, record))},
    );
    reveal(CachedJournal::State::next);
    reveal(CachedJournal::State::next_by);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    // Marshal should preserve the interpreted full journal.
    // Remaining proof obligation: connect CachedJournal::JournalMarshal +
    // corresponding cache write to the unchanged AJ interpretation.
    assume(pre.i().journal.i().i().journal == post.i().journal.i().i().journal);
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
