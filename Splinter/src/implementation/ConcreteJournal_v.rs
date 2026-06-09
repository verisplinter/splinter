// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// ConcreteJournal: Composes CachedJournal + Cache + Disk into a single
// allocation-aware journal that refines to AllocationJournal.
//
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::{map::*,set_lib::*};
use vstd::math;
use vstd::assert_maps_equal;

use verus_state_machines_macros::state_machine;

use crate::spec::AsyncDisk_t::*;
use crate::spec::MapSpec_t::{ID};
use crate::disk::GenericDisk_v::{Pointer, to_aus};
use crate::abstract_system::StampedMap_v::LSN;
use crate::abstract_system::MsgHistory_v::*;
use crate::journal::LinkedJournal_v::*;
use crate::journal::LinkedJournalRefinement_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::implementation::Cache_v::*;
use crate::implementation::AtomicState_v::{raw_page_to_record, to_journal_records};
use crate::allocation_layer::LikesJournal_v::*;
use crate::allocation_layer::AllocationJournal_v::{
    AllocationJournal, JournalImage, LsnAUIndex,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;

verus!{

impl DiskView {
    pub proof fn boundary_advance_preserves_wf(self, new_bdy: LSN)
        requires
            self.wf(),
            self.boundary_lsn <= new_bdy,
        ensures
            (DiskView{boundary_lsn: new_bdy, entries: self.entries}).wf(),
    {
        let post = DiskView{boundary_lsn: new_bdy, entries: self.entries};

        assert(post.entries_wf());

        assert(post.nondangling_pointers()) by {
            assert forall |addr| #[trigger] post.entries.contains_key(addr)
                implies post.is_nondangling_pointer(post.entries[addr].cropped_prior(post.boundary_lsn)) by {
                let next = post.entries[addr].cropped_prior(post.boundary_lsn);
                if next is Some {
                    assert(post.boundary_lsn < post.entries[addr].message_seq.seq_start);
                    assert(self.boundary_lsn < self.entries[addr].message_seq.seq_start);
                    assert(next == self.entries[addr].cropped_prior(self.boundary_lsn));
                    assert(self.nondangling_pointers());
                }
            }
        };

        assert(post.blocks_can_concat()) by {
            assert forall |addr| #[trigger] post.entries.contains_key(addr)
                implies post.this_block_can_concat(addr) by {
                let next = post.entries[addr].cropped_prior(post.boundary_lsn);
                if next is Some {
                    assert(post.boundary_lsn < post.entries[addr].message_seq.seq_start);
                    assert(self.boundary_lsn < self.entries[addr].message_seq.seq_start);
                    assert(next == self.entries[addr].cropped_prior(self.boundary_lsn));
                    assert(self.this_block_can_concat(addr));
                }
            }
        };

        assert(post.blocks_each_have_link()) by {
            assert forall |addr| #[trigger] post.entries.contains_key(addr)
                implies post.entries[addr].has_link(post.boundary_lsn) by {
                if post.boundary_lsn < post.entries[addr].message_seq.seq_start {
                    assert(self.boundary_lsn < self.entries[addr].message_seq.seq_start);
                    assert(self.entries[addr].has_link(self.boundary_lsn));
                    assert(post.entries[addr].cropped_prior(post.boundary_lsn)
                        == self.entries[addr].cropped_prior(self.boundary_lsn));
                }
            }
        };
    }

    pub proof fn boundary_advance_preserves_acyclic(self, new_bdy: LSN)
        requires
            self.wf(),
            self.acyclic(),
            self.boundary_lsn <= new_bdy,
        ensures
            (DiskView{boundary_lsn: new_bdy, entries: self.entries}).acyclic(),
    {
        let post = DiskView{boundary_lsn: new_bdy, entries: self.entries};
        self.boundary_advance_preserves_wf(new_bdy);
        let ranking = self.the_ranking();

        assert(post.valid_ranking(ranking)) by {
            assert forall |addr| #[trigger] post.entries.contains_key(addr)
                && post.entries[addr].cropped_prior(post.boundary_lsn) is Some
                implies ranking[post.entries[addr].cropped_prior(post.boundary_lsn).unwrap()] < ranking[addr] by {
                assert(post.boundary_lsn < post.entries[addr].message_seq.seq_start);
                assert(self.boundary_lsn < self.entries[addr].message_seq.seq_start);
                assert(post.entries[addr].cropped_prior(post.boundary_lsn)
                    == self.entries[addr].cropped_prior(self.boundary_lsn));
                assert(self.valid_ranking(ranking));
            }
        };
    }
}

pub open spec fn cached_lsn_au_index(journal: CachedJournal::State) -> LsnAUIndex
    recommends journal.status is Some
{
    let index = cj_lsn_addr_index(journal);
    Map::new(
        |lsn| index.contains_key(lsn),
        |lsn| index[lsn].au,
    )
}

pub open spec fn cached_first_au(journal: CachedJournal::State) -> AU
    recommends journal.status is Some
{
    let index = cached_lsn_au_index(journal);
    if journal.snapshot.freshest_rec is Some && index.contains_key(journal.snapshot.boundary_lsn) {
        index[journal.snapshot.boundary_lsn]
    } else {
        0
    }
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

state_machine!{ ConcreteJournal{
    fields {
        pub journal: CachedJournal::State,
        pub cache: Cache::State,
        pub disk: AsyncDisk::State,
        pub mini_allocator: MiniAllocator,
        pub outstanding_cache_reqs: Map<ID, Address>,
    }

    pub enum Label {
        ReadForRecovery{messages: MsgHistory},
        FreezeForCommit{frozen: JournalSnapshot},
        QueryEndLsn{end_lsn: LSN},
        Put{messages: MsgHistory},
        DiscardOld{start_lsn: LSN, require_end: LSN},
        Internal{allocs: Set<AU>, deallocs: Set<AU>},
    }

    transition!{ read_for_recovery(lbl: Label, reads: Map<Address, RawPage>) {
        require let Label::ReadForRecovery{messages} = lbl;

        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);

        let journal_lbl = CachedJournal::Label::ReadForRecovery{messages, reads: to_journal_records(reads)};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
    }}

    transition!{ freeze_for_commit(lbl: Label, frozen_domain: Set<Address>, reads: Map<Address, RawPage>) {
        require lbl is FreezeForCommit;

        let cache_lbl1 = Cache::Label::Access{reads: reads, writes: Map::empty()};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl1);

        let cache_lbl2 = Cache::Label::EvictableCheck{aus: to_aus(frozen_domain)};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl2);

        // frozen_seq_end computed from state
        let ptr = lbl->frozen.freshest_rec;
        require ptr is Some ==> reads.contains_key(ptr.unwrap());
        let frozen_seq_end = if ptr is Some { to_journal_records(reads)[ptr.unwrap()].message_seq.seq_end } else { lbl->frozen.boundary_lsn };

        let journal_lbl = CachedJournal::Label::FreezeForCommit{
            frozen: lbl->frozen, frozen_seq_end};
        require CachedJournal::State::next(pre.journal, pre.journal, journal_lbl);
        require pre.tj_at(lbl->frozen).wf();
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
        require discard_addrs == cj_lsn_addr_index(pre.journal).values()
            .difference(cj_lsn_addr_index(new_journal).values());
        let discarded_aus = cached_lsn_au_index(pre.journal).values().difference(
            cached_lsn_au_index(new_journal).values(),
        );

        let cache_lbl = Cache::Label::EvictableCheck{aus: to_aus(discard_addrs)};
        require Cache::State::next(pre.cache, pre.cache, cache_lbl);

        update journal = new_journal;
        update mini_allocator = pre.mini_allocator.prune(discarded_aus);
    }}

    transition!{ journal_marshal(
        lbl: Label,
        new_journal: CachedJournal::State,
        new_cache: Cache::State,
        addr: Address,
        writes: Map<Address, RawPage>,
    ) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require pre.mini_allocator.tight_next_addr(pre.journal_tj().freshest_rec, addr);
        require !pre.journal_disk_view().entries.contains_key(addr);

        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)};
        require CachedJournal::State::next(pre.journal, new_journal, journal_lbl);
        require new_journal.snapshot.freshest_rec == Some(addr);

        let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update journal = new_journal;
        update cache = new_cache;
        update mini_allocator = pre.mini_allocator.allocate(addr).observe(addr);
    }}

    transition!{ internal_mini_allocator_fill(lbl: Label) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require deallocs == Set::<AU>::empty();
        require allocs.disjoint(pre.mini_allocator.allocs.dom());
        require allocs.disjoint(cached_lsn_au_index(pre.journal).values());

        update mini_allocator = pre.mini_allocator.add_aus(allocs);
    }}

    transition!{ internal_mini_allocator_prune(lbl: Label) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require forall |au| #[trigger] deallocs.contains(au)
            ==> pre.mini_allocator.can_remove(au);
        require forall |au| #[trigger] lbl.arrow_Internal_deallocs().contains(au)
            ==> pre.mini_allocator.can_remove(au);

        update mini_allocator = pre.mini_allocator.prune(deallocs);
    }}

    transition!{ cache_disk_ops(lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State,
            cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>,
            disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require pre.disk_requests_match_cache_requests(cache_requests, disk_requests);
        require pre.disk_responses_match_cache_responses(cache_responses, disk_responses);

        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        let disk_lbl = AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        require AsyncDisk::State::next(pre.disk, new_disk, disk_lbl);

        update cache = new_cache;
        update disk = new_disk;
        update outstanding_cache_reqs = pre.next_outstanding_cache_reqs(disk_requests, disk_responses);
    }}

    transition!{ cache_internal(lbl: Label, new_cache: Cache::State) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{});
        update cache = new_cache;
    }}

    transition!{ disk_internal(lbl: Label, new_disk: AsyncDisk::State) {
        require let Label::Internal{allocs, deallocs} = lbl;
        require allocs == Set::<AU>::empty();
        require deallocs == Set::<AU>::empty();
        require AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{});
        update disk = new_disk;
    }}

    pub open spec fn tj_from_reads_and_snapshot(snapshot: JournalSnapshot, reads: Map<Address, RawPage>) -> TruncatedJournal
    {
        let dv = DiskView{
            boundary_lsn: snapshot.boundary_lsn,
            entries: to_journal_records(reads),
        };
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec,
            disk_view: dv,
        }
    }

    init!{ initialize(disk: AsyncDisk::State, cache: Cache::State, journal: CachedJournal::State) {
        require disk.inv();
        require disk.requests == Map::<ID, DiskRequest>::empty();
        require disk.responses == Map::<ID, DiskResponse>::empty();
        require cache.inv();
        require cache.lookup_map == Map::<Address, Slot>::empty();
        require journal.status is Some;
        require journal.wf();
        require ConcreteJournal::State{
            disk,
            cache,
            journal,
            mini_allocator: MiniAllocator::empty(),
            outstanding_cache_reqs: Map::empty(),
        }.valid_journal_structure();
        require JournalImage{
            tj: ConcreteJournal::State{
                disk,
                cache,
                journal,
                mini_allocator: MiniAllocator::empty(),
                outstanding_cache_reqs: Map::empty(),
            }.loaded_journal_tj(),
        }.valid_image();
        require cj_unmarshalled_tail(journal) == MsgHistory::empty_history_at(
            ConcreteJournal::State{
                disk,
                cache,
                journal,
                mini_allocator: MiniAllocator::empty(),
                outstanding_cache_reqs: Map::empty(),
            }.loaded_journal_tj().seq_end(),
        );
        init disk = disk;
        init cache = cache;
        init journal = journal;
        init mini_allocator = MiniAllocator::empty();
        init outstanding_cache_reqs = Map::empty();
    }}

    #[invariant]
    pub open spec fn inv(self) -> bool
    {
        &&& self.journal.wf()
        &&& self.journal.status is Some
        &&& self.cache.inv()
        &&& self.disk.inv()
        &&& self.mini_allocator.wf()
        &&& self.valid_journal_structure()
        &&& self.clean_journal_cache_matches_disk()
        &&& self.outstanding_reqs_consistent()
    }

    pub open spec fn journal_live_aus(self) -> Set<AU>
    {
        cached_lsn_au_index(self.journal).values()
    }

    /// Journal pages decoded from the concrete disk.
    pub open spec fn disk_journal_entries(self) -> Map<Address, JournalRecord>
    {
        Map::new(
            |addr| self.disk.content.contains_key(addr),
            |addr| raw_page_to_record(self.disk.content[addr])
        )
    }

    /// Dirty/writeback journal pages decoded from the concrete cache.
    pub open spec fn dirty_cache_journal_entries(self) -> Map<Address, JournalRecord>
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

    /// Decoded concrete journal pages, with dirty cache pages overriding disk pages.
    pub open spec fn journal_overlay_entries(self) -> Map<Address, JournalRecord>
    {
        self.disk_journal_entries().union_prefer_right(self.dirty_cache_journal_entries())
    }

    /// Concrete journal disk view: decoded disk content overlaid with dirty cache pages.
    pub open spec fn journal_disk_view(self) -> DiskView
    {
        DiskView{
            boundary_lsn: cj_boundary_lsn(self.journal),
            entries: self.journal_overlay_entries(),
        }
    }

    pub open spec fn journal_tj(self) -> TruncatedJournal
    {
        TruncatedJournal{freshest_rec: cj_freshest_rec(self.journal), disk_view: self.journal_disk_view()}
    }

    /// AllocationJournal interpretation of the loaded journal area. This is a
    /// restricted view of the full concrete overlay, not a second concrete disk.
    pub open spec fn loaded_journal_disk_view(self) -> DiskView
    {
        let full = self.journal_disk_view();
        let domain = full.tight_domain(cached_lsn_au_index(self.journal), cj_freshest_rec(self.journal));
        DiskView{
            boundary_lsn: full.boundary_lsn,
            entries: full.entries.restrict(domain),
        }
    }

    pub open spec fn loaded_journal_tj(self) -> TruncatedJournal
    {
        TruncatedJournal{freshest_rec: cj_freshest_rec(self.journal), disk_view: self.loaded_journal_disk_view()}
    }

    /// Clean cache pages are coherent with the durable disk. Dirty/writeback pages
    /// are intentionally excluded because the journal disk view prefers those cache pages.
    pub open spec fn clean_journal_cache_matches_disk(self) -> bool
    {
        forall |addr: Address, data: RawPage|
            #[trigger] self.cache.valid_read(addr, data)
            && self.cache.status_map[self.cache.lookup_map[addr]] is Clean
            && self.journal_disk_view().entries.contains_key(addr)
            ==> self.disk.content.contains_key(addr) && self.disk.content[addr] == data
    }

    pub open spec fn io_id_valid(self, id: ID) -> bool
    {
        &&& self.outstanding_cache_reqs.contains_key(id)
        &&& {
            let addr = self.outstanding_cache_reqs[id];
            &&& self.cache.lookup_map.contains_key(addr)
            &&& self.cache.entries.contains_key(self.cache.lookup_map[addr])
            &&& self.cache.status_map.contains_key(self.cache.lookup_map[addr])
            &&& (self.disk.requests.contains_key(id) && self.disk.requests[id] is ReadReq ==> self.disk.content.contains_key(addr))
            &&& (self.disk.responses.contains_key(id) ==> self.disk.content.contains_key(addr))
        }
    }

    pub open spec fn outstanding_reqs_requests_ok(self) -> bool
    {
        forall |id: ID| #[trigger] self.disk.requests.contains_key(id)
            ==> {
                let req = self.disk.requests[id];
                let addr = self.outstanding_cache_reqs[id];
                &&& self.outstanding_cache_reqs.contains_key(id)
                &&& req.addr() == addr
                &&& req is ReadReq ==> {
                    let slot = self.cache.lookup_map[addr];
                    &&& self.cache.entries[slot] is Loading
                }
                &&& req is WriteReq ==> {
                    let slot = self.cache.lookup_map[addr];
                    &&& self.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                    &&& self.cache.status_map[slot] is Writeback
                }
            }
    }

    pub open spec fn outstanding_reqs_responses_ok(self) -> bool
    {
        forall |id: ID| #[trigger] self.disk.responses.contains_key(id)
            ==> {
                let resp = self.disk.responses[id];
                let addr = self.outstanding_cache_reqs[id];
                &&& self.outstanding_cache_reqs.contains_key(id)
                &&& resp is ReadResp ==> {
                    let slot = self.cache.lookup_map[addr];
                    &&& resp->data == self.disk.content[addr]
                    &&& self.cache.entries[slot] is Loading
                }
                &&& resp is WriteResp ==> {
                    let slot = self.cache.lookup_map[addr];
                    &&& self.cache.entries[slot] == Entry::Filled{addr, data: self.disk.content[addr]}
                    &&& self.cache.status_map[slot] is Writeback
                }
            }
    }

    pub open spec fn outstanding_reqs_consistent(self) -> bool
    {
        &&& self.outstanding_cache_reqs.is_injective()
        &&& self.disk.requests.dom() + self.disk.responses.dom() == self.outstanding_cache_reqs.dom()
        &&& self.outstanding_reqs_requests_ok()
        &&& self.outstanding_reqs_responses_ok()
        &&& forall |id: ID|
            #![trigger self.disk.requests.contains_key(id)]
            #![trigger self.disk.responses.contains_key(id)]
            (self.disk.requests.contains_key(id) || self.disk.responses.contains_key(id))
            ==> self.io_id_valid(id)
    }

    pub open spec fn disk_requests_match_cache_requests(
        self,
        cache_requests: Set<DiskRequest>,
        disk_requests: Map<ID, DiskRequest>,
    ) -> bool
    {
        &&& disk_requests.is_injective()
        &&& disk_requests.values() =~= cache_requests
        &&& disk_requests.dom().disjoint(self.outstanding_cache_reqs.dom())
        &&& {
            let request_addr_map =
                Map::new(|id: ID| disk_requests.contains_key(id), |id: ID| disk_requests[id].addr());
            &&& request_addr_map.is_injective()
            &&& request_addr_map.values().disjoint(self.outstanding_cache_reqs.values())
            &&& forall |id: ID| #[trigger] disk_requests.contains_key(id)
                ==> (disk_requests[id] is ReadReq ==> self.disk.content.contains_key(disk_requests[id]->from))
        }
    }

    pub open spec fn disk_responses_match_cache_responses(
        self,
        cache_responses: Map<Address, DiskResponse>,
        disk_responses: Map<ID, DiskResponse>,
    ) -> bool
    {
        &&& disk_responses.dom() <= self.outstanding_cache_reqs.dom()
        &&& cache_responses.dom() =~= self.outstanding_cache_reqs.restrict(disk_responses.dom()).values()
        &&& forall |id: ID| #[trigger] disk_responses.contains_key(id) ==> {
            let addr = self.outstanding_cache_reqs[id];
            &&& cache_responses.contains_key(addr)
            &&& cache_responses[addr] == disk_responses[id]
        }
    }

    pub open spec fn next_outstanding_cache_reqs(
        self,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    ) -> Map<ID, Address>
    {
        self.outstanding_cache_reqs.remove_keys(disk_responses.dom()).union_prefer_right(
            Map::new(
                |id: ID| disk_requests.contains_key(id),
                |id: ID| disk_requests[id].addr(),
            ),
        )
    }

    /// Key structural invariant connecting journal_tj to CachedJournal state
    #[verifier::opaque]
    pub open spec fn valid_journal_structure(self) -> bool
    {
        &&& self.journal_tj().decodable()
        &&& self.journal_tj().seq_end() == cj_unmarshalled_tail(self.journal).seq_start
        &&& cj_lsn_addr_index(self.journal) == self.journal_tj().build_lsn_addr_index()
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
        // snapshot unchanged → journal_disk_view, journal_tj unchanged.
        // lsn_addr_index unchanged.
        // concat preserves seq_start, so journal_tj().seq_end() == new_tail.seq_start still holds.
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        reveal(ConcreteJournal::State::valid_journal_structure);
        assert(post.disk == pre.disk);
        assert(post.cache == pre.cache);
        assert(post.journal.snapshot == pre.journal.snapshot);
        assert(cj_lsn_addr_index(post.journal) == cj_lsn_addr_index(pre.journal));
        assert(post.journal_tj() == pre.journal_tj());
        assert(cj_unmarshalled_tail(post.journal).seq_start == cj_unmarshalled_tail(pre.journal).seq_start);
        assert(post.valid_journal_structure());
    }

    #[inductive(discard_old)]
    fn discard_old_inductive(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State, discard_addrs: Set<Address>)
    {
        // journal changes (boundary_lsn, freshest_rec, lsn_addr_index); cache/disk unchanged
        // CachedJournal::DiscardOld moves boundary_lsn forward and prunes lsn_addr_index
        // EvictableCheck ensures discarded addrs are Clean in cache
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::EvictableCheck{aus: to_aus(discard_addrs)});
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        reveal(ConcreteJournal::State::valid_journal_structure);
        let start_lsn = lbl->start_lsn;
        let pre_index = cj_lsn_addr_index(pre.journal);
        let post_index = cj_lsn_addr_index(post.journal);
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(cj_unmarshalled_tail(post.journal)
            == cj_unmarshalled_tail(pre.journal).bounded_discard(start_lsn));
        assert(post_index == lsn_addr_index_discard_up_to(pre_index, start_lsn));
        assert(discard_addrs == pre_index.values().difference(post_index.values()));
        lsn_addr_index_discard_up_to_ensures(pre_index, start_lsn);
        assert(post_index <= pre_index);
        assert(post_index.values() <= pre_index.values()) by {
            assert forall |a: Address| #[trigger] post_index.values().contains(a)
                implies pre_index.values().contains(a) by {
                let lsn = choose |lsn| post_index.contains_key(lsn) && post_index[lsn] == a;
                assert(pre_index.contains_key(lsn));
                assert(pre_index[lsn] == a);
            }
        };
        pre.journal_tj().build_lsn_addr_index_ensures();

        if start_lsn < pre.journal_tj().seq_end() {
            assert(pre.journal_tj().can_discard_to(start_lsn)) by {
                assert(pre.journal_tj().wf());
                assert(pre.journal_tj().seq_start() == pre.journal_tj().disk_view.boundary_lsn);
                assert(pre.journal_tj().seq_start() == cj_boundary_lsn(pre.journal));
                assert(pre.journal_tj().seq_end() == cj_unmarshalled_tail(pre.journal).seq_start);
            };
            pre.journal_tj().discard_old_decodable(start_lsn);
            assert(pre.journal_tj().disk_view.index_keys_map_to_valid_entries(pre_index));
            assert(post_index.values() <= post.journal_tj().disk_view.entries.dom()) by {
                assert forall |a: Address| #[trigger] post_index.values().contains(a)
                    implies post.journal_tj().disk_view.entries.dom().contains(a) by {
                    assert(pre_index.values().contains(a));
                    let lsn = choose |lsn| pre_index.contains_key(lsn) && pre_index[lsn] == a;
                    reveal(DiskView::index_keys_map_to_valid_entries);
                    assert(pre.journal_tj().disk_view.entries.contains_key(a));
                }
            };
            assert(pre.journal_tj().discard_old_cond(start_lsn, post_index.values(), post.journal_tj()));
            assert(post.journal_tj().wf());
            pre.journal_tj().discard_old_preserves_acyclicity(start_lsn, post_index.values(), post.journal_tj());
            assert(post.journal_tj().decodable());
            pre.journal_tj().discard_old_maintains_repr_index(start_lsn, post_index, post.journal_tj());
            assert(post.journal_tj().build_lsn_addr_index() == post_index);
        } else {
            assert(pre.journal_tj().seq_start() <= start_lsn) by {
                assert(pre.journal_tj().seq_start() == cj_boundary_lsn(pre.journal));
            };
            assert(cj_freshest_rec(post.journal) is None);
            assert(post.journal_tj().freshest_rec is None);
            assert(post.journal_tj().disk_view
                == pre.journal_tj().disk_view.discard_old(start_lsn));
            pre.journal_tj().disk_view.boundary_advance_preserves_wf(start_lsn);
            pre.journal_tj().disk_view.boundary_advance_preserves_acyclic(start_lsn);
            assert(post.journal_tj().wf());
            assert(post.journal_tj().decodable());
            assert(post_index =~= Map::<LSN, Address>::empty()) by {
                assert forall |lsn| #[trigger] post_index.contains_key(lsn) implies false by {
                    assert(pre_index.contains_key(lsn));
                    assert(start_lsn <= lsn);
                    reveal(TruncatedJournal::index_domain_valid);
                    assert(pre.journal_tj().index_domain_valid(pre_index));
                    assert(pre.journal_tj().seq_start() <= lsn < pre.journal_tj().seq_end());
                }
            };
            assert(post.journal_tj().build_lsn_addr_index() =~= Map::<LSN, Address>::empty());
            assert(post.journal_tj().build_lsn_addr_index() == post_index);
            assert(post.journal_tj().seq_end() == start_lsn);
            assert(cj_unmarshalled_tail(post.journal).seq_start == start_lsn);
            }
        assert(post.valid_journal_structure());
    }

    #[inductive(journal_marshal)]
    fn journal_marshal_inductive(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
        new_cache: Cache::State,
        addr: Address,
        writes: Map<Address, RawPage>,
    )
    {
        // journal changes (new page in lsn_addr_index, tail shortened)
        // cache changes (new dirty entry for marshalled page)
        // disk unchanged
        Cache::State::inv_next(pre.cache, post.cache, Cache::Label::Access{reads: Map::empty(), writes});
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        reveal(ConcreteJournal::State::valid_journal_structure);
        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)};
        let journal_step = choose |step| CachedJournal::State::next_by(pre.journal, new_journal, journal_lbl, step);
        match journal_step {
            CachedJournal::Step::internal_journal_marshal(cut, marshalled_addr) => {
                let marshalled_msgs = cj_unmarshalled_tail(pre.journal).discard_recent(cut);
                assert(marshalled_addr == addr);
                let expected_record = JournalRecord{
                    message_seq: marshalled_msgs,
                    prior_rec: pre.journal.snapshot.freshest_rec,
                };
                assert(journal_lbl->writes == Map::empty().insert(addr, expected_record));
                assert(journal_lbl->writes.contains_key(addr));
                assert(to_journal_records(writes).contains_key(addr));
                assert(journal_lbl->writes[addr] == expected_record);
                assert(to_journal_records(writes)[addr] == expected_record);
                assert(writes.contains_key(addr));
                assert forall |a: Address| writes.contains_key(a) implies a == addr by {
                    assert(to_journal_records(writes).contains_key(a));
                    assert(Map::<Address, JournalRecord>::empty().insert(addr, expected_record).contains_key(a));
                }
                assert forall |a: Address| a == addr implies writes.contains_key(a) by {
                    assert(to_journal_records(writes).contains_key(addr));
                }
                assert(raw_page_to_record(writes[addr]) == expected_record);
                assert(!cj_lsn_addr_index(pre.journal).contains_value(addr));
                assert(!pre.journal_disk_view().entries.contains_key(addr));
                let cache_lbl = Cache::Label::Access{
                    reads: Map::empty(),
                    writes,
                };
                assert(Cache::State::next_by(pre.cache, new_cache, cache_lbl, Cache::Step::access()));
                assert(writes.contains_key(addr));
                assert(pre.cache.valid_write(addr));
                let slot = pre.cache.lookup_map[addr];
                assert(pre.cache.lookup_map.contains_key(addr));
                let restricted_lookup = pre.cache.lookup_map.restrict(writes.dom());
                assert(restricted_lookup.contains_key(addr));
                assert(restricted_lookup[addr] == slot);
                assert(restricted_lookup.values().contains(slot));
                assert(pre.cache.write_updated_entries(writes).contains_key(slot));
                assert(pre.cache.write_updated_status(writes).contains_key(slot));
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.cache.entries[slot] == Entry::Filled{
                    addr,
                    data: writes[addr],
                });
                assert(post.cache.status_map[slot] is Dirty);
                pre.cache.build_lookup_map_ensures();
                post.cache.build_lookup_map_ensures();
                assert(pre.cache.lookup_map == pre.cache.build_lookup_map());
                assert(post.cache.lookup_map == post.cache.build_lookup_map());
                assert(pre.cache.lookup_map.is_injective()) by {
                    assert(pre.cache.build_lookup_map_props(pre.cache.build_lookup_map()));
                };
                assert(post.cache.lookup_map.is_injective()) by {
                    assert(post.cache.build_lookup_map_props(post.cache.build_lookup_map()));
                };
                assert(cj_unmarshalled_tail(post.journal) == cj_unmarshalled_tail(pre.journal).discard_old(cut));
                assert(cj_unmarshalled_tail(post.journal).seq_start == cut);
                let pre_index = cj_lsn_addr_index(pre.journal);
                let post_index = cj_lsn_addr_index(post.journal);
                let start = marshalled_msgs.seq_start;
                let end = marshalled_msgs.seq_end;
                assert(start == cj_unmarshalled_tail(pre.journal).seq_start);
                assert(end == cut);
                assert(start < end);
                pre.journal_tj().build_lsn_addr_index_ensures();
                reveal(TruncatedJournal::index_domain_valid);
                assert(lsn_disjoint(pre_index.dom(), start, end)) by {
                    assert forall |lsn| start <= lsn < end implies !pre_index.dom().contains(lsn) by {
                        assert(pre_index == pre.journal_tj().build_lsn_addr_index());
                        assert(pre.journal_tj().index_domain_valid(pre_index));
                        assert(pre.journal_tj().seq_end() == start);
                    }
                };
                assert(post_index == lsn_addr_index_append_record(pre_index, start, end, addr));
                lsn_addr_index_append_record_ensures(pre_index, start, end, addr);
                assert(post_index.values() == pre_index.values() + set![addr]);
                assert(post_index.contains_value(addr)) by {
                    assert(post_index.contains_key(start));
                    assert(post_index[start] == addr);
                };
                assert(post.journal_live_aus().contains(addr.au)) by {
                    assert(post_index.contains_key(start));
                    assert(post_index[start] == addr);
                    assert(cached_lsn_au_index(post.journal).contains_key(start));
                    assert(cached_lsn_au_index(post.journal)[start] == addr.au);
                };
                assert(post.cache.lookup_map.contains_key(addr));
                assert(post.cache.entries.contains_key(post.cache.lookup_map[addr]));
                assert(post.cache.entries[post.cache.lookup_map[addr]] is Filled);
                assert(post.cache.status_map[post.cache.lookup_map[addr]] is Dirty);
                assert(post.dirty_cache_journal_entries().contains_key(addr));
                assert(post.dirty_cache_journal_entries()[addr] == expected_record);
                assert_maps_equal!(
                    post.journal_disk_view().entries,
                    pre.journal_disk_view().entries.insert(addr, expected_record),
                    a => {
                        if a == addr {
                            assert(post.dirty_cache_journal_entries().contains_key(addr));
                        } else {
                            if post.journal_disk_view().entries.contains_key(a) {
                                if post.dirty_cache_journal_entries().contains_key(a) {
                                    assert(pre.dirty_cache_journal_entries().contains_key(a));
                                } else {
                                    assert(post.disk_journal_entries().contains_key(a));
                                    assert(pre.disk_journal_entries().contains_key(a));
                                }
                            }
                            if pre.journal_disk_view().entries.contains_key(a) {
                                if pre.dirty_cache_journal_entries().contains_key(a) {
                                    assert(post.dirty_cache_journal_entries().contains_key(a));
                                } else {
                                    assert(pre.disk_journal_entries().contains_key(a));
                                    assert(post.disk_journal_entries().contains_key(a));
                                }
                            }
                        }
                    }
                );
                assert(post.journal_tj() == pre.journal_tj().append_record(addr, marshalled_msgs));
                build_lsn_addr_index_commutes_over_append_record(
                    pre.journal_tj().disk_view,
                    pre.journal_tj().freshest_rec,
                    marshalled_msgs,
                    addr,
                );
                let linked_pre = LinkedJournal::State{
                    truncated_journal: pre.journal_tj(),
                    unmarshalled_tail: cj_unmarshalled_tail(pre.journal),
                };
                let linked_post = LinkedJournal::State{
                    truncated_journal: post.journal_tj(),
                    unmarshalled_tail: cj_unmarshalled_tail(post.journal),
                };
                assert(linked_post.truncated_journal == linked_pre.truncated_journal.append_record(addr, marshalled_msgs));
                assert(linked_post.unmarshalled_tail == linked_pre.unmarshalled_tail.discard_old(cut));
                assert(linked_pre.inv());
                reveal(LinkedJournal::State::next_by);
                assert(LinkedJournal::State::next_by(
                    linked_pre,
                    linked_post,
                    LinkedJournal::Label::Internal{},
                    LinkedJournal::Step::internal_journal_marshal(cut, addr),
                ));
                LinkedJournal::State::inv_next(
                    linked_pre,
                    linked_post,
                    LinkedJournal::Label::Internal{},
                    LinkedJournal::Step::internal_journal_marshal(cut, addr),
                );
                assert(linked_post.inv());
                assert(post.journal_tj().decodable());
                post.journal_tj().build_lsn_addr_index_ensures();
                assert(cj_lsn_addr_index(post.journal) == post.journal_tj().build_lsn_addr_index());
            }
            _ => { assert(false); }
        }
        assert(post.valid_journal_structure());
        assert(post.clean_journal_cache_matches_disk()) by {
            assert forall |a: Address, data: RawPage|
                #[trigger] post.cache.valid_read(a, data)
                && post.cache.status_map[post.cache.lookup_map[a]] is Clean
                && post.journal_disk_view().entries.contains_key(a)
            implies post.disk.content.contains_key(a) && post.disk.content[a] == data by {
                let pre_index = cj_lsn_addr_index(pre.journal);
                let post_index = cj_lsn_addr_index(post.journal);
                if a == addr {
                    let slot = pre.cache.lookup_map[addr];
                    assert(post.cache.lookup_map == pre.cache.lookup_map);
                    assert(post.cache.lookup_map[a] == slot);
                    assert(post.cache.status_map[slot] is Dirty);
                    assert(false);
                } else {
                    assert(!writes.contains_key(a));
                    Cache::State::access_unwritten_addr_unchanged(
                        pre.cache,
                        post.cache,
                        Map::empty(),
                        writes,
                        a,
                    );
                    assert(pre.cache.valid_read(a, data));
                    assert(pre.cache.status_map[pre.cache.lookup_map[a]] is Clean);
                    assert(pre.journal_disk_view().entries.contains_key(a));
                    assert(pre.clean_journal_cache_matches_disk());
                }
            }
        }
        cache_access_preserves_outstanding_reqs_consistent(pre, post, Map::empty(), writes);
        assert(post.outstanding_reqs_consistent());
    }

    #[inductive(internal_mini_allocator_fill)]
    fn internal_mini_allocator_fill_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(ConcreteJournal::State::valid_journal_structure);
        assert(post.journal == pre.journal);
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(post.journal_tj() == pre.journal_tj());
        assert(post.valid_journal_structure());
    }

    #[inductive(internal_mini_allocator_prune)]
    fn internal_mini_allocator_prune_inductive(pre: Self, post: Self, lbl: Label) {
        reveal(ConcreteJournal::State::valid_journal_structure);
        assert(post.journal == pre.journal);
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(post.journal_tj() == pre.journal_tj());
        assert(post.valid_journal_structure());
    }

    #[inductive(cache_disk_ops)]
    fn cache_disk_ops_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State, new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>, cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>, disk_responses: Map<ID, DiskResponse>)
    {
        let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
        let disk_lbl = AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
        // inv_next for post.cache.inv(); reveal for post.disk.inv()
        Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step| AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
        match disk_step {
            AsyncDisk::Step::disk_ops() => {
                assert(post.disk.requests == pre.disk.requests.union_prefer_right(disk_requests));
                assert(post.disk.responses == pre.disk.responses.remove_keys(disk_responses.dom()));
                assert(post.disk.content == pre.disk.content);
            }
            _ => {
                assert(false);
            }
        }
        cache_disk_ops_preserves_i(pre, post, new_cache, new_disk, cache_requests, cache_responses, disk_requests, disk_responses);
        valid_journal_structure_preserved_by_i_equal(pre, post);
        assert(post.outstanding_cache_reqs == pre.next_outstanding_cache_reqs(disk_requests, disk_responses));
        assert_sets_equal!(post.disk.requests.dom() + post.disk.responses.dom(), post.outstanding_cache_reqs.dom());
        let old_outstanding = pre.outstanding_cache_reqs.remove_keys(disk_responses.dom());
        let request_addr_map = Map::new(
            |id: ID| disk_requests.contains_key(id),
            |id: ID| disk_requests[id].addr(),
        );
        assert(request_addr_map.is_injective());
        assert(request_addr_map.values().disjoint(pre.outstanding_cache_reqs.values()));
        assert(post.outstanding_cache_reqs == old_outstanding.union_prefer_right(request_addr_map));
        assert(post.outstanding_cache_reqs.is_injective()) by {
            assert forall |x: ID, y: ID|
                x != y
                && post.outstanding_cache_reqs.contains_key(x)
                && post.outstanding_cache_reqs.contains_key(y)
                implies #[trigger] post.outstanding_cache_reqs[x] != #[trigger] post.outstanding_cache_reqs[y] by {
                if request_addr_map.contains_key(x) {
                    assert(post.outstanding_cache_reqs[x] == request_addr_map[x]);
                    assert(request_addr_map.values().contains(request_addr_map[x]));
                    if request_addr_map.contains_key(y) {
                        assert(post.outstanding_cache_reqs[y] == request_addr_map[y]);
                        assert(request_addr_map[x] != request_addr_map[y]);
                    } else {
                        assert(old_outstanding.contains_key(y));
                        assert(post.outstanding_cache_reqs[y] == old_outstanding[y]);
                        assert(pre.outstanding_cache_reqs.contains_key(y));
                        assert(old_outstanding[y] == pre.outstanding_cache_reqs[y]);
                        assert(pre.outstanding_cache_reqs.values().contains(pre.outstanding_cache_reqs[y]));
                    }
                } else {
                    assert(old_outstanding.contains_key(x));
                    assert(post.outstanding_cache_reqs[x] == old_outstanding[x]);
                    assert(pre.outstanding_cache_reqs.contains_key(x));
                    assert(old_outstanding[x] == pre.outstanding_cache_reqs[x]);
                    assert(pre.outstanding_cache_reqs.values().contains(pre.outstanding_cache_reqs[x]));
                    if request_addr_map.contains_key(y) {
                        assert(post.outstanding_cache_reqs[y] == request_addr_map[y]);
                        assert(request_addr_map.values().contains(request_addr_map[y]));
                    } else {
                        assert(old_outstanding.contains_key(y));
                        assert(post.outstanding_cache_reqs[y] == old_outstanding[y]);
                        assert(pre.outstanding_cache_reqs.contains_key(y));
                        assert(old_outstanding[y] == pre.outstanding_cache_reqs[y]);
                        assert(pre.outstanding_cache_reqs[x] != pre.outstanding_cache_reqs[y]);
                    }
                }
            }
        }
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
        assert(post.outstanding_reqs_requests_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
                implies {
                    let req = post.disk.requests[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& req.addr() == addr
                    &&& req is ReadReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& req is WriteReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                if disk_requests.contains_key(id) {
                    let req = disk_requests[id];
                    let addr = req.addr();
                    assert(post.disk.requests[id] == req);
                    assert(request_addr_map.contains_key(id));
                    assert(post.outstanding_cache_reqs[id] == request_addr_map[id]);
                    assert(post.outstanding_cache_reqs[id] == addr);
                    assert(cache_requests.contains(req));
                    match cache_step {
                        Cache::Step::load_initiate(new_slots_mapping) => {
                            assert(req is ReadReq);
                            assert(crate::implementation::Cache_v::addr_maps_to_req(
                                cache_requests,
                                req,
                                addr,
                            ));
                            assert(Cache::State::valid_load_requests(cache_requests, new_slots_mapping));
                            assert(new_slots_mapping.contains_value(addr));
                            Cache::State::invert_contains_pair(new_slots_mapping, addr);
                            let slot = choose |slot: Slot|
                                new_slots_mapping.contains_key(slot)
                                && #[trigger] new_slots_mapping[slot] == addr;
                            assert(new_slots_mapping.invert().contains_pair(addr, slot));
                            assert(new_slots_mapping.invert()[addr] == slot);
                            assert(post.cache.lookup_map.contains_key(addr));
                            assert(post.cache.lookup_map[addr] == slot);
                            let updated_entries = Map::new(
                                |slot| new_slots_mapping.contains_key(slot),
                                |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                            );
                            assert(updated_entries.contains_key(slot));
                            assert(updated_entries[slot] == Entry::Loading{addr});
                            assert(post.cache.entries[slot] == Entry::Loading{addr});
                        }
                        Cache::Step::writeback_initiate() => {
                            assert(req is WriteReq);
                            assert(pre.cache.valid_writeback_requests(cache_requests));
                            assert(pre.cache.lookup_map.contains_key(addr));
                            let slot = pre.cache.lookup_map[addr];
                            assert(pre.cache.entries[slot] == Entry::Filled{addr, data: req->data});
                            let writeback_slots = Map::new(
                                |req: DiskRequest| cache_requests.contains(req),
                                |req: DiskRequest| pre.cache.lookup_map[req->to],
                            ).values();
                            assert(cache_requests.contains(req));
                            assert(Map::new(
                                |req: DiskRequest| cache_requests.contains(req),
                                |req: DiskRequest| pre.cache.lookup_map[req->to],
                            ).contains_key(req));
                            assert(Map::new(
                                |req: DiskRequest| cache_requests.contains(req),
                                |req: DiskRequest| pre.cache.lookup_map[req->to],
                            )[req] == slot);
                            assert(writeback_slots.contains(slot));
                            assert(post.cache.lookup_map == pre.cache.lookup_map);
                            assert(post.cache.entries == pre.cache.entries);
                            assert(post.cache.status_map[slot] is Writeback);
                        }
                        _ => {
                            assert(false);
                        }
                    }
                } else {
                    assert(old_outstanding.contains_key(id));
                    assert(pre.outstanding_cache_reqs.contains_key(id));
                    assert(!disk_responses.contains_key(id));
                    assert(pre.disk.requests.contains_key(id));
                    assert(post.disk.requests[id] == pre.disk.requests[id]);
                    let req = pre.disk.requests[id];
                    let addr = pre.outstanding_cache_reqs[id];
                    assert(pre.outstanding_cache_reqs[id] == old_outstanding[id]);
                    assert(post.outstanding_cache_reqs[id] == old_outstanding[id]);
                    cache_response_absent_for_unresponded_outstanding(
                        pre,
                        cache_responses,
                        disk_responses,
                        id,
                    );
                    cache_disk_ops_preserves_pending_slot(
                        pre.cache,
                        post.cache,
                        cache_requests,
                        cache_responses,
                        addr,
                    );
                }
            }
        }
        assert(post.outstanding_reqs_responses_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id)
                implies {
                    let resp = post.disk.responses[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& resp is ReadResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& resp->data == post.disk.content[addr]
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& resp is WriteResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: post.disk.content[addr]}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                assert(pre.disk.responses.contains_key(id));
                assert(!disk_responses.contains_key(id));
                assert(old_outstanding.contains_key(id));
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(post.disk.responses[id] == pre.disk.responses[id]);
                assert(post.disk.content == pre.disk.content);
                let resp = pre.disk.responses[id];
                let addr = pre.outstanding_cache_reqs[id];
                assert(pre.outstanding_cache_reqs[id] == old_outstanding[id]);
                assert(post.outstanding_cache_reqs[id] == old_outstanding[id]);
                cache_response_absent_for_unresponded_outstanding(
                    pre,
                    cache_responses,
                    disk_responses,
                    id,
                );
                cache_disk_ops_preserves_pending_slot(
                    pre.cache,
                    post.cache,
                    cache_requests,
                    cache_responses,
                    addr,
                );
            }
        }
        assert forall |id: ID|
            #![trigger post.disk.requests.contains_key(id)]
            #![trigger post.disk.responses.contains_key(id)]
            (post.disk.requests.contains_key(id) || post.disk.responses.contains_key(id))
            implies post.io_id_valid(id) by {
            if disk_requests.contains_key(id) {
                let req = disk_requests[id];
                let addr = req.addr();
                assert(request_addr_map.contains_key(id));
                assert(post.outstanding_cache_reqs[id] == addr);
                assert(cache_requests.contains(req));
                match cache_step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(req is ReadReq);
                        assert(crate::implementation::Cache_v::addr_maps_to_req(
                            cache_requests,
                            req,
                            addr,
                        ));
                        assert(Cache::State::valid_load_requests(cache_requests, new_slots_mapping));
                        assert(new_slots_mapping.contains_value(addr));
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        let slot = choose |slot: Slot|
                            new_slots_mapping.contains_key(slot)
                            && #[trigger] new_slots_mapping[slot] == addr;
                        assert(new_slots_mapping.invert().contains_pair(addr, slot));
                        assert(new_slots_mapping.invert()[addr] == slot);
                        assert(post.cache.lookup_map.contains_key(addr));
                        assert(post.cache.lookup_map[addr] == slot);
                        let updated_entries = Map::new(
                            |slot| new_slots_mapping.contains_key(slot),
                            |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                        );
                        assert(updated_entries.contains_key(slot));
                        assert(updated_entries[slot] == Entry::Loading{addr});
                        assert(post.cache.entries[slot] == Entry::Loading{addr});
                        assert(post.cache.entries.contains_key(slot));
                        assert(post.cache.inv());
                        assert(post.cache.status_map.dom() =~= post.cache.entries.dom());
                        assert(post.cache.status_map.contains_key(slot));
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                    Cache::Step::writeback_initiate() => {
                        assert(req is WriteReq);
                        assert(pre.cache.valid_writeback_requests(cache_requests));
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                        assert(post.cache.entries == pre.cache.entries);
                        assert(pre.cache.lookup_map.contains_key(addr));
                        assert(post.cache.lookup_map.contains_key(addr));
                        let slot = pre.cache.lookup_map[addr];
                        assert(post.cache.lookup_map[addr] == slot);
                        cache_lookup_gets_addr(pre.cache, addr);
                        assert(pre.cache.entries.contains_key(slot));
                        assert(post.cache.entries.contains_key(slot));
                        assert(post.cache.inv());
                        assert(post.cache.status_map.dom() =~= post.cache.entries.dom());
                        assert(post.cache.status_map.contains_key(slot));
                    }
                    _ => {
                        assert(false);
                    }
                }
            } else {
                assert(old_outstanding.contains_key(id));
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(!disk_responses.contains_key(id));
                let addr = pre.outstanding_cache_reqs[id];
                cache_response_absent_for_unresponded_outstanding(
                    pre,
                    cache_responses,
                    disk_responses,
                    id,
                );
                cache_disk_ops_preserves_pending_slot(
                    pre.cache,
                    post.cache,
                    cache_requests,
                    cache_responses,
                    addr,
                );
                assert(post.outstanding_cache_reqs[id] == addr);
                assert(pre.io_id_valid(id));
                assert(post.cache.lookup_map.contains_key(addr));
                cache_lookup_gets_addr(post.cache, addr);
                if post.disk.requests.contains_key(id) {
                    assert(pre.disk.requests.contains_key(id));
                    let req = pre.disk.requests[id];
                    if req is ReadReq {
                        assert(pre.disk.content.contains_key(addr));
                        assert(post.disk.content.contains_key(addr));
                    }
                } else {
                    assert(post.disk.responses.contains_key(id));
                    assert(pre.disk.responses.contains_key(id));
                    assert(pre.disk.content.contains_key(addr));
                    assert(post.disk.content.contains_key(addr));
                }
            }
            assert(post.outstanding_cache_reqs.contains_key(id));
            assert(post.cache.lookup_map.contains_key(post.outstanding_cache_reqs[id]));
            cache_lookup_gets_addr(post.cache, post.outstanding_cache_reqs[id]);
            assert(post.cache.entries.contains_key(post.cache.lookup_map[post.outstanding_cache_reqs[id]]));
            assert(post.cache.status_map.contains_key(post.cache.lookup_map[post.outstanding_cache_reqs[id]]));
        }
        assert(post.clean_journal_cache_matches_disk()) by {
            assert forall |a: Address, data: RawPage|
                #[trigger] post.cache.valid_read(a, data)
                && post.cache.status_map[post.cache.lookup_map[a]] is Clean
                && post.journal_disk_view().entries.contains_key(a)
            implies post.disk.content.contains_key(a) && post.disk.content[a] == data by {
                match cache_step {
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        let updated_entries = Map::new(
                            |slot| new_slots_mapping.contains_key(slot),
                            |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                        );
                        assert(!new_slots_mapping.invert().contains_key(a)) by {
                            if new_slots_mapping.invert().contains_key(a) {
                                reveal(Map::invert);
                                assert(new_slots_mapping.contains_value(a));
                                Cache::State::invert_contains_pair(new_slots_mapping, a);
                                let slot = new_slots_mapping.invert()[a];
                                assert(new_slots_mapping.contains_pair(slot, a));
                                assert(new_slots_mapping.contains_key(slot));
                                assert(post.cache.lookup_map[a] == slot);
                                assert(post.cache.entries[slot] == Entry::Loading{addr: a});
                                assert(false);
                            }
                        }
                        assert(post.cache.lookup_map
                            == pre.cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                        assert(pre.cache.lookup_map.contains_key(a));
                        assert(post.cache.lookup_map[a] == pre.cache.lookup_map[a]);
                        let slot = pre.cache.lookup_map[a];
                        cache_lookup_gets_addr(pre.cache, a);
                        assert(post.cache.lookup_map[a] == slot);
                        assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                        assert(!updated_entries.contains_key(slot)) by {
                            if updated_entries.contains_key(slot) {
                                assert(post.cache.entries[slot] == updated_entries[slot]);
                                assert(updated_entries[slot] is Loading);
                                assert(false);
                            }
                        }
                        assert(pre.cache.entries.contains_key(slot));
                        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                        assert(post.cache.status_map == pre.cache.status_map);
                        assert(pre.cache.valid_read(a, data));
                        assert(pre.cache.status_map[pre.cache.lookup_map[a]] is Clean);
                        assert(pre.clean_journal_cache_matches_disk());
                    }
                    Cache::Step::load_complete() => {
                        assert(cache_requests.is_empty());
                        assert(pre.cache.valid_load_responses(cache_responses));
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                        let restricted_lookup = pre.cache.lookup_map.restrict(cache_responses.dom());
                        let slot_addr_map = restricted_lookup.invert();
                        let updated_entries = Map::new(
                            |slot| slot_addr_map.contains_key(slot),
                            |slot| Entry::Filled{
                                addr: slot_addr_map[slot],
                                data: cache_responses[slot_addr_map[slot]]->data,
                            },
                        );
                        let updated_status_map = Map::new(
                            |slot| slot_addr_map.contains_key(slot),
                            |slot| Status::Clean,
                        );
                        if cache_responses.contains_key(a) {
                            read_response_matches_outstanding_disk(pre, cache_responses, disk_responses, a);
                            assert(cache_responses[a] is ReadResp);
                            let slot = pre.cache.lookup_map[a];
                            assert(restricted_lookup.contains_key(a));
                            assert(restricted_lookup[a] == slot);
                            assert(restricted_lookup.contains_value(slot));
                            Cache::State::invert_contains_pair(restricted_lookup, slot);
                            assert(slot_addr_map.contains_key(slot));
                            let resp_addr = slot_addr_map[slot];
                            assert(restricted_lookup.contains_pair(resp_addr, slot));
                            assert(restricted_lookup.contains_pair(a, slot));
                            pre.cache.build_lookup_map_ensures();
                            assert(pre.cache.lookup_map.is_injective());
                            assert(resp_addr == a);
                            assert(slot_addr_map[slot] == a);
                            assert(updated_entries.contains_key(slot));
                            assert(updated_entries[slot] == Entry::Filled{addr: a, data: cache_responses[a]->data});
                            assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                            assert(post.cache.entries[slot] == updated_entries[slot]);
                            assert(post.cache.entries[post.cache.lookup_map[a]]
                                == Entry::Filled{addr: a, data: cache_responses[a]->data});
                            assert(data == cache_responses[a]->data);
                            assert(post.disk.content == pre.disk.content);
                        } else {
                            let slot = pre.cache.lookup_map[a];
                            cache_lookup_gets_addr(pre.cache, a);
                            assert(!slot_addr_map.contains_key(slot)) by {
                                if slot_addr_map.contains_key(slot) {
                                    Cache::State::invert_contains_pair(
                                        restricted_lookup,
                                        slot,
                                    );
                                    let resp_addr = slot_addr_map[slot];
                                    assert(restricted_lookup.contains_pair(resp_addr, slot));
                                    assert(cache_responses.contains_key(resp_addr));
                                    assert(pre.cache.lookup_map[resp_addr] == slot);
                                    pre.cache.build_lookup_map_ensures();
                                    assert(pre.cache.lookup_map.is_injective());
                                    assert(resp_addr == a);
                                    assert(false);
                                }
                            }
                            assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                            assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                            assert(!updated_entries.contains_key(slot));
                            assert(!updated_status_map.contains_key(slot));
                            assert(pre.cache.entries.contains_key(slot));
                            assert(pre.cache.status_map.contains_key(slot));
                            assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                            assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                            assert(pre.cache.valid_read(a, data));
                            assert(pre.cache.status_map[pre.cache.lookup_map[a]] is Clean);
                            assert(pre.clean_journal_cache_matches_disk());
                            assert(post.disk.content == pre.disk.content);
                        }
                    }
                    Cache::Step::writeback_initiate() => {
                        let request_slot_map = Map::new(
                            |req: DiskRequest| cache_requests.contains(req),
                            |req: DiskRequest| pre.cache.lookup_map[req->to],
                        );
                        let writeback_slots = request_slot_map.values();
                        let updated_status_map = Map::new(
                            |slot| writeback_slots.contains(slot),
                            |slot| Status::Writeback{},
                        );
                        let slot = post.cache.lookup_map[a];
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                        assert(post.cache.entries == pre.cache.entries);
                        assert(pre.cache.lookup_map.contains_key(a));
                        cache_lookup_gets_addr(pre.cache, a);
                        assert(!writeback_slots.contains(slot)) by {
                            if writeback_slots.contains(slot) {
                                let req = choose |req: DiskRequest|
                                    request_slot_map.contains_key(req)
                                    && #[trigger] request_slot_map[req] == slot;
                                assert(cache_requests.contains(req));
                                assert(post.cache.status_map[slot] is Writeback);
                                assert(false);
                            }
                        }
                        assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                        assert(!updated_status_map.contains_key(slot));
                        assert(pre.cache.status_map.contains_key(slot));
                        assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                        assert(pre.cache.valid_read(a, data));
                        assert(pre.cache.status_map[pre.cache.lookup_map[a]] is Clean);
                        assert(pre.clean_journal_cache_matches_disk());
                        assert(post.disk.content == pre.disk.content);
                    }
                    Cache::Step::writeback_complete() => {
                        assert(cache_requests.is_empty());
                        assert(pre.cache.valid_writeback_responses(cache_responses));
                        assert(post.cache.lookup_map == pre.cache.lookup_map);
                        assert(post.cache.entries == pre.cache.entries);
                        let resps_slots = pre.cache.lookup_map.restrict(cache_responses.dom()).values();
                        let updated_status_map = Map::new(
                            |slot| resps_slots.contains(slot),
                            |slot| Status::Clean,
                        );
                        if cache_responses.contains_key(a) {
                            assert(cache_responses[a] is WriteResp);
                            writeback_response_matches_outstanding_disk(pre, cache_responses, disk_responses, a);
                            assert(pre.cache.entries[pre.cache.lookup_map[a]]
                                == Entry::Filled{addr: a, data: pre.disk.content[a]});
                            assert(post.cache.entries[post.cache.lookup_map[a]]
                                == Entry::Filled{addr: a, data: pre.disk.content[a]});
                            assert(data == pre.disk.content[a]);
                            assert(post.disk.content == pre.disk.content);
                        } else {
                            let slot = pre.cache.lookup_map[a];
                            cache_lookup_gets_addr(pre.cache, a);
                            assert(!resps_slots.contains(slot)) by {
                                if resps_slots.contains(slot) {
                                    let resp_addr = choose |addr: Address|
                                        pre.cache.lookup_map.restrict(cache_responses.dom()).contains_key(addr)
                                        && #[trigger] pre.cache.lookup_map.restrict(cache_responses.dom())[addr] == slot;
                                    assert(cache_responses.contains_key(resp_addr));
                                    pre.cache.build_lookup_map_ensures();
                                    assert(pre.cache.lookup_map.is_injective());
                                    assert(resp_addr == a);
                                    assert(false);
                                }
                            }
                            assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                            assert(!updated_status_map.contains_key(slot));
                            assert(pre.cache.status_map.contains_key(slot));
                            assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                            assert(pre.cache.valid_read(a, data));
                            assert(pre.cache.status_map[pre.cache.lookup_map[a]] is Clean);
                            assert(pre.clean_journal_cache_matches_disk());
                            assert(post.disk.content == pre.disk.content);
                        }
                    }
                    _ => {
                        assert(false);
                    }
                }
            }
        }
        assert(post.outstanding_reqs_consistent());
    }

    #[inductive(cache_internal)]
    fn cache_internal_inductive(pre: Self, post: Self, lbl: Label, new_cache: Cache::State)
    {
        let cache_lbl = Cache::Label::Internal{};
        Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
        cache_internal_preserves_i(pre, post, new_cache);
        valid_journal_structure_preserved_by_i_equal(pre, post);
        assert(post.disk == pre.disk);
        assert(post.outstanding_cache_reqs == pre.outstanding_cache_reqs);
        assert(post.outstanding_reqs_requests_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
                implies {
                    let req = post.disk.requests[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& req.addr() == addr
                    &&& req is ReadReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& req is WriteReq ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                let req = pre.disk.requests[id];
                let addr = pre.outstanding_cache_reqs[id];
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(pre.disk.requests[id] == post.disk.requests[id]);
                if req is ReadReq {
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                    assert(pre.io_id_valid(id));
                    cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
                } else {
                    assert(req is WriteReq);
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]]
                        == Entry::Filled{addr, data: req->data});
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback);
                    assert(pre.io_id_valid(id));
                    cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
                }
            }
        }
        assert(post.outstanding_reqs_responses_ok()) by {
            assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id)
                implies {
                    let resp = post.disk.responses[id];
                    let addr = post.outstanding_cache_reqs[id];
                    &&& post.outstanding_cache_reqs.contains_key(id)
                    &&& resp is ReadResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& resp->data == post.disk.content[addr]
                        &&& post.cache.entries[slot] is Loading
                    }
                    &&& resp is WriteResp ==> {
                        let slot = post.cache.lookup_map[addr];
                        &&& post.cache.entries[slot] == Entry::Filled{addr, data: post.disk.content[addr]}
                        &&& post.cache.status_map[slot] is Writeback
                    }
                } by {
                let resp = pre.disk.responses[id];
                let addr = pre.outstanding_cache_reqs[id];
                assert(pre.outstanding_cache_reqs.contains_key(id));
                assert(pre.disk.responses[id] == post.disk.responses[id]);
                if resp is ReadResp {
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                    assert(pre.io_id_valid(id));
                    cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
                } else {
                    assert(resp is WriteResp);
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]]
                        == Entry::Filled{addr, data: pre.disk.content[addr]});
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback);
                    assert(pre.io_id_valid(id));
                    cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
                }
            }
        }
        assert forall |id: ID|
            #![trigger post.disk.requests.contains_key(id)]
            #![trigger post.disk.responses.contains_key(id)]
            (post.disk.requests.contains_key(id) || post.disk.responses.contains_key(id))
            implies post.io_id_valid(id) by {
            let addr = pre.outstanding_cache_reqs[id];
            assert(pre.io_id_valid(id));
            if post.disk.requests.contains_key(id) {
                let req = pre.disk.requests[id];
                if req is ReadReq {
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                } else {
                    assert(req is WriteReq);
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback);
                }
            } else {
                let resp = pre.disk.responses[id];
                if resp is ReadResp {
                    assert(pre.cache.entries[pre.cache.lookup_map[addr]] is Loading);
                } else {
                    assert(resp is WriteResp);
                    assert(pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback);
                }
            }
            cache_internal_preserves_pending_slot(pre.cache, post.cache, addr);
            assert(post.cache.lookup_map.contains_key(addr));
            cache_lookup_gets_addr(post.cache, addr);
        }
        assert(post.clean_journal_cache_matches_disk()) by {
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
            let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
            assert forall |a: Address, data: RawPage|
                #[trigger] post.cache.valid_read(a, data)
                && post.cache.status_map[post.cache.lookup_map[a]] is Clean
                && post.journal_disk_view().entries.contains_key(a)
            implies post.disk.content.contains_key(a) && post.disk.content[a] == data by {
                match cache_step {
                    Cache::Step::reserve(new_slots_mapping) => {
                        let updated_entries = Map::new(
                            |slot| new_slots_mapping.contains_key(slot),
                            |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                        );
                        assert(!new_slots_mapping.invert().contains_key(a)) by {
                            if new_slots_mapping.invert().contains_key(a) {
                                reveal(Map::invert);
                                assert(new_slots_mapping.contains_value(a));
                                Cache::State::invert_contains_pair(new_slots_mapping, a);
                                let slot = new_slots_mapping.invert()[a];
                                assert(new_slots_mapping.contains_pair(slot, a));
                                assert(new_slots_mapping.contains_key(slot));
                                assert(post.cache.lookup_map[a] == slot);
                                assert(post.cache.entries[slot] == Entry::Reserved{addr: a});
                                assert(false);
                            }
                        }
                        assert(post.cache.lookup_map
                            == pre.cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                        assert(pre.cache.lookup_map.contains_key(a));
                        assert(post.cache.lookup_map[a] == pre.cache.lookup_map[a]);
                        let slot = pre.cache.lookup_map[a];
                        cache_lookup_gets_addr(pre.cache, a);
                        assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                        assert(!updated_entries.contains_key(slot)) by {
                            if updated_entries.contains_key(slot) {
                                assert(post.cache.entries[slot] == updated_entries[slot]);
                                assert(updated_entries[slot] is Reserved);
                                assert(false);
                            }
                        }
                        assert(pre.cache.entries.contains_key(slot));
                        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                        assert(post.cache.status_map == pre.cache.status_map);
                        assert(pre.cache.valid_read(a, data));
                        assert(pre.cache.status_map[pre.cache.lookup_map[a]] is Clean);
                        assert(pre.clean_journal_cache_matches_disk());
                    }
                    Cache::Step::evict(evicted_slots) => {
                        let evicted_addrs = Map::new(
                            |slot| evicted_slots.contains(slot),
                            |slot| pre.cache.entries[slot].get_addr(),
                        ).values();
                        assert(pre.cache.lookup_map.contains_key(a));
                        assert(!evicted_addrs.contains(a));
                        let slot = pre.cache.lookup_map[a];
                        cache_lookup_gets_addr(pre.cache, a);
                        assert(!evicted_slots.contains(slot)) by {
                            if evicted_slots.contains(slot) {
                                assert(evicted_addrs.contains(a)) by {
                                    assert(Map::new(
                                        |slot| evicted_slots.contains(slot),
                                        |slot| pre.cache.entries[slot].get_addr(),
                                    ).contains_key(slot));
                                    cache_lookup_gets_addr(pre.cache, a);
                                    assert(pre.cache.entries[slot].get_addr() == a);
                                }
                                assert(false);
                            }
                        }
                        assert(post.cache.lookup_map[a] == slot);
                        let updated_entries = Map::new(|slot| evicted_slots.contains(slot), |slot| Entry::Empty);
                        let updated_status_map = Map::new(|slot| evicted_slots.contains(slot), |slot| Status::NotFilled);
                        assert(post.cache.entries == pre.cache.entries.union_prefer_right(updated_entries));
                        assert(post.cache.status_map == pre.cache.status_map.union_prefer_right(updated_status_map));
                        assert(!updated_entries.contains_key(slot));
                        assert(!updated_status_map.contains_key(slot));
                        assert(pre.cache.entries.contains_key(slot));
                        assert(pre.cache.status_map.contains_key(slot));
                        assert(post.cache.entries[slot] == pre.cache.entries[slot]);
                        assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                        assert(pre.cache.valid_read(a, data));
                        assert(pre.cache.status_map[pre.cache.lookup_map[a]] is Clean);
                        assert(pre.clean_journal_cache_matches_disk());
                    }
                    Cache::Step::noop() => {
                        assert(post.cache == pre.cache);
                        assert(pre.clean_journal_cache_matches_disk());
                    }
                    _ => {
                        assert(false);
                    }
                }
            }
        }
        assert(post.outstanding_reqs_consistent());
    }

    #[inductive(disk_internal)]
    fn disk_internal_inductive(pre: Self, post: Self, lbl: Label, new_disk: AsyncDisk::State)
    {
        // reveal for post.disk.inv()
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        disk_internal_preserves_i(pre, post, new_disk);
        valid_journal_structure_preserved_by_i_equal(pre, post);
        async_disk_internal_pending_dom_preserved(pre.disk, post.disk);
        assert(post.outstanding_reqs_consistent());
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self, disk: AsyncDisk::State, cache: Cache::State,
        journal: CachedJournal::State)
    {
        reveal(ConcreteJournal::State::valid_journal_structure);
        assert(post.valid_journal_structure());
        assert(post.disk.requests.dom() =~= Set::<ID>::empty());
        assert(post.disk.responses.dom() =~= Set::<ID>::empty());
        assert(post.disk.requests.dom() + post.disk.responses.dom() =~= Set::<ID>::empty());
        assert(post.outstanding_cache_reqs.dom() =~= Set::<ID>::empty());
        assert(post.outstanding_reqs_consistent());
    }

    pub proof fn put_inv_next(pre: Self, post: Self, lbl: Label, new_journal: CachedJournal::State)
        requires
            pre.inv(),
            Self::put(pre, post, lbl, new_journal),
        ensures
            post.inv(),
    {
        reveal(ConcreteJournal::State::put);
        Self::put_inductive(pre, post, lbl, new_journal);
    }

    pub proof fn journal_marshal_inv_next(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
        new_cache: Cache::State,
        addr: Address,
        writes: Map<Address, RawPage>,
    )
        requires
            pre.inv(),
            Self::journal_marshal(pre, post, lbl, new_journal, new_cache, addr, writes),
        ensures
            post.inv(),
    {
        reveal(ConcreteJournal::State::journal_marshal);
        Self::journal_marshal_inductive(pre, post, lbl, new_journal, new_cache, addr, writes);
    }

    pub proof fn journal_marshal_full_disk_effect(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
        new_cache: Cache::State,
        addr: Address,
        writes: Map<Address, RawPage>,
        cut: LSN,
    )
        requires
            pre.inv(),
            Self::journal_marshal(pre, post, lbl, new_journal, new_cache, addr, writes),
            CachedJournal::State::next_by(
                pre.journal,
                new_journal,
                CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)},
                CachedJournal::Step::internal_journal_marshal(cut, addr),
            ),
        ensures ({
            let marshalled_msgs = cj_unmarshalled_tail(pre.journal).discard_recent(cut);
            &&& post.journal_tj() == pre.journal_tj().append_record(addr, marshalled_msgs)
            &&& cj_unmarshalled_tail(post.journal) == cj_unmarshalled_tail(pre.journal).discard_old(cut)
            &&& cj_lsn_addr_index(post.journal) == lsn_addr_index_append_record(
                cj_lsn_addr_index(pre.journal),
                marshalled_msgs.seq_start,
                marshalled_msgs.seq_end,
                addr,
            )
        })
    {
        reveal(ConcreteJournal::State::journal_marshal);
        reveal(CachedJournal::State::next_by);
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        reveal(ConcreteJournal::State::valid_journal_structure);

        let marshalled_msgs = cj_unmarshalled_tail(pre.journal).discard_recent(cut);
        let expected_record = JournalRecord{
            message_seq: marshalled_msgs,
            prior_rec: pre.journal.snapshot.freshest_rec,
        };
        let journal_lbl = CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)};
        assert(journal_lbl->writes == Map::empty().insert(addr, expected_record));
        assert(journal_lbl->writes.contains_key(addr));
        assert(to_journal_records(writes).contains_key(addr));
        assert(journal_lbl->writes[addr] == expected_record);
        assert(to_journal_records(writes)[addr] == expected_record);
        assert(writes.contains_key(addr));
        assert forall |a: Address| writes.contains_key(a) implies a == addr by {
            assert(to_journal_records(writes).contains_key(a));
            assert(Map::<Address, JournalRecord>::empty().insert(addr, expected_record).contains_key(a));
        }
        assert(raw_page_to_record(writes[addr]) == expected_record);

        let cache_lbl = Cache::Label::Access{
            reads: Map::empty(),
            writes,
        };
        Cache::State::inv_next(pre.cache, post.cache, cache_lbl);
        assert(Cache::State::next_by(pre.cache, new_cache, cache_lbl, Cache::Step::access()));
        assert(pre.cache.valid_write(addr));
        let slot = pre.cache.lookup_map[addr];
        assert(pre.cache.lookup_map.contains_key(addr));
        let restricted_lookup = pre.cache.lookup_map.restrict(writes.dom());
        assert(restricted_lookup.contains_key(addr));
        assert(restricted_lookup[addr] == slot);
        assert(restricted_lookup.values().contains(slot));
        assert(pre.cache.write_updated_entries(writes).contains_key(slot));
        assert(pre.cache.write_updated_status(writes).contains_key(slot));
        assert(post.cache.lookup_map == pre.cache.lookup_map);
        assert(post.cache.entries[slot] == Entry::Filled{
            addr,
            data: writes[addr],
        });
        assert(post.cache.status_map[slot] is Dirty);
        pre.cache.build_lookup_map_ensures();
        post.cache.build_lookup_map_ensures();
        assert(pre.cache.lookup_map == pre.cache.build_lookup_map());
        assert(post.cache.lookup_map == post.cache.build_lookup_map());
        assert(pre.cache.lookup_map.is_injective()) by {
            assert(pre.cache.build_lookup_map_props(pre.cache.build_lookup_map()));
        };
        assert(post.cache.lookup_map.is_injective()) by {
            assert(post.cache.build_lookup_map_props(post.cache.build_lookup_map()));
        };

        assert(cj_unmarshalled_tail(post.journal) == cj_unmarshalled_tail(pre.journal).discard_old(cut));
        assert(cj_lsn_addr_index(post.journal) == lsn_addr_index_append_record(
            cj_lsn_addr_index(pre.journal),
            marshalled_msgs.seq_start,
            marshalled_msgs.seq_end,
            addr,
        ));
        assert(post.cache.lookup_map.contains_key(addr));
        assert(post.cache.entries.contains_key(post.cache.lookup_map[addr]));
        assert(post.cache.entries[post.cache.lookup_map[addr]] is Filled);
        assert(post.cache.status_map[post.cache.lookup_map[addr]] is Dirty);
        assert(post.dirty_cache_journal_entries().contains_key(addr));
        assert(post.dirty_cache_journal_entries()[addr] == expected_record);
        assert_maps_equal!(
            post.journal_disk_view().entries,
            pre.journal_disk_view().entries.insert(addr, expected_record),
            a => {
                if a == addr {
                    assert(post.dirty_cache_journal_entries().contains_key(addr));
                } else {
                    if post.journal_disk_view().entries.contains_key(a) {
                        if post.dirty_cache_journal_entries().contains_key(a) {
                            assert(pre.dirty_cache_journal_entries().contains_key(a));
                        } else {
                            assert(post.disk_journal_entries().contains_key(a));
                            assert(pre.disk_journal_entries().contains_key(a));
                        }
                    }
                    if pre.journal_disk_view().entries.contains_key(a) {
                        if pre.dirty_cache_journal_entries().contains_key(a) {
                            assert(post.dirty_cache_journal_entries().contains_key(a));
                        } else {
                            assert(pre.disk_journal_entries().contains_key(a));
                            assert(post.disk_journal_entries().contains_key(a));
                        }
                    }
                }
            }
        );
        assert(post.journal_tj() == pre.journal_tj().append_record(addr, marshalled_msgs));
    }

    pub proof fn discard_old_inv_next(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
        discard_addrs: Set<Address>,
    )
        requires
            pre.inv(),
            Self::discard_old(pre, post, lbl, new_journal, discard_addrs),
        ensures
            post.inv(),
    {
        reveal(ConcreteJournal::State::discard_old);
        Self::discard_old_inductive(pre, post, lbl, new_journal, discard_addrs);
    }

    pub proof fn discard_old_full_disk_effect(
        pre: Self,
        post: Self,
        lbl: Label,
        new_journal: CachedJournal::State,
        discard_addrs: Set<Address>,
    )
        requires
            pre.inv(),
            Self::discard_old(pre, post, lbl, new_journal, discard_addrs),
        ensures ({
            let start_lsn = lbl->start_lsn;
            let pre_index = cj_lsn_addr_index(pre.journal);
            let post_index = cj_lsn_addr_index(post.journal);
            &&& cj_unmarshalled_tail(post.journal)
                == cj_unmarshalled_tail(pre.journal).bounded_discard(start_lsn)
            &&& post_index == lsn_addr_index_discard_up_to(pre_index, start_lsn)
            &&& start_lsn < pre.journal_tj().seq_end() ==>
                pre.journal_tj().discard_old_cond(start_lsn, post_index.values(), post.journal_tj())
            &&& pre.journal_tj().seq_end() <= start_lsn ==> {
                &&& post.journal_tj().freshest_rec is None
                &&& post.journal_tj().disk_view == pre.journal_tj().disk_view.discard_old(start_lsn)
                &&& post.journal_tj().build_lsn_addr_index() =~= Map::<LSN, Address>::empty()
            }
        })
    {
        reveal(ConcreteJournal::State::discard_old);
        reveal(CachedJournal::State::next);
        reveal(CachedJournal::State::next_by);
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        reveal(ConcreteJournal::State::valid_journal_structure);

        let start_lsn = lbl->start_lsn;
        let pre_index = cj_lsn_addr_index(pre.journal);
        let post_index = cj_lsn_addr_index(post.journal);
        assert(post.cache == pre.cache);
        assert(post.disk == pre.disk);
        assert(cj_unmarshalled_tail(post.journal)
            == cj_unmarshalled_tail(pre.journal).bounded_discard(start_lsn));
        assert(post_index == lsn_addr_index_discard_up_to(pre_index, start_lsn));
        lsn_addr_index_discard_up_to_ensures(pre_index, start_lsn);
        assert(post_index <= pre_index);
        assert(post_index.values() <= pre_index.values()) by {
            assert forall |a: Address| #[trigger] post_index.values().contains(a)
                implies pre_index.values().contains(a) by {
                let lsn = choose |lsn| post_index.contains_key(lsn) && post_index[lsn] == a;
                assert(pre_index.contains_key(lsn));
                assert(pre_index[lsn] == a);
            }
        };
        pre.journal_tj().build_lsn_addr_index_ensures();

        if start_lsn < pre.journal_tj().seq_end() {
            assert(pre.journal_tj().can_discard_to(start_lsn)) by {
                assert(pre.journal_tj().wf());
                assert(pre.journal_tj().seq_start() == pre.journal_tj().disk_view.boundary_lsn);
                assert(pre.journal_tj().seq_start() == cj_boundary_lsn(pre.journal));
                assert(pre.journal_tj().seq_end() == cj_unmarshalled_tail(pre.journal).seq_start);
            };
            pre.journal_tj().discard_old_decodable(start_lsn);
            assert(pre.journal_tj().disk_view.index_keys_map_to_valid_entries(pre_index));
            assert(post_index.values() <= post.journal_tj().disk_view.entries.dom()) by {
                assert forall |a: Address| #[trigger] post_index.values().contains(a)
                    implies post.journal_tj().disk_view.entries.dom().contains(a) by {
                    assert(pre_index.values().contains(a));
                    let lsn = choose |lsn| pre_index.contains_key(lsn) && pre_index[lsn] == a;
                    reveal(DiskView::index_keys_map_to_valid_entries);
                    assert(pre.journal_tj().disk_view.entries.contains_key(a));
                }
            };
            assert(pre.journal_tj().discard_old_cond(start_lsn, post_index.values(), post.journal_tj()));
        } else {
            assert(pre.journal_tj().seq_start() <= start_lsn) by {
                assert(pre.journal_tj().seq_start() == cj_boundary_lsn(pre.journal));
            };
            assert(cj_freshest_rec(post.journal) is None);
            assert(post.journal_tj().freshest_rec is None);
            assert(post.journal_tj().disk_view
                == pre.journal_tj().disk_view.discard_old(start_lsn));
            pre.journal_tj().disk_view.boundary_advance_preserves_wf(start_lsn);
            pre.journal_tj().disk_view.boundary_advance_preserves_acyclic(start_lsn);
            assert(post.journal_tj().decodable());
            assert(post_index =~= Map::<LSN, Address>::empty()) by {
                assert forall |lsn| #[trigger] post_index.contains_key(lsn) implies false by {
                    assert(pre_index.contains_key(lsn));
                    assert(start_lsn <= lsn);
                    reveal(TruncatedJournal::index_domain_valid);
                    assert(pre.journal_tj().index_domain_valid(pre_index));
                    assert(pre.journal_tj().seq_start() <= lsn < pre.journal_tj().seq_end());
                }
            }
            assert(post.journal_tj().build_lsn_addr_index() =~= Map::<LSN, Address>::empty());
        }
    }

    pub proof fn cache_disk_ops_inv_next(
        pre: Self,
        post: Self,
        lbl: Label,
        new_cache: Cache::State,
        new_disk: AsyncDisk::State,
        cache_requests: Set<DiskRequest>,
        cache_responses: Map<Address, DiskResponse>,
        disk_requests: Map<ID, DiskRequest>,
        disk_responses: Map<ID, DiskResponse>,
    )
        requires
            pre.inv(),
            Self::cache_disk_ops(
                pre,
                post,
                lbl,
                new_cache,
                new_disk,
                cache_requests,
                cache_responses,
                disk_requests,
                disk_responses,
            ),
        ensures
            post.inv(),
    {
        reveal(ConcreteJournal::State::cache_disk_ops);
        Self::cache_disk_ops_inductive(
            pre,
            post,
            lbl,
            new_cache,
            new_disk,
            cache_requests,
            cache_responses,
            disk_requests,
            disk_responses,
        );
    }

    pub proof fn cache_internal_inv_next(
        pre: Self,
        post: Self,
        lbl: Label,
        new_cache: Cache::State,
    )
        requires
            pre.inv(),
            Self::cache_internal(pre, post, lbl, new_cache),
        ensures
            post.inv(),
    {
        reveal(ConcreteJournal::State::cache_internal);
        Self::cache_internal_inductive(pre, post, lbl, new_cache);
    }

    pub proof fn disk_internal_inv_next(
        pre: Self,
        post: Self,
        lbl: Label,
        new_disk: AsyncDisk::State,
    )
        requires
            pre.inv(),
            Self::disk_internal(pre, post, lbl, new_disk),
        ensures
            post.inv(),
    {
        reveal(ConcreteJournal::State::disk_internal);
        Self::disk_internal_inductive(pre, post, lbl, new_disk);
    }

    pub proof fn initialize_inv(
        post: Self,
        disk: AsyncDisk::State,
        cache: Cache::State,
        journal: CachedJournal::State,
    )
        requires
            Self::initialize(post, disk, cache, journal),
        ensures
            post.inv(),
    {
        reveal(ConcreteJournal::State::initialize);
        Self::initialize_inductive(post, disk, cache, journal);
    }
}}

/// The loaded journal/cache/disk interpretation before allocation ownership.
impl ConcreteJournal::State {
    pub open spec fn linked_journal_view(self) -> LinkedJournal::State
    {
        LinkedJournal::State{
            truncated_journal: self.journal_tj(),
            unmarshalled_tail: cj_unmarshalled_tail(self.journal),
        }
    }

    pub open spec fn linked_journal_i(self) -> LinkedJournal::State
    {
        LinkedJournal::State{
            truncated_journal: self.loaded_journal_tj(),
            unmarshalled_tail: cj_unmarshalled_tail(self.journal),
        }
    }

    /// Interpretation function: ConcreteJournal -> AllocationJournal::State.
    pub open spec fn i(self) -> AllocationJournal::State
    {
        AllocationJournal::State{
            journal: self.linked_journal_i(),
            lsn_au_index: cached_lsn_au_index(self.journal),
            index_loaded: self.journal.status is Some,
            mini_allocator: self.mini_allocator,
        }
    }

    pub open spec fn tj_at(self, snapshot: JournalSnapshot) -> TruncatedJournal
    {
        let disk = self.journal_disk_view();
        TruncatedJournal{
            freshest_rec: snapshot.freshest_rec,
            disk_view: DiskView{
                boundary_lsn: snapshot.boundary_lsn,
                entries: disk.entries,
            },
        }
    }
}

pub proof fn valid_journal_structure_preserved_by_i_equal(
    pre: ConcreteJournal::State,
    post: ConcreteJournal::State,
)
    requires
        pre.valid_journal_structure(),
        post.journal == pre.journal,
        pre.journal_tj() =~= post.journal_tj(),
    ensures
        post.valid_journal_structure(),
{
    reveal(ConcreteJournal::State::valid_journal_structure);
    assert(cj_unmarshalled_tail(post.journal) == cj_unmarshalled_tail(pre.journal));
    assert(cj_lsn_addr_index(post.journal) == cj_lsn_addr_index(pre.journal));
}

proof fn build_lsn_addr_index_commutes_over_append_record(
    dv: DiskView,
    root: Pointer,
    msgs: MsgHistory,
    new_addr: Address,
)
    requires
        dv.tj_at(root).decodable(),
        dv.tj_at(root).seq_end() == msgs.seq_start,
        msgs.wf(),
        !msgs.is_empty(),
        !dv.entries.contains_key(new_addr),
    ensures
        lsn_addr_index_append_record(
            dv.build_lsn_addr_index(root),
            msgs.seq_start,
            msgs.seq_end,
            new_addr,
        ) =~= dv.tj_at(root).append_record(new_addr, msgs).build_lsn_addr_index(),
{
    let appended_tj = dv.tj_at(root).append_record(new_addr, msgs);
    assert(appended_tj.disk_view.valid_ranking(dv.tj_at(root).marshal_ranking(new_addr)));
    assert(appended_tj.decodable());
    dv.sub_disk_repr_index(appended_tj.disk_view, root);
    let update = singleton_index(msgs.seq_start, msgs.seq_end, new_addr);
    assert(dv.build_lsn_addr_index(root) == appended_tj.disk_view.build_lsn_addr_index(root));
    assert(appended_tj.disk_view.next(Some(new_addr)) == root);
    assert(appended_tj.disk_view.build_lsn_addr_index(Some(new_addr))
        == appended_tj.disk_view.build_lsn_addr_index(root).union_prefer_right(update));
}

/// Helper: from cache.inv(), lookup_map[addr] points to a non-empty slot whose get_addr() == addr.
/// Derives from cache.inv() => lookup_map == build_lookup_map(), proven via build_lookup_map_ensures.
proof fn cache_lookup_gets_addr(cache: Cache::State, addr: Address)
    requires
        cache.inv(),
        cache.lookup_map.contains_key(addr),
    ensures
        cache.entries.contains_key(cache.lookup_map[addr]),
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

proof fn async_disk_internal_pending_dom_preserved(pre: AsyncDisk::State, post: AsyncDisk::State)
    requires
        pre.inv(),
        AsyncDisk::State::next(pre, post, AsyncDisk::Label::Internal{}),
    ensures
        post.requests.dom() + post.responses.dom() == pre.requests.dom() + pre.responses.dom(),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let lbl = AsyncDisk::Label::Internal{};
    let step = choose |step| AsyncDisk::State::next_by(pre, post, lbl, step);
    match step {
        AsyncDisk::Step::process_read(id) => {
            let resp = DiskResponse::ReadResp{data: pre.content[pre.requests[id]->from]};
            assert(post.requests == pre.requests.remove(id));
            assert(post.responses == pre.responses.insert(id, resp));
            assert_sets_equal!(post.requests.dom() + post.responses.dom(), pre.requests.dom() + pre.responses.dom());
        }
        AsyncDisk::Step::process_write(id) => {
            let resp = DiskResponse::WriteResp{};
            assert(post.requests == pre.requests.remove(id));
            assert(post.responses == pre.responses.insert(id, resp));
            assert_sets_equal!(post.requests.dom() + post.responses.dom(), pre.requests.dom() + pre.responses.dom());
        }
        _ => {
            assert(false);
        }
    }
}

proof fn cache_internal_preserves_pending_slot(pre: Cache::State, post: Cache::State, addr: Address)
    requires
        pre.inv(),
        Cache::State::next(pre, post, Cache::Label::Internal{}),
        pre.lookup_map.contains_key(addr),
        ({
            let slot = pre.lookup_map[addr];
            ||| pre.entries[slot] is Loading
            ||| pre.status_map[slot] is Writeback
        }),
    ensures
        post.lookup_map.contains_key(addr),
        post.lookup_map[addr] == pre.lookup_map[addr],
        post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]],
        post.status_map[post.lookup_map[addr]] == pre.status_map[pre.lookup_map[addr]],
{
    Cache::State::inv_next(pre, post, Cache::Label::Internal{});
    let slot = pre.lookup_map[addr];
    cache_lookup_gets_addr(pre, addr);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let lbl = Cache::Label::Internal{};
    let step = choose |step| Cache::State::next_by(pre, post, lbl, step);
    match step {
        Cache::Step::reserve(new_slots_mapping) => {
            assert(!new_slots_mapping.contains_key(slot)) by {
                if new_slots_mapping.contains_key(slot) {
                    assert(pre.entries[slot] is Empty);
                }
            }
            assert(!new_slots_mapping.invert().contains_key(addr)) by {
                if new_slots_mapping.invert().contains_key(addr) {
                    reveal(Map::invert);
                    let mapped_slot = new_slots_mapping.invert()[addr];
                    assert(new_slots_mapping.contains_pair(mapped_slot, addr));
                    assert(new_slots_mapping.contains_value(addr));
                    assert(new_slots_mapping.values().contains(addr));
                    assert(pre.lookup_map.dom().contains(addr));
                    assert(false);
                }
            }
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::evict(evicted_slots) => {
            assert(!evicted_slots.contains(slot)) by {
                if evicted_slots.contains(slot) {
                    assert(pre.entries[slot] is Filled);
                    assert(pre.status_map[slot] is Clean);
                }
            }
            let evicted_addrs = Map::new(
                |slot: Slot| evicted_slots.contains(slot),
                |slot: Slot| pre.entries[slot].get_addr(),
            ).values();
            assert(!evicted_addrs.contains(addr)) by {
                if evicted_addrs.contains(addr) {
                    let evicted_slot = choose |s: Slot|
                        evicted_slots.contains(s)
                        && #[trigger] pre.entries[s].get_addr() == addr;
                    assert(pre.entries[evicted_slot] is Filled);
                    cache_filled_entry_in_lookup(pre, evicted_slot);
                    assert(pre.lookup_map[addr] == evicted_slot);
                    assert(slot == evicted_slot);
                    assert(false);
                }
            }
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::noop() => {
            assert(post == pre);
        }
        _ => {
            assert(false);
        }
    }
}

proof fn cache_disk_ops_preserves_pending_slot(
    pre: Cache::State,
    post: Cache::State,
    cache_requests: Set<DiskRequest>,
    cache_responses: Map<Address, DiskResponse>,
    addr: Address,
)
    requires
        pre.inv(),
        Cache::State::next(
            pre,
            post,
            Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses},
        ),
        pre.lookup_map.contains_key(addr),
        !cache_responses.contains_key(addr),
        ({
            let slot = pre.lookup_map[addr];
            ||| pre.entries[slot] is Loading
            ||| pre.status_map[slot] is Writeback
        }),
    ensures
        post.lookup_map.contains_key(addr),
        post.lookup_map[addr] == pre.lookup_map[addr],
        post.entries[post.lookup_map[addr]] == pre.entries[pre.lookup_map[addr]],
        post.status_map[post.lookup_map[addr]] == pre.status_map[pre.lookup_map[addr]],
{
    Cache::State::inv_next(
        pre,
        post,
        Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses},
    );
    let slot = pre.lookup_map[addr];
    cache_lookup_gets_addr(pre, addr);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
    let step = choose |step| Cache::State::next_by(pre, post, lbl, step);
    match step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert(cache_responses.is_empty());
            assert(!new_slots_mapping.contains_key(slot)) by {
                if new_slots_mapping.contains_key(slot) {
                    assert(pre.entries[slot] is Empty);
                }
            }
            assert(!new_slots_mapping.invert().contains_key(addr)) by {
                if new_slots_mapping.invert().contains_key(addr) {
                    reveal(Map::invert);
                    let mapped_slot = new_slots_mapping.invert()[addr];
                    assert(new_slots_mapping.contains_pair(mapped_slot, addr));
                    assert(new_slots_mapping.contains_value(addr));
                    assert(new_slots_mapping.values().contains(addr));
                    assert(pre.lookup_map.dom().contains(addr));
                    assert(false);
                }
            }
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::load_complete() => {
            assert(cache_requests.is_empty());
            let restricted_lookup = pre.lookup_map.restrict(cache_responses.dom());
            let slot_addr_map = restricted_lookup.invert();
            assert(!slot_addr_map.contains_key(slot)) by {
                if slot_addr_map.contains_key(slot) {
                    Cache::State::invert_contains_pair(restricted_lookup, slot);
                    let resp_addr = slot_addr_map[slot];
                    assert(restricted_lookup.contains_pair(resp_addr, slot));
                    assert(cache_responses.contains_key(resp_addr));
                    assert(pre.lookup_map.contains_key(resp_addr));
                    assert(pre.lookup_map[resp_addr] == slot);
                    pre.build_lookup_map_ensures();
                    assert(pre.lookup_map.is_injective());
                    assert(resp_addr == addr);
                    assert(false);
                }
            }
            assert(post.lookup_map == pre.lookup_map);
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::writeback_initiate() => {
            assert(cache_responses.is_empty());
            let request_slot_map = Map::new(
                |req: DiskRequest| cache_requests.contains(req),
                |req: DiskRequest| pre.lookup_map[req->to],
            );
            let writeback_slots = request_slot_map.values();
            assert(!writeback_slots.contains(slot)) by {
                if writeback_slots.contains(slot) {
                    let req = choose |req: DiskRequest|
                        request_slot_map.contains_key(req)
                        && #[trigger] request_slot_map[req] == slot;
                    assert(cache_requests.contains(req));
                    assert(req is WriteReq);
                    assert(pre.lookup_map.contains_key(req->to));
                    assert(pre.entries[pre.lookup_map[req->to]]
                        == Entry::Filled{addr: req->to, data: req->data});
                    assert(pre.status_map[pre.lookup_map[req->to]] is Dirty);
                    assert(pre.lookup_map[req->to] == slot);
                    if pre.entries[slot] is Loading {
                        assert(false);
                    } else {
                        assert(pre.status_map[slot] is Writeback);
                        assert(false);
                    }
                }
            }
            assert(post.lookup_map == pre.lookup_map);
            assert(post.entries == pre.entries);
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        Cache::Step::writeback_complete() => {
            assert(cache_requests.is_empty());
            let resps_slots = pre.lookup_map.restrict(cache_responses.dom()).values();
            assert(!resps_slots.contains(slot)) by {
                if resps_slots.contains(slot) {
                    let resp_addr = choose |a: Address|
                        pre.lookup_map.restrict(cache_responses.dom()).contains_key(a)
                        && #[trigger] pre.lookup_map.restrict(cache_responses.dom())[a] == slot;
                    assert(cache_responses.contains_key(resp_addr));
                    assert(pre.lookup_map.contains_key(resp_addr));
                    assert(pre.lookup_map[resp_addr] == slot);
                    pre.build_lookup_map_ensures();
                    assert(pre.lookup_map.is_injective());
                    assert(resp_addr == addr);
                    assert(false);
                }
            }
            assert(post.lookup_map == pre.lookup_map);
            assert(post.entries == pre.entries);
            assert(post.lookup_map.contains_key(addr));
            assert(post.lookup_map[addr] == pre.lookup_map[addr]);
            assert(post.entries[slot] == pre.entries[slot]);
            assert(post.status_map[slot] == pre.status_map[slot]);
        }
        _ => {
            assert(false);
        }
    }
}

proof fn cache_response_absent_for_unresponded_outstanding(
    pre: ConcreteJournal::State,
    cache_responses: Map<Address, DiskResponse>,
    disk_responses: Map<ID, DiskResponse>,
    id: ID,
)
    requires
        pre.outstanding_cache_reqs.is_injective(),
        pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
        pre.outstanding_cache_reqs.contains_key(id),
        !disk_responses.contains_key(id),
    ensures
        !cache_responses.contains_key(pre.outstanding_cache_reqs[id]),
{
    let addr = pre.outstanding_cache_reqs[id];
    if cache_responses.contains_key(addr) {
        let restricted = pre.outstanding_cache_reqs.restrict(disk_responses.dom());
        assert(restricted.values().contains(addr));
        let id2 = choose |id2: ID|
            restricted.contains_key(id2) && #[trigger] restricted[id2] == addr;
        assert(disk_responses.contains_key(id2));
        assert(pre.outstanding_cache_reqs.contains_key(id2));
        assert(pre.outstanding_cache_reqs[id2] == addr);
        if id2 != id {
            assert(pre.outstanding_cache_reqs[id2] != pre.outstanding_cache_reqs[id]);
        } else {
            assert(disk_responses.contains_key(id));
        }
        assert(false);
    }
}

proof fn cache_access_preserves_outstanding_reqs_consistent(
    pre: ConcreteJournal::State,
    post: ConcreteJournal::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.cache.inv(),
        pre.outstanding_reqs_consistent(),
        Cache::State::next(pre.cache, post.cache, Cache::Label::Access{reads, writes}),
        post.disk == pre.disk,
        post.outstanding_cache_reqs == pre.outstanding_cache_reqs,
    ensures
        post.outstanding_reqs_consistent(),
{
    let lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre.cache, post.cache, lbl);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(pre.cache, post.cache, lbl, Cache::Step::access()));

    assert(post.outstanding_reqs_requests_ok()) by {
        assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
            implies {
                let req = post.disk.requests[id];
                let addr = post.outstanding_cache_reqs[id];
                &&& post.outstanding_cache_reqs.contains_key(id)
                &&& req.addr() == addr
                &&& req is ReadReq ==> {
                    let slot = post.cache.lookup_map[addr];
                    &&& post.cache.entries[slot] is Loading
                }
                &&& req is WriteReq ==> {
                    let slot = post.cache.lookup_map[addr];
                    &&& post.cache.entries[slot] == Entry::Filled{addr, data: req->data}
                    &&& post.cache.status_map[slot] is Writeback
                }
            } by {
            let req = pre.disk.requests[id];
            let addr = pre.outstanding_cache_reqs[id];
            assert(pre.outstanding_cache_reqs.contains_key(id));
            assert(!writes.contains_key(addr)) by {
                if writes.contains_key(addr) {
                    assert(pre.cache.valid_write(addr));
                    let slot = pre.cache.lookup_map[addr];
                    if req is ReadReq {
                        assert(pre.cache.entries[slot] is Loading);
                        assert(false);
                    } else {
                        assert(req is WriteReq);
                        assert(pre.cache.status_map[slot] is Writeback);
                        assert(false);
                    }
                }
            }
            Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
        }
    }

    assert(post.outstanding_reqs_responses_ok()) by {
        assert forall |id: ID| #[trigger] post.disk.responses.contains_key(id)
            implies {
                let resp = post.disk.responses[id];
                let addr = post.outstanding_cache_reqs[id];
                &&& post.outstanding_cache_reqs.contains_key(id)
                &&& resp is ReadResp ==> {
                    let slot = post.cache.lookup_map[addr];
                    &&& resp->data == post.disk.content[addr]
                    &&& post.cache.entries[slot] is Loading
                }
                &&& resp is WriteResp ==> {
                    let slot = post.cache.lookup_map[addr];
                    &&& post.cache.entries[slot] == Entry::Filled{addr, data: post.disk.content[addr]}
                    &&& post.cache.status_map[slot] is Writeback
                }
            } by {
            let resp = pre.disk.responses[id];
            let addr = pre.outstanding_cache_reqs[id];
            assert(pre.outstanding_cache_reqs.contains_key(id));
            assert(!writes.contains_key(addr)) by {
                if writes.contains_key(addr) {
                    assert(pre.cache.valid_write(addr));
                    let slot = pre.cache.lookup_map[addr];
                    if resp is ReadResp {
                        assert(pre.cache.entries[slot] is Loading);
                        assert(false);
                    } else {
                        assert(resp is WriteResp);
                        assert(pre.cache.status_map[slot] is Writeback);
                        assert(false);
                    }
                }
            }
            Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
        }
    }

    assert forall |id: ID|
        #![trigger post.disk.requests.contains_key(id)]
        #![trigger post.disk.responses.contains_key(id)]
        (post.disk.requests.contains_key(id) || post.disk.responses.contains_key(id))
        implies post.io_id_valid(id) by {
        let addr = pre.outstanding_cache_reqs[id];
        assert(pre.io_id_valid(id));
        assert(!writes.contains_key(addr)) by {
            if writes.contains_key(addr) {
                assert(pre.cache.valid_write(addr));
                let slot = pre.cache.lookup_map[addr];
                if pre.disk.requests.contains_key(id) {
                    let req = pre.disk.requests[id];
                    if req is ReadReq {
                        assert(pre.cache.entries[slot] is Loading);
                        assert(false);
                    } else {
                        assert(req is WriteReq);
                        assert(pre.cache.status_map[slot] is Writeback);
                        assert(false);
                    }
                } else {
                    let resp = pre.disk.responses[id];
                    if resp is ReadResp {
                        assert(pre.cache.entries[slot] is Loading);
                        assert(false);
                    } else {
                        assert(resp is WriteResp);
                        assert(pre.cache.status_map[slot] is Writeback);
                        assert(false);
                    }
                }
            }
        }
        Cache::State::access_unwritten_addr_unchanged(pre.cache, post.cache, reads, writes, addr);
        assert(post.outstanding_cache_reqs.contains_key(id));
        assert(post.cache.lookup_map.contains_key(post.outstanding_cache_reqs[id]));
        cache_lookup_gets_addr(post.cache, post.outstanding_cache_reqs[id]);
        assert(post.cache.entries.contains_key(post.cache.lookup_map[post.outstanding_cache_reqs[id]]));
        assert(post.cache.status_map.contains_key(post.cache.lookup_map[post.outstanding_cache_reqs[id]]));
    }

    assert(post.outstanding_cache_reqs.is_injective());
    assert(post.disk.requests.dom() + post.disk.responses.dom() == post.outstanding_cache_reqs.dom());
}

proof fn writeback_response_matches_outstanding_disk(
    pre: ConcreteJournal::State,
    cache_responses: Map<Address, DiskResponse>,
    disk_responses: Map<ID, DiskResponse>,
    addr: Address,
)
    requires
        pre.inv(),
        pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
        disk_responses <= pre.disk.responses,
        cache_responses.contains_key(addr),
        cache_responses[addr] is WriteResp,
    ensures
        pre.disk.content.contains_key(addr),
        pre.cache.lookup_map.contains_key(addr),
        pre.cache.entries[pre.cache.lookup_map[addr]]
            == (Entry::Filled{addr, data: pre.disk.content[addr]}),
        pre.cache.status_map[pre.cache.lookup_map[addr]] is Writeback,
{
    let restricted = pre.outstanding_cache_reqs.restrict(disk_responses.dom());
    assert(restricted.values().contains(addr));
    let id = choose |id: ID| restricted.contains_key(id) && #[trigger] restricted[id] == addr;
    assert(disk_responses.contains_key(id));
    assert(pre.outstanding_cache_reqs.contains_key(id));
    assert(pre.outstanding_cache_reqs[id] == addr);
    assert(cache_responses[addr] == disk_responses[id]);
    assert(pre.disk.responses.contains_key(id));
    assert(pre.disk.responses[id] == disk_responses[id]);
    assert(cache_responses[addr] is WriteResp);
    assert(pre.disk.responses[id] is WriteResp);
}

proof fn read_response_matches_outstanding_disk(
    pre: ConcreteJournal::State,
    cache_responses: Map<Address, DiskResponse>,
    disk_responses: Map<ID, DiskResponse>,
    addr: Address,
)
    requires
        pre.inv(),
        pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
        disk_responses <= pre.disk.responses,
        cache_responses.contains_key(addr),
        cache_responses[addr] is ReadResp,
    ensures
        pre.disk.content.contains_key(addr),
        cache_responses[addr]->data == pre.disk.content[addr],
        pre.cache.lookup_map.contains_key(addr),
        pre.cache.entries[pre.cache.lookup_map[addr]] is Loading,
{
    let restricted = pre.outstanding_cache_reqs.restrict(disk_responses.dom());
    assert(restricted.values().contains(addr));
    let id = choose |id: ID| restricted.contains_key(id) && #[trigger] restricted[id] == addr;
    assert(disk_responses.contains_key(id));
    assert(pre.outstanding_cache_reqs.contains_key(id));
    assert(pre.outstanding_cache_reqs[id] == addr);
    assert(cache_responses[addr] == disk_responses[id]);
    assert(pre.disk.responses.contains_key(id));
    assert(pre.disk.responses[id] == disk_responses[id]);
    assert(pre.disk.responses[id] is ReadResp);
}

// ================================================================
// Public proof lemmas: journal_disk_view preservation for internal transitions.
// Called by CrashAwareConcreteJournalRefinement to prove pre.i() == post.i().
// ================================================================

/// Cache internal (reserve/evict/noop) preserves journal_disk_view and ConcreteJournal.i().
pub proof fn cache_internal_preserves_i(
    pre: ConcreteJournal::State,
    post: ConcreteJournal::State,
    new_cache: Cache::State,
)
    requires
        pre.inv(),
        Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{}),
        post.journal == pre.journal,
        post.cache == new_cache,
        post.disk == pre.disk,
        post.mini_allocator == pre.mini_allocator,
    ensures
        pre.journal_disk_view() =~= post.journal_disk_view(),
        pre.journal_tj() =~= post.journal_tj(),
        pre.journal_disk_view() =~= post.journal_disk_view(),
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
                post.dirty_cache_journal_entries().dom().contains(addr)
            implies #[trigger] pre.dirty_cache_journal_entries().dom().contains(addr)
            by {
                cache_lookup_gets_addr(post.cache, addr);
                let slot = post.cache.lookup_map[addr];
                cache_filled_entry_in_lookup(pre.cache, slot);
            };
            assert(pre.dirty_cache_journal_entries() =~= post.dirty_cache_journal_entries());
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
            assert(pre.dirty_cache_journal_entries() =~= post.dirty_cache_journal_entries());
        }
        Cache::Step::noop() => {}
        _ => {}
    }
    assert(pre.disk_journal_entries() =~= post.disk_journal_entries());
    assert(pre.journal_disk_view() =~= post.journal_disk_view());
    assert(pre.journal_tj() =~= post.journal_tj());
    assert(pre.journal_disk_view() =~= post.journal_disk_view());
    assert(pre.i() =~= post.i()) by {
        reveal(ConcreteJournal::State::i);
        assert(pre.journal_tj() =~= post.journal_tj());
    }
}

/// Disk internal (process_read/process_write) preserves journal_disk_view and ConcreteJournal.i().
pub proof fn disk_internal_preserves_i(
    pre: ConcreteJournal::State,
    post: ConcreteJournal::State,
    new_disk: AsyncDisk::State,
)
    requires
        pre.inv(),
        AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::Internal{}),
        post.journal == pre.journal,
        post.cache == pre.cache,
        post.disk == new_disk,
        post.mini_allocator == pre.mini_allocator,
    ensures
        pre.journal_disk_view() =~= post.journal_disk_view(),
        pre.journal_tj() =~= post.journal_tj(),
        pre.journal_disk_view() =~= post.journal_disk_view(),
        pre.i() =~= post.i(),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let step = choose |step| AsyncDisk::State::next_by(pre.disk, post.disk, AsyncDisk::Label::Internal{}, step);
    match step {
        AsyncDisk::Step::process_read(id) => {}
        AsyncDisk::Step::process_write(id) => {
            let req = pre.disk.requests[id];
            let write_addr = pre.disk.requests[id]->to;
            assert(req is WriteReq);
            assert(write_addr == req.addr());
            assert(pre.outstanding_cache_reqs.contains_key(id));
            assert(pre.outstanding_cache_reqs[id] == write_addr);
            let slot = pre.cache.lookup_map[write_addr];
            assert(pre.cache.entries[slot] == Entry::Filled{addr: write_addr, data: req->data});
            assert(pre.cache.status_map[slot] is Writeback);
            if pre.journal_disk_view().entries.dom().contains(write_addr) {
                assert(pre.dirty_cache_journal_entries().dom().contains(write_addr));
            }

            assert forall |addr: Address|
                pre.journal_disk_view().entries.dom().contains(addr)
                <==> #[trigger] post.journal_disk_view().entries.dom().contains(addr)
            by {};

            assert forall |addr: Address|
                pre.journal_disk_view().entries.dom().contains(addr)
            implies pre.journal_disk_view().entries[addr]
                =~= #[trigger] post.journal_disk_view().entries[addr]
            by {};

            assert(pre.journal_disk_view() =~= post.journal_disk_view());
        }
        _ => {}
    }
    assert(pre.journal_tj() =~= post.journal_tj());
    assert(pre.journal_disk_view() =~= post.journal_disk_view());
    assert(pre.i() =~= post.i()) by {
        reveal(ConcreteJournal::State::i);
        assert(pre.journal_tj() =~= post.journal_tj());
    }
}

/// Disk ops (request enqueue / response dequeue) preserves journal_disk_view and ConcreteJournal.i()
/// when journal and cache are unchanged because disk content is unchanged.
pub proof fn disk_ops_preserves_i(
    pre: ConcreteJournal::State,
    post: ConcreteJournal::State,
    new_disk: AsyncDisk::State,
    disk_requests: Map<ID, DiskRequest>,
    disk_responses: Map<ID, DiskResponse>,
)
    requires
        pre.inv(),
        AsyncDisk::State::next(pre.disk, new_disk, AsyncDisk::Label::DiskOps{
            requests: disk_requests,
            responses: disk_responses,
        }),
        post.journal == pre.journal,
        post.cache == pre.cache,
        post.disk == new_disk,
        post.mini_allocator == pre.mini_allocator,
    ensures
        pre.journal_disk_view() =~= post.journal_disk_view(),
        pre.journal_tj() =~= post.journal_tj(),
        pre.journal_disk_view() =~= post.journal_disk_view(),
        pre.i() =~= post.i(),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let step = choose |step| AsyncDisk::State::next_by(
        pre.disk,
        post.disk,
        AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses},
        step,
    );
    match step {
        AsyncDisk::Step::disk_ops() => {
            assert(post.disk.content == pre.disk.content);
            assert(pre.disk_journal_entries() =~= post.disk_journal_entries());
            assert(pre.dirty_cache_journal_entries() =~= post.dirty_cache_journal_entries());
            assert(pre.journal_disk_view() =~= post.journal_disk_view());
            assert(pre.journal_tj() =~= post.journal_tj());
            assert(pre.journal_disk_view() =~= post.journal_disk_view());
            assert(pre.i() =~= post.i()) by {
                reveal(ConcreteJournal::State::i);
                assert(pre.journal_tj() =~= post.journal_tj());
            }
        }
        _ => {
            assert(false);
        }
    }
}

/// Cache disk ops preserves journal_disk_view and ConcreteJournal.i().
pub proof fn cache_disk_ops_preserves_i(
    pre: ConcreteJournal::State,
    post: ConcreteJournal::State,
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
        pre.disk_responses_match_cache_responses(cache_responses, disk_responses),
        post.journal == pre.journal,
        post.cache == new_cache,
        post.disk == new_disk,
        post.mini_allocator == pre.mini_allocator,
    ensures
        pre.journal_disk_view() =~= post.journal_disk_view(),
        pre.journal_tj() =~= post.journal_tj(),
        pre.journal_disk_view() =~= post.journal_disk_view(),
        pre.i() =~= post.i(),
{
    Cache::State::inv_next(pre.cache, post.cache, Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses});
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);

    let cache_lbl = Cache::Label::DiskOps{requests: cache_requests, responses: cache_responses};
    let cache_step = choose |step| Cache::State::next_by(pre.cache, post.cache, cache_lbl, step);
    let disk_lbl = AsyncDisk::Label::DiskOps{requests: disk_requests, responses: disk_responses};
    let disk_step = choose |step| AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
    match disk_step {
        AsyncDisk::Step::disk_ops() => {
            assert(post.disk.content == pre.disk.content);
            assert(disk_responses <= pre.disk.responses);
        }
        _ => {
            assert(false);
        }
    }
    match cache_step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert forall |slot: Slot|
                pre.cache.entries.contains_key(slot) && pre.cache.entries[slot] is Filled
            implies post.cache.entries.contains_key(slot)
                && #[trigger] post.cache.entries[slot] == pre.cache.entries[slot]
            by { assert(!new_slots_mapping.contains_key(slot)); };

            assert forall |addr: Address|
                post.dirty_cache_journal_entries().dom().contains(addr)
            implies #[trigger] pre.dirty_cache_journal_entries().dom().contains(addr)
            by {
                cache_lookup_gets_addr(post.cache, addr);
                let slot = post.cache.lookup_map[addr];
                cache_filled_entry_in_lookup(pre.cache, slot);
            };

            assert forall |addr: Address|
                pre.dirty_cache_journal_entries().dom().contains(addr)
            implies #[trigger] post.dirty_cache_journal_entries().dom().contains(addr)
            by {
                cache_lookup_gets_addr(pre.cache, addr);
                let slot = pre.cache.lookup_map[addr];
                cache_filled_entry_in_lookup(post.cache, slot);
            };

            assert(pre.dirty_cache_journal_entries() =~= post.dirty_cache_journal_entries());
        }
        Cache::Step::load_complete() => {
            assert(pre.dirty_cache_journal_entries() =~= post.dirty_cache_journal_entries());
        }
        Cache::Step::writeback_initiate() => {
            assert(pre.dirty_cache_journal_entries() =~= post.dirty_cache_journal_entries());
        }
        Cache::Step::writeback_complete() => {
            assert(cache_requests.is_empty());
            assert(pre.cache.valid_writeback_responses(cache_responses));
            assert(post.disk.content == pre.disk.content);
            assert forall |addr: Address|
                pre.dirty_cache_journal_entries().dom().contains(addr)
                && !cache_responses.contains_key(addr)
            implies #[trigger] post.dirty_cache_journal_entries().dom().contains(addr)
            by {
                cache_lookup_gets_addr(pre.cache, addr);
                let slot = pre.cache.lookup_map[addr];
                let resps_slots = pre.cache.lookup_map.restrict(cache_responses.dom()).values();
                assert(!resps_slots.contains(slot)) by {
                    if resps_slots.contains(slot) {
                        let resp_addr = choose |a: Address|
                            pre.cache.lookup_map.restrict(cache_responses.dom()).contains_key(a)
                            && #[trigger] pre.cache.lookup_map.restrict(cache_responses.dom())[a] == slot;
                        assert(cache_responses.contains_key(resp_addr));
                        assert(pre.cache.lookup_map.contains_key(resp_addr));
                        assert(pre.cache.lookup_map[resp_addr] == slot);
                        pre.cache.build_lookup_map_ensures();
                        assert(pre.cache.lookup_map.is_injective());
                        assert(resp_addr == addr);
                        assert(false);
                    }
                }
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.cache.entries == pre.cache.entries);
                assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
            };
            assert forall |addr: Address|
                post.dirty_cache_journal_entries().dom().contains(addr)
            implies #[trigger] pre.dirty_cache_journal_entries().dom().contains(addr)
            by {
                cache_lookup_gets_addr(post.cache, addr);
                let slot = post.cache.lookup_map[addr];
                assert(post.cache.lookup_map == pre.cache.lookup_map);
                assert(post.cache.entries == pre.cache.entries);
                if cache_responses.contains_key(addr) {
                    assert(pre.cache.valid_writeback_responses(cache_responses));
                    assert(pre.cache.lookup_map.contains_key(addr));
                    assert(pre.cache.lookup_map[addr] == slot);
                    let resps_slots = pre.cache.lookup_map.restrict(cache_responses.dom()).values();
                    let restricted_lookup = pre.cache.lookup_map.restrict(cache_responses.dom());
                    assert(restricted_lookup.contains_key(addr));
                    assert(restricted_lookup[addr] == slot);
                    assert(resps_slots.contains(slot));
                    let updated_status_map = Map::new(
                        |slot| resps_slots.contains(slot),
                        |slot| Status::Clean,
                    );
                    assert(updated_status_map.contains_key(slot));
                    assert(updated_status_map[slot] is Clean);
                    assert(post.cache.status_map[slot] is Clean);
                    assert(false);
                } else {
                    let resps_slots = pre.cache.lookup_map.restrict(cache_responses.dom()).values();
                    assert(!resps_slots.contains(slot)) by {
                        if resps_slots.contains(slot) {
                            let resp_addr = choose |a: Address|
                                pre.cache.lookup_map.restrict(cache_responses.dom()).contains_key(a)
                                && #[trigger] pre.cache.lookup_map.restrict(cache_responses.dom())[a] == slot;
                            assert(cache_responses.contains_key(resp_addr));
                            assert(pre.cache.lookup_map.contains_key(resp_addr));
                            assert(pre.cache.lookup_map[resp_addr] == slot);
                            pre.cache.build_lookup_map_ensures();
                            assert(pre.cache.lookup_map.is_injective());
                            assert(resp_addr == addr);
                            assert(false);
                        }
                    }
                    assert(post.cache.status_map[slot] == pre.cache.status_map[slot]);
                }
            };
            assert forall |addr: Address|
                cache_responses.contains_key(addr)
                && pre.dirty_cache_journal_entries().dom().contains(addr)
            implies post.disk_journal_entries().dom().contains(addr)
                && #[trigger] post.disk_journal_entries()[addr] == pre.dirty_cache_journal_entries()[addr]
            by {
                assert(cache_responses[addr] is WriteResp);
                writeback_response_matches_outstanding_disk(pre, cache_responses, disk_responses, addr);
                cache_lookup_gets_addr(pre.cache, addr);
                let slot = pre.cache.lookup_map[addr];
                assert(pre.cache.entries[slot] == Entry::Filled{addr, data: pre.disk.content[addr]});
                assert(pre.dirty_cache_journal_entries()[addr] == raw_page_to_record(pre.disk.content[addr]));
                assert(post.journal == pre.journal);
                assert(post.disk.content == pre.disk.content);
                assert(post.disk_journal_entries().contains_key(addr));
                assert(post.disk_journal_entries()[addr] == raw_page_to_record(pre.disk.content[addr]));
            };
            assert forall |addr: Address|
                pre.journal_disk_view().entries.dom().contains(addr)
                <==> #[trigger] post.journal_disk_view().entries.dom().contains(addr)
            by {
                if pre.journal_disk_view().entries.dom().contains(addr) {
                    if pre.dirty_cache_journal_entries().contains_key(addr) {
                        if cache_responses.contains_key(addr) {
                            assert(cache_responses[addr] is WriteResp);
                            writeback_response_matches_outstanding_disk(pre, cache_responses, disk_responses, addr);
                            assert(post.journal == pre.journal);
                            assert(post.disk.content == pre.disk.content);
                            assert(post.disk_journal_entries().contains_key(addr));
                        } else {
                            assert(post.dirty_cache_journal_entries().contains_key(addr));
                        }
                    } else {
                        assert(pre.disk_journal_entries().contains_key(addr));
                        assert(post.disk_journal_entries().contains_key(addr));
                    }
                } else {
                    if post.dirty_cache_journal_entries().contains_key(addr) {
                        assert(pre.dirty_cache_journal_entries().contains_key(addr));
                    } else if post.disk_journal_entries().contains_key(addr) {
                        assert(pre.disk_journal_entries().contains_key(addr));
                    }
                }
            };
            assert forall |addr: Address|
                pre.journal_disk_view().entries.dom().contains(addr)
            implies pre.journal_disk_view().entries[addr]
                =~= #[trigger] post.journal_disk_view().entries[addr]
            by {
                if pre.dirty_cache_journal_entries().contains_key(addr) {
                    if cache_responses.contains_key(addr) {
                        assert(post.disk_journal_entries()[addr] == pre.dirty_cache_journal_entries()[addr]);
                    } else {
                        assert(post.dirty_cache_journal_entries()[addr] == pre.dirty_cache_journal_entries()[addr]);
                    }
                } else {
                    assert(pre.disk_journal_entries().contains_key(addr));
                    if post.dirty_cache_journal_entries().contains_key(addr) {
                        assert(pre.dirty_cache_journal_entries().contains_key(addr));
                        assert(false);
                    } else {
                        assert(post.disk_journal_entries()[addr] == pre.disk_journal_entries()[addr]);
                    }
                }
            };
            assert(pre.journal_disk_view() =~= post.journal_disk_view());
        }
        _ => {}
    }
    assert(pre.journal_disk_view() =~= post.journal_disk_view());
    assert(pre.journal_tj() =~= post.journal_tj());
    assert(pre.journal_disk_view() =~= post.journal_disk_view());
    assert(pre.i() =~= post.i()) by {
        reveal(ConcreteJournal::State::i);
        assert(pre.journal_tj() =~= post.journal_tj());
    }
}

impl ConcreteJournal::Label {
    pub open spec fn i(self, state: ConcreteJournal::State) -> AllocationJournal::Label
    {
        match self {
            Self::ReadForRecovery{messages} => { AllocationJournal::Label::ReadForRecovery{messages} }
            Self::FreezeForCommit{frozen} => {
                let frozen_tj = state.tj_at(frozen);
                AllocationJournal::Label::FreezeForCommit{
                    frozen_journal: JournalImage{
                        tj: frozen_tj,
                    },
                }
            }
            Self::QueryEndLsn{end_lsn} => { AllocationJournal::Label::QueryEndLsn{end_lsn} }
            Self::Put{messages} => { AllocationJournal::Label::Put{messages} }
            Self::DiscardOld{start_lsn, require_end} => {
                let new_lsn_au_index = Map::new(
                    |lsn| cached_lsn_au_index(state.journal).contains_key(lsn) && start_lsn <= lsn,
                    |lsn| cached_lsn_au_index(state.journal)[lsn],
                );
                AllocationJournal::Label::DiscardOld{
                    start_lsn,
                    require_end,
                    deallocs: cached_lsn_au_index(state.journal).values().difference(new_lsn_au_index.values()),
                }
            }
            Self::Internal{allocs, deallocs} => { AllocationJournal::Label::InternalAllocations{allocs, deallocs} }
        }
    }
}

}
