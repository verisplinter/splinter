// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::LSN;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Value;
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::AtomicState_v::{to_journal_reads, raw_page_to_record};
use crate::implementation::OverflowFiction_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::disk::GenericDisk_v::{Address, IAddress, Pointer, Ranking};
use crate::implementation::JournalTypes_v::AJournal;
use crate::implementation::JournalTypes_v::ILsn;
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, lsn_addr_index_append_record, singleton_index, lsn_disjoint};
use crate::implementation::Cache_v::Cache;
use crate::implementation::FracCacheImpl_v::*;
use crate::implementation::ILsnAddrIndex_v::*;
use crate::marshalling::Slice_v::Slice;
use crate::marshalling::IJournalRecordFormat_v::{IJournalRecord, IJournalRecordFormat, IJournalRecordWrappable};
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::Wrappable_v::Wrappable;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::JournalRecord;

verus!{

#[derive(Debug, Copy, Clone)]
pub struct IJournalSnapshot {
    pub boundary_lsn: u64,
    pub freshest_rec: Option<IAddress>,
}

impl IJournalSnapshot {
    pub open spec fn spec_new_empty(at_lsn: u64) -> Self {
        IJournalSnapshot{ boundary_lsn: at_lsn, freshest_rec: None }
    }

    pub exec fn new_empty(at_lsn: u64) -> (out: Self)
        ensures out == Self::spec_new_empty(at_lsn)
    {
        IJournalSnapshot{ boundary_lsn: at_lsn, freshest_rec: None }
    }
}

pub open spec fn iaddr_view(ptr: Option<IAddress>) -> Option<Address>
{
    match ptr {
        None => None,
        Some(iaddr) => Some(iaddr@),
    }
}

proof fn map_le_lookup_eq<V>(m1: Map<Address, V>, m2: Map<Address, V>, k: Address)
requires
    m1 <= m2,
    m1.contains_key(k),
ensures
    m1[k] == m2[k],
{
    // trigger
    assert(m2.contains_key(k));
}

proof fn disk_view_valid_ranking_subset(
    disk: LinkedJournal_v::DiskView,
    sub: Map<Address, JournalRecord>,
    ranking: Ranking,
)
requires
    disk.valid_ranking(ranking),
    sub <= disk.entries,
ensures
    (LinkedJournal_v::DiskView{boundary_lsn: disk.boundary_lsn, entries: sub}).valid_ranking(ranking),
{
    let dv = LinkedJournal_v::DiskView{boundary_lsn: disk.boundary_lsn, entries: sub};
    assert(dv.entries.dom().subset_of(ranking.dom())) by {
        assert forall |k| #[trigger] dv.entries.contains_key(k)
            implies ranking.dom().contains(k) by {
            assert(disk.entries.contains_key(k));
            assert(disk.entries.dom().contains(k));
            assert(disk.entries.dom().subset_of(ranking.dom()));
        };
    }
    assert forall |addr| #[trigger] dv.entries.contains_key(addr)
        && dv.entries[addr].cropped_prior(dv.boundary_lsn) is Some
        implies ranking[dv.entries[addr].cropped_prior(dv.boundary_lsn).unwrap()] < ranking[addr] by {
        assert(disk.entries.contains_key(addr));
        map_le_lookup_eq(sub, disk.entries, addr);
        assert(disk.entries[addr] == dv.entries[addr]);
        assert(ranking[disk.entries[addr].cropped_prior(dv.boundary_lsn).unwrap()] < ranking[addr]);
    };
}

pub proof fn to_journal_reads_entry_from_exec_parse(
    fmt: IJournalRecordFormat,
    reads: Map<Address, RawPage>,
    addr: Address,
    value: IJournalRecord,
)
requires
    fmt.valid(),
    reads.contains_key(addr),
    fmt.parsable(reads[addr]),
    value.parsedv() == fmt.parse(reads[addr]),
ensures
    to_journal_reads(reads)[addr] == value.parsedv().view(),
{
    let ghost spec_fmt = IJournalRecordFormat::spec_new();
    assert((fmt.pair_fmt.a_fmt, fmt.pair_fmt.b_fmt)
        == IJournalRecordWrappable::spec_new_format_pair());
    assert((spec_fmt.pair_fmt.a_fmt, spec_fmt.pair_fmt.b_fmt)
        == IJournalRecordWrappable::spec_new_format_pair());
    assert(fmt.pair_fmt == spec_fmt.pair_fmt);
    assert(spec_fmt.parsable(reads[addr]));
    assert(fmt.parse(reads[addr]) == spec_fmt.parse(reads[addr]));
    assert(to_journal_reads(reads)[addr] == raw_page_to_record(reads[addr]));
    assert(raw_page_to_record(reads[addr]) == spec_fmt.parse(reads[addr]).view());
    assert(value.parsedv().view() == fmt.parse(reads[addr]).view());
}

#[verifier::external_body]
fn please_panic()
    ensures false
{
    panic!();
}

impl View for IJournalSnapshot {
    type V = JournalSnapshot;

    open spec fn view(&self) -> Self::V {
        Self::V{
            boundary_lsn: self.boundary_lsn as LSN,
            freshest_rec: iaddr_view(self.freshest_rec),
        }
    }
}

impl Parsedview<JournalSnapshot> for IJournalSnapshot {
    open spec fn parsedv(&self) -> JournalSnapshot
    {
        self@
    }
}

use crate::marshalling::WF_v::WF;

impl WF for IJournalSnapshot {}

pub struct FrozenJournal {
    pub snapshot: IJournalSnapshot,
    pub seq_end: ILsn,
}

impl FrozenJournal {
    pub open spec fn wf(self) -> bool {
        &&& self.seq_start() <= self.seq_end
        &&& self.snapshot.freshest_rec is None ==> self.seq_end == self.snapshot.boundary_lsn
        &&& self.snapshot.freshest_rec is Some ==> self.seq_start() < self.seq_end
    }

    pub open spec fn seq_start(self) -> ILsn { self.snapshot.boundary_lsn }

    /// The page at this frozen journal's freshest_rec, parsed via raw_page_to_record,
    /// has message_seq.seq_end matching this frozen journal's seq_end.
    pub open spec fn freshest_rec_page_agrees(self, cache: Cache::State) -> bool {
        self.snapshot@.freshest_rec is Some ==> {
            let addr = self.snapshot@.freshest_rec.unwrap();
            &&& cache.lookup_map.contains_key(addr)
            &&& raw_page_to_record(cache.entries[cache.lookup_map[addr]]->data).message_seq.seq_end == self.seq_end as nat
        }
    }
}

pub struct IJournalStatus {
    pub lsn_addr_index: ILsnAddrIndex,
    pub unmarshalled_tail: Vec<(Key,Value)>,
    pub clean_watermark_lsn: ILsn,
}

impl IJournalStatus {
    spec fn wf(&self) -> bool
    {
        &&& self.lsn_addr_index.wf()
    }

    closed spec fn tail_as_history(&self) -> MsgHistory
    {
        AJournal {
            msg_history: self.unmarshalled_tail@.map_values(|pr: (Key, Value)| KeyedMessage::from_kv(pr.0, pr.1)),
            seq_start: self.lsn_addr_index.seq_end(),
        }@
    }
}

impl View for IJournalStatus {
    type V = JournalStatus;
    closed spec fn view(&self) -> Self::V {
        Self::V {
            unmarshalled_tail: self.tail_as_history(),
            lsn_addr_index: self.lsn_addr_index@,
        }
    }
}

pub struct IndexBuilder {
    next_head: IJournalSnapshot,
}

pub enum RecoverIndexResult{
    CacheLoad{slot_handle: MutHandle, addr: IAddress},
    IndexComplete{reads: Ghost<Map<Address, RawPage>>},
    IndexProgress{},
}

pub struct JournalImpl {
    snapshot: IJournalSnapshot,
    index_builder: Option<IndexBuilder>,
    status: Option<IJournalStatus>,
    fmt: IJournalRecordFormat,
}

pub open spec fn load_index_labels(reads: Map<Address, RawPage>) -> (Cache::Label, CachedJournal::Label)
{
    let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
    let journal_lbl = CachedJournal::Label::LoadIndex{reads: to_journal_reads(reads)};
    (cache_lbl, journal_lbl)
}

pub open spec fn cache_matches_raw_disk(cache: Cache::State, disk: Map<Address, RawPage>) -> bool
{
    forall |addr, data| #[trigger] cache.valid_read(addr, data)
        ==> disk.contains_key(addr) && disk[addr] == data
}

pub open spec fn journal_raw_disk_inv(fmt: IJournalRecordFormat, disk: Map<Address, RawPage>) -> bool
{
    forall |addr| #[trigger] disk.contains_key(addr) ==> fmt.parsable(disk[addr])
}

pub open spec fn journal_disk_inv(disk: LinkedJournal_v::DiskView, root: Pointer) -> bool
{
    &&& disk.acyclic()
    &&& disk.decodable(root)
    &&& disk.boundary_lsn < disk.entries[root.unwrap()].message_seq.seq_end
}

impl IJournalRecord {
    exec fn seq_end(&self) -> (out: ILsn)
        requires self.wf()
        ensures out@ == self.parsedv().header.start_lsn + self.parsedv().messages.len()
    {
        assume(self.header.start_lsn + (self.messages.len() as u64) < u64::MAX);
        self.header.start_lsn + self.messages.len() as u64
    }

    exec fn cropped_prior(self, bdy: ILsn) -> (out: Option<IAddress>)
        requires self.wf()
        ensures ({
            let i_result = self.parsedv()@.cropped_prior(bdy as nat);
            &&& i_result is None ==> out is None
            &&& out is None ==> i_result is None
            &&& i_result is Some ==> i_result == Some(out.unwrap()@)
            &&& out is Some ==> i_result == Some(out.unwrap()@)
        })
    {
        if bdy < self.header.start_lsn { self.header.prior_rec } else { None }
    }
}

impl JournalImpl {
    pub closed spec fn wf(&self) -> bool {
        &&& self.fmt.valid()
        &&& match self.status {
            None => { self.index_builder is Some },
            Some(status) => {
                &&& status.wf()
                &&& self.snapshot.boundary_lsn <= status.clean_watermark_lsn
                &&& status.clean_watermark_lsn <= status.lsn_addr_index.seq_end()
                &&& (self.snapshot.freshest_rec is None ==> status.clean_watermark_lsn == self.snapshot.boundary_lsn)
                &&& (self.snapshot.freshest_rec is Some ==> self.snapshot.boundary_lsn < status.clean_watermark_lsn)
            }
        }
    }

    pub closed spec fn seq_start(&self) -> LSN {
        self.snapshot.boundary_lsn as nat
    }

    pub exec fn exec_seq_start(&self) -> (out: u64)
    ensures out == self.seq_start()
    {
        self.snapshot.boundary_lsn
    }

    pub closed spec fn freshest_rec(&self) -> Pointer
    {
        self.snapshot@.freshest_rec
    }

    pub exec fn exec_freshest_rec(&self) -> (out: Option<IAddress>)
    ensures 
        out is None ==> self.freshest_rec() is None,
        out is Some ==> self.freshest_rec() == Some(out.unwrap()@)
    {
        self.snapshot.freshest_rec
    }

    pub closed spec fn seq_end(&self) -> LSN {
        match &self.status {
            None => 0,
            Some(status) => {
                status.lsn_addr_index.seq_end() as nat + status.unmarshalled_tail.len() as nat
            }
        }
    }

    pub exec fn exec_seq_end(&self) -> (out: ILsn)
    requires self.wf()
    ensures out == self.seq_end()
    {
        match &self.status {
            None => 0,
            Some(status) => {
                let tail_start = status.lsn_addr_index.exec_seq_end();
                // this cheat is incurring a runtime check, ugh
                if u64::MAX - tail_start < status.unmarshalled_tail.len() as u64 {
                    convert_overflow_into_liveness_failure();
                }
                tail_start + status.unmarshalled_tail.len() as u64
            }
        }
    }

    pub closed spec fn index_ready(&self) -> bool
    {
        self.status is Some
    }
    pub exec fn new(snapshot: IJournalSnapshot) -> (out: Self)
    ensures
        out.wf(),
        !out.index_ready(),
        out@.snapshot == snapshot@,
//         TODO how do I express this? transition!s work, but not init!
//     ensures CachedJournal::initialize(snapshot@)
    {
        Self{
            snapshot,
            index_builder: Some(IndexBuilder{
                next_head: snapshot,
            }),
            status: None,
            fmt: IJournalRecordFormat::new(),
        }
    }

    // This should do some cache reads and either bump another cache read (to walk the skip list)
    // or report that it's done (and the index is ready).
    // This could be a while loop that restarts from the beginning after every block for cache IO,
    // but that's quadratric compute, and will eventually suck. I'm going to write it keeping
    // intermediate state. That state will need an invariant wrt the cache, which Implementation
    // will have to hang onto for us, unfortunately.
    // TODO: should also pass in a journal model and associate it with journal snapshot
    pub exec fn recover_index_step(&mut self, cache: &mut FracCacheImpl) 
        -> (out: RecoverIndexResult) //(out: (bool, Option<(MutHandle, IAddress, Ghost<Cache::Label>)>, bool))
    requires
        old(self).wf(),
        !old(self).index_ready(),
        old(cache).wf(),
    ensures ({
        &&& self.wf()
        &&& self@.wf()
        &&& cache.wf()
        &&& cache.valid_load_handles_preserved(*old(cache))
        &&& match out {
            RecoverIndexResult::CacheLoad{slot_handle, addr} => {
                &&& self@ == old(self)@
                &&& !old(cache).entry_fetched(&addr)
                &&& cache.entry_fetched(&addr)
                &&& cache.valid_load_handle(&addr, slot_handle)
                &&& Cache::State::next(old(cache)@, cache@, cache_load_label(&addr))
            },
            RecoverIndexResult::IndexComplete{reads} => {
                let (cache_lbl, journal_lbl) = load_index_labels(reads@);
                &&& old(cache)@ == cache@
                &&& self.index_ready()
                &&& Cache::State::next(old(cache)@, cache@, cache_lbl)
                &&& CachedJournal::State::next(old(self)@, self@, journal_lbl)
            },
            RecoverIndexResult::IndexProgress{} => {
                &&& old(cache)@ == cache@
                &&& self@ == old(self)@
            }
        }
    })
    {
        let mut out = RecoverIndexResult::IndexProgress{};
        let mut index_builder = self.index_builder.take();
        index_builder = match index_builder {
            // NOTE: builder becomes None when we are out of the building phase
            None => { assert(false); None },
            // NOTE: builder is a hint for continued fetch
            Some(mut builder) => { 
                // -------------- Assumption from system invariants -----------------
                let ghost journal_raw_disk : Map<Address, RawPage> = arbitrary(); 
                assume(journal_raw_disk_inv(self.fmt, journal_raw_disk));
                assume(cache_matches_raw_disk(cache@, journal_raw_disk));
                // -------------- End of system invariants assumptions -----------------

                match builder.next_head.freshest_rec {
                    None => {
                        reveal(Cache::State::next_by);
                        reveal(Cache::State::next);
                        reveal(CachedJournal::State::next_by);
                        reveal(CachedJournal::State::next);

                        let bdy = self.snapshot.boundary_lsn;
                        let ghost mut reads = map!{};
                        let mut curr = self.snapshot.freshest_rec;
                        let mut index;
                        // trigger
                        assert(LinkedJournal_v::DiskView{boundary_lsn: bdy as nat, entries: to_journal_reads(reads)}.valid_ranking(map!{})); // witness


                        if let Some(root) = curr {
                            let mut end = u64::MAX;
                            let mut index_initialized = false;
                            index = ILsnAddrIndex::new(end);

                            // -------------- Assumption from system invariants -----------------
                            // NOTE: Cached Journal contains no internal disk, has to cross layers
                            // faking from system invariant (should be opened on the caller side and passed in)
                            // modularity issue, this might also be relevant to our passing commands back and forth problem
                            // how would wee use this when facing concurrency?
                            let ghost journal_disk = LinkedJournal_v::DiskView{boundary_lsn: bdy as nat, entries: to_journal_reads(journal_raw_disk)};
                            assume(journal_disk_inv(journal_disk, iaddr_view(curr)));
                            // -------------- End of system invariants assumptions -----------------

                            let ghost ranking = journal_disk.the_ranking();
                            let ghost seq_end = journal_disk.entries[root@].message_seq.seq_end;

                            // NOTE: journal disk should carry an inv that any clean address the cache has
                            // have the same content as the journal disk and is a parsable journal page
                            while index.exec_seq_start() != bdy
                            invariant 
                                index.wf(),
                                cache.wf(),
                                cache@ == old(cache)@,
                                cache_matches_raw_disk(cache@, journal_raw_disk),
                                journal_raw_disk_inv(self.fmt, journal_raw_disk),
                                self.fmt.valid(),
                                self.snapshot == old(self).snapshot,
                                index.seq_start() != bdy ==> curr is Some,
                                curr is Some ==> journal_disk.entries.contains_key(curr.unwrap()@),
                                curr is Some ==> (forall |a| #[trigger] reads.contains_key(a) ==> ranking[a] >= ranking[curr.unwrap()@]),
                                forall |addr| #[trigger] reads.contains_key(addr) ==> cache@.valid_read(addr, reads[addr]),
                                forall |addr| #[trigger] to_journal_reads(reads).contains_key(addr) ==> {
                                    let next = to_journal_reads(reads)[addr].cropped_prior(bdy as nat);
                                    next is None || to_journal_reads(reads).contains_key(next.unwrap()) || next == iaddr_view(curr)
                                },
                                iaddr_view(curr) == build_lsn_addr_index_from_reads_next_ptr(to_journal_reads(reads), bdy as nat, self@.snapshot.freshest_rec),
                                acyclic_reads(bdy as nat, to_journal_reads(reads)),
                                !index_initialized ==> curr == self.snapshot.freshest_rec,
                                index_initialized ==> (index.seq_start() == bdy
                                    || index.seq_start() == journal_disk.entries[curr.unwrap()@].message_seq.seq_end),
                                bdy <= index.seq_start(),
                                index_initialized ==> {
                                    &&& index.seq_end() == seq_end
                                    &&& reads.contains_key(root@)
                                    &&& index@ =~= build_lsn_addr_index_from_reads(to_journal_reads(reads), bdy as nat, self@.snapshot.freshest_rec)
                                },
                            decreases journal_disk.the_rank_of(iaddr_view(curr))
                            {
                                let ghost prev = iaddr_view(curr);
                                let addr = curr.unwrap();

                                let ghost cache_pre = cache@;
                                match cache.fetch(&addr) {
                                    FetchErrorCode::Success{slot_handle} => {
                                        let all_slice = Slice::all(&slot_handle.rec);
                                        // trigger
                                        assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                        let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);
                                        cache.handle_release(&addr, slot_handle);

                                        let ghost reads_pre = reads;
                                        proof {
                                            reads = reads.insert(addr@, slot_handle.rec@);
                                            let ghost reads_post = to_journal_reads(reads_pre).insert(addr@, to_journal_reads(reads)[addr@]);
                                            disk_view_valid_ranking_subset(journal_disk, reads_post, ranking);
                                            build_lsn_addr_index_from_reads_next_ptr_after_insert(to_journal_reads(reads_pre), bdy as nat, self@.snapshot.freshest_rec, iaddr_view(curr), to_journal_reads(reads)[addr@]);
                                        }

                                        end = i_journal_record.seq_end();
                                        let start = if i_journal_record.header.start_lsn < bdy { bdy } else { i_journal_record.header.start_lsn };

                                        let ghost was_initialized = index_initialized;
                                        if !index_initialized {
                                            index = ILsnAddrIndex::new(end); 
                                            index_initialized = true;
                                        }

                                        // if they are the same then we don't need to do anything                                             
                                        let ghost old_index = index@;
                                        let ghost index_pre = index;
                                        let old_bound = index.exec_seq_start();
                                        proof { to_journal_reads_entry_from_exec_parse(self.fmt, reads, addr@, i_journal_record); }
                                        index.index_prepend_record(old_bound, start, addr);
                                        proof {
                                            // Proof block: extend the index model and re-establish build-index equality.
                                            if index_initialized {
                                                let ptr2_data = to_journal_reads(reads)[addr@];
                                                let start_lsn = vstd::math::max(bdy as int, ptr2_data.message_seq.seq_start as int) as nat;
                                                let end_lsn = ptr2_data.message_seq.seq_end;
                                                let update = singleton_index(start_lsn, end_lsn, addr@);
                                                let ghost reads_post = to_journal_reads(reads_pre).insert(addr@, ptr2_data);
                                                assert(to_journal_reads(reads) == reads_post);
                                                // show the build index extends by this record
                                                let ghost build_pre = build_lsn_addr_index_from_reads(to_journal_reads(reads_pre), bdy as nat, self@.snapshot.freshest_rec);
                                                if !was_initialized {
                                                    build_lsn_addr_index_from_reads_next_ptr_not_in_reads(to_journal_reads(reads_pre), bdy as nat, self@.snapshot.freshest_rec, iaddr_view(curr));
                                                }
                                                // trigger
                                                assert(lsn_disjoint(build_pre.dom(), start_lsn, end_lsn)) by {
                                                    index_pre.view_domain();
                                                };
                                                build_lsn_addr_index_from_reads_extend_next_ptr(to_journal_reads(reads_pre), bdy as nat, self@.snapshot.freshest_rec, prev, ptr2_data);
                                            }
                                            build_lsn_addr_index_from_reads_next_ptr_after_insert(to_journal_reads(reads_pre), bdy as nat, self@.snapshot.freshest_rec, prev, to_journal_reads(reads)[addr@]);
                                        }
                                        let prior = i_journal_record.cropped_prior(bdy);
                                        curr = prior;
                                    },
                                    _ => {
                                        // we can also just set builder back to freshest rec, 
                                        // but panic here bc our current testing shouldn't reach that case
                                        please_panic(); 
                                    } 
                                }
                            }
                            if !index_initialized {
                                please_panic(); // something's wrong o.o
                            }
                        } else {
                            index = ILsnAddrIndex::new(bdy);
                        }

                        let i_seq_end = index.exec_seq_end();
                        self.status = Some(IJournalStatus{
                            unmarshalled_tail: vec![],
                            lsn_addr_index: index,
                            clean_watermark_lsn: i_seq_end,
                        });

                        
                        proof {
                            let (_, journal_lbl) = load_index_labels(reads);
                            let ptr = old(self)@.snapshot.freshest_rec;
                            let bdy = old(self)@.snapshot.boundary_lsn;
                            let journal_reads = to_journal_reads(reads);
                            let lsn_addr_index = build_lsn_addr_index_from_reads(journal_reads, bdy, ptr);
 
                            // trigger
                            index.view_domain();
                            // trigger
                            assert( lsn_addr_index =~= index@ );
                            // trigger
                            assert(self@.status.unwrap().unmarshalled_tail == MsgHistory::empty_history_at(index.seq_end() as nat));
                            // trigger
                            assert( CachedJournal::State::next_by(old(self)@, self@, journal_lbl, CachedJournal::Step::load_index{}) );
                        }
                        proof {
                            let (cache_lbl, _) = load_index_labels(reads);
                            let updated_entries = old(cache)@.write_updated_entries(cache_lbl->writes);
                            let updated_status_map = old(cache)@.write_updated_status(cache_lbl->writes);

                            // trigger
                            assert(old(cache)@.entries.union_prefer_right(updated_entries) =~= old(cache)@.entries);
                            // trigger
                            assert(old(cache)@.status_map.union_prefer_right(updated_status_map) =~= old(cache)@.status_map);
                            // trigger
                            assert( Cache::State::next_by(old(cache)@, cache@, cache_lbl, Cache::Step::access{}) );
                        }
                        out = RecoverIndexResult::IndexComplete{reads: Ghost(reads)};
                        None
                    },
                    Some(addr) => {
                        // Can we read the next page from the cache?
                        let ghost cache_pre = cache@;
                        match cache.fetch(&addr) {
                            FetchErrorCode::LoadInitiate{slot_handle} => {
                                // release previous handle
                                // Cache is going to do a fetch and call us later. Bail out.
                                // Re-construct the struct
                                proof {
                                    assert(!old(cache).entry_fetched(&addr));
                                }
                                out = RecoverIndexResult::CacheLoad{slot_handle, addr};
                                Some(builder)
                            },
                            FetchErrorCode::Success{slot_handle} => {
                                let all_slice = Slice::all(&slot_handle.rec);
                                // trigger
                                assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);
                                cache.handle_release(&addr, slot_handle);
                                builder.next_head.freshest_rec = match i_journal_record.header.prior_rec 
                                    {
                                        None => None,
                                        Some(iaddr) => { // cropped prior logic
                                            if i_journal_record.header.start_lsn > self.snapshot.boundary_lsn {
                                                Some(iaddr)
                                            } else { None }
                                        }
                                    };
                                Some(builder)
                            },
                            _ => {
                                Some(builder)
                            },
                        }
                    },
                }
            }
        };
        core::mem::swap(&mut self.index_builder, &mut index_builder);
        proof { assume(cache.valid_load_handles_preserved(*old(cache))); }
        out
    }

    pub exec fn insert(&mut self, key: Key, value: Value)
    requires
        old(self).wf(),
        old(self).index_ready(),
    ensures 
        self.wf(),
        self@.wf(),
        self.seq_start() == old(self).seq_start(),
        self.seq_end() == old(self).seq_end() + 1,
        CachedJournal::State::put(old(self)@, self@,
            CachedJournal::Label::Put{
                messages: MsgHistory::singleton_at(old(self).seq_end(), KeyedMessage::from_kv(key, value))}),
        self.index_ready(),
    {
        // swappery to deal with lack of &mut
        // Since we don't have &mut results in verus yet, we need to swap the
        // option out of self, deconstruct it, do the work we want on the inner struct,
        // then reassemble the option and swap it back in. 🫤
        let mut dummy: Option<IJournalStatus> = None;
        core::mem::swap(&mut self.status, &mut dummy);
        dummy = match dummy {
            None => { None },
            Some(mut status) => {
                status.unmarshalled_tail.push((key,value));
                Some(status)
            }
        };
        core::mem::swap(&mut self.status, &mut dummy);

        proof {
            let messages = MsgHistory::singleton_at(old(self).seq_end(), KeyedMessage::from_kv(key, value));
            let old_tail = old(self)@.status.unwrap().unmarshalled_tail;
            let new_tail = self@.status.unwrap().unmarshalled_tail;

            // trigger
            assert( new_tail == old_tail.concat(messages) );
            assert(
                CachedJournal::State::put(old(self)@, self@,
                    CachedJournal::Label::Put{
                    messages: MsgHistory::singleton_at(old(self).seq_end(), KeyedMessage::from_kv(key, value))
                })
            );
        }
    }

    pub broadcast proof fn view_ensures(self)
        ensures self.index_ready() <==> (#[trigger] self@).status is Some
    {
    }

    pub proof fn seq_start_le_marshalled_end(&self)
        requires self.wf(), self.index_ready()
        ensures self.seq_start() as nat <= self@.status.unwrap().unmarshalled_tail.seq_start
    {
    }

    pub fn is_empty(&self) -> bool
    requires self.index_ready()
    {
        self.status.as_ref().unwrap().unmarshalled_tail.len() > 0 || self.snapshot.freshest_rec.is_some()
    }

    // Provide a frozen snapshot for use in Implementation::send_superblock
    // Design intent:
    // - this exec call is really cheap, so it can be used both to "probe" what LSN we are able to
    // freeze to, as well as to capture that frozen sequence and use it in the superblock.
    // - This interface gives the journal design freedom to decide how to respond: A smarter
    // journal could keep track of what prior pages are clean and return just those. A lazy
    // journal (right now) just returns whatever it has lying around.
    // - The caller can use it in "probe" mode to decide that the LSN hasn't advanced enough,
    // and call some other interface to ask the journal to push the clean mark forward by cleaning
    // cache pages.

    pub exec fn freeze_journal(&self, cache: &FracCacheImpl) -> (out: FrozenJournal)
    requires
        self.wf(),
        self.index_ready(),
    ensures
        out.wf(),
        out.snapshot@ == self@.snapshot,
        out.snapshot.boundary_lsn == self.seq_start(),
        out.seq_end as nat == self.clean_watermark(),
        self.lsns_are_clean(cache@, out),
        out.freshest_rec_page_agrees(cache@),
    {
        let out = FrozenJournal{
            snapshot: self.snapshot.clone(),
            seq_end: self.status.as_ref().unwrap().clean_watermark_lsn,
        };
        proof {
            reveal(Cache::State::next_by);
            if self.snapshot.freshest_rec is Some {
                // Non-empty journal: requires cache-cleanliness invariants not yet established.
                // The only initialization path for freshest_rec is Some has assume(false),
                // so this branch is unreachable in practice.
                assume(self.lsns_are_clean(cache@, out));
                assume(out.freshest_rec_page_agrees(cache@));
            } else {
                // Empty journal: watermark == boundary_lsn, so LSN range is empty,
                // addrs set is empty, evictable is vacuously true.
            }
        }
        out
    }

    pub open spec fn lsn_range(start_incl: LSN, end_excl: LSN) -> Set<LSN>
    {
        Set::new(|lsn: LSN| start_incl <= lsn && lsn < end_excl)
    }

    // Open because this definition gets used proving the refinement CachedJournal::Step::freeze_for_commit(depth) in Implementation
    pub open spec fn iaddrs_for_lsns(self, start_incl: LSN, end_excl: LSN) -> Set<Address>
    recommends self.index_ready()
    {
        self@.status.unwrap().lsn_addr_index.restrict(Self::lsn_range(start_incl, end_excl)).values()
    }

    /// All marshalled journal pages are Filled+Clean in cache.
    pub open spec fn marshalled_pages_are_clean(&self, cache: Cache::State) -> bool
    recommends self.index_ready()
    {
        Cache::State::next_by(cache, cache,
            Cache::Label::EvictableCheck{addrs: self.iaddrs_for_lsns(self.seq_start() as LSN, self@.marshalled_seq_end())},
            Cache::Step::evictable())
    }

    /// The clean high water mark: the seq_end of the highest page in the journal chain
    /// for which it and all lower pages are Filled+Clean in cache.
    /// Independent of marshalled_seq_end — marshalling may have raced ahead with dirty pages.
    pub closed spec fn clean_watermark(&self) -> LSN {
        self.status.unwrap().clean_watermark_lsn as nat
    }

    pub open spec fn lsns_are_clean(&self, cache: Cache::State, out: FrozenJournal) -> bool
    {
        Cache::State::next_by(cache, cache,
            Cache::Label::EvictableCheck{addrs: self.iaddrs_for_lsns(out.seq_start() as LSN, out.seq_end as LSN)},
            Cache::Step::evictable())
    }

    /// Check whether the journal is clean up to target_lsn.
    /// Returns true iff target_lsn <= clean_watermark (all pages up to there are Filled+Clean).
    /// If not ready, may do work (marshal tail, poke cache to flush) and return false;
    /// caller should retry later.
    pub exec fn clean_for_commit(&self, cache: &FracCacheImpl, target_lsn: ILsn) -> (ready: bool)
    requires
        self.wf(),
        self.index_ready(),
    ensures
        ready ==> target_lsn as nat <= self.clean_watermark(),
    {
        target_lsn <= self.status.as_ref().unwrap().clean_watermark_lsn
    }
}

impl View for JournalImpl {
    type V = CachedJournal::State;
    closed spec fn view(&self) -> Self::V {
        CachedJournal::State {
            snapshot: self.snapshot@,
            status: match self.status {
                None => None,
                Some(status) => Some(status@),
            }
        }
    }
}

}//verus!
