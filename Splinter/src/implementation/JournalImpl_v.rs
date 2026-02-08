// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
// use vstd::hash_map::HashMapWithView;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::*;
use crate::marshalling::IntegerMarshalling_v::IntFormat;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::marshalling::ResizableUniformSizedSeq_v::ResizableUniformSizedElementSeqFormat;
use crate::marshalling::KeyedMessageFormat_v::KeyedMessageFormat;
use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::AsyncDisk_t::RawPage;
use crate::implementation::AtomicState_v::{to_journal_reads, raw_page_to_record};
use crate::implementation::OverflowFiction_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::disk::GenericDisk_v::{Address, IAddress, Pointer};
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
        &&& self.lsn_addr_index.ascending
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
        &&& match out {
            RecoverIndexResult::CacheLoad{slot_handle, addr} => {
                &&& self@ == old(self)@
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

                        assert(LinkedJournal_v::DiskView{boundary_lsn: bdy as nat, entries: to_journal_reads(reads)}.valid_ranking(map!{})); // witness
                        assert(acyclic_reads(bdy as nat, to_journal_reads(reads)));

                        if let Some(root) = curr {
                            let mut end = u64::MAX;
                            let mut index_initialized = false;
                            index = ILsnAddrIndex::new(end, false);

                            // NOTE: Cached Journal contains no internal disk, has to cross layers
                            // faking from system invariant (should be opened on the caller side and passed in)
                            // modularity issue, this might also be relevant to our passing commands back and forth problem
                            // how would wee use this when facing concurrency?
                            let ghost journal_disk = LinkedJournal_v::DiskView{boundary_lsn: self.snapshot@.boundary_lsn, entries: arbitrary()};
                            assume(journal_disk.acyclic());
                            assume(journal_disk.decodable(iaddr_view(curr)));

                            let ghost seq_end = journal_disk.entries[root@].message_seq.seq_end;
                            assume(bdy < seq_end);
                            assert(bdy <= index.seq_start());

                            // NOTE: journal disk should carry an inv that any clean address the cache has
                            // have the same content as the journal disk and is a parsable journal page
                            while index.exec_seq_start() != bdy
                            invariant 
                                index.wf(),
                                !index.ascending,
                                cache.wf(),
                                cache@ == old(cache)@,
                                bdy == self.snapshot.boundary_lsn,
                                self.fmt == old(self).fmt,
                                self.snapshot == old(self).snapshot,
                                curr is Some,
                                journal_disk.entries.contains_key(curr.unwrap()@),
                                journal_disk.wf(),
                                journal_disk.acyclic(),
                                journal_disk.boundary_lsn == bdy as nat,
                                forall |addr| #[trigger] reads.contains_key(addr) ==> cache@.valid_read(addr, reads[addr]),
                                to_journal_reads(reads) <= journal_disk.entries,
                                forall |addr| #[trigger] reads.contains_key(addr) ==> self.fmt.parsable(reads[addr]),
                                forall |addr| #[trigger] to_journal_reads(reads).contains_key(addr) ==> {
                                    let next = to_journal_reads(reads)[addr].cropped_prior(bdy as nat);
                                    next is None || to_journal_reads(reads).contains_key(next.unwrap()) || next == iaddr_view(curr)
                                },
                                iaddr_view(curr) == build_lsn_addr_index_from_reads_next_ptr(to_journal_reads(reads), bdy as nat, self@.snapshot.freshest_rec),
                                acyclic_reads(bdy as nat, to_journal_reads(reads)),
                                !index_initialized ==> curr == self.snapshot.freshest_rec,
                                index_initialized ==> {
                                    &&& index.seq_end() == seq_end
                                    &&& reads.contains_key(root@)
                                    &&& index@ =~= build_lsn_addr_index_from_reads(to_journal_reads(reads), bdy as nat, self@.snapshot.freshest_rec)
                                },
                            decreases journal_disk.the_rank_of(iaddr_view(curr))
                            {
                                let ghost prev = iaddr_view(curr);
                                let addr = curr.unwrap();
                                match cache.fetch(&addr) {
                                    FetchErrorCode::Success{slot_handle} => {
                                        let all_slice = Slice::all(&slot_handle.rec);
                                        assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                        // NOTE: journal disk should say that any address that live here is parsable as a journal page
                                        assume( self.fmt.parsable(all_slice@.i(slot_handle.rec@)) );

                                        // got the page, parse makes a copy (likely needs a partial parse spec later)
                                        let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);
                                        cache.handle_release(&addr, slot_handle);

                                        let ghost reads_pre = reads;
                                        proof {
                                            reads = reads.insert(addr@, slot_handle.rec@);
                                            assume(acyclic_reads(bdy as nat, to_journal_reads(reads))); // system invariant
                                            assume(to_journal_reads(reads)[addr@] == journal_disk.entries[addr@]); // system invariant
                                            assert(self.fmt.parsable(reads[addr@]));
                                            assert forall |k| #[trigger] reads.contains_key(k)
                                            implies self.fmt.parsable(reads[k]) by {
                                                if k == addr@ {
                                                    assert(self.fmt.parsable(reads[addr@]));
                                                } else {
                                                    assert(reads_pre.contains_key(k));
                                                    assert(self.fmt.parsable(reads_pre[k]));
                                                }
                                            };
                                            // Maintain cache valid_read invariant.
                                            // assert forall |k| #[trigger] reads.contains_key(k)
                                            // implies cache@.valid_read(k, reads[k]) by {
                                            //     if k == addr@ {
                                            //         FracCacheImpl::lookup_map_bijection_lemma();
                                            //         assert(cache.entry_fetched(&addr));
                                            //         assert(cache@.lookup_map.contains_key(addr@));
                                            //         let slot = cache@.lookup_map[addr@];
                                            //         assert(cache@.entries[slot] is Filled);
                                            //         assert(cache@.entries[slot].get_addr() == addr@);
                                            //         assert(cache@.entries[slot] is Filled);
                                            //         assert(cache@.entries[slot]->data == reads[addr@]);
                                            //         assert(cache@.valid_read(addr@, reads[addr@]));
                                            //     } else {
                                            //         assert(reads_pre.contains_key(k));
                                            //         assert(cache@.valid_read(k, reads_pre[k]));
                                            //     }
                                            // };
                                            // Connect parsed exec record to ghost journal reads.
                                            to_journal_reads_entry_from_exec_parse(
                                                self.fmt,
                                                reads,
                                                addr@,
                                                i_journal_record,
                                            );
                                            assert(to_journal_reads(reads)[addr@] == i_journal_record.parsedv().view());
                                            assert(to_journal_reads(reads) <= journal_disk.entries) by {
                                                assert forall |k| #[trigger] to_journal_reads(reads).contains_key(k)
                                                implies journal_disk.entries.contains_key(k)
                                                    && to_journal_reads(reads)[k] == journal_disk.entries[k] by {
                                                    if k == addr@ {
                                                        assert(journal_disk.entries.contains_key(addr@));
                                                    } else {
                                                        assert(to_journal_reads(reads_pre).contains_key(k));
                                                        assert(journal_disk.entries.contains_key(k));
                                                        assert(to_journal_reads(reads_pre)[k] == journal_disk.entries[k]);
                                                    }
                                                };
                                            }
                                            assert(
                                                iaddr_view(curr)
                                                    == build_lsn_addr_index_from_reads_next_ptr(
                                                        to_journal_reads(reads_pre),
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    )
                                            );
                                            assume(acyclic_reads(
                                                bdy as nat,
                                                to_journal_reads(reads_pre)
                                                    .insert(addr@, to_journal_reads(reads)[addr@]),
                                            ));
                                            assume(
                                                to_journal_reads(reads)[addr@].cropped_prior(bdy as nat) is None
                                                || !to_journal_reads(reads_pre)
                                                    .contains_key(to_journal_reads(reads)[addr@].cropped_prior(bdy as nat).unwrap())
                                            );
                                            build_lsn_addr_index_from_reads_next_ptr_after_insert(
                                                to_journal_reads(reads_pre),
                                                bdy as nat,
                                                self@.snapshot.freshest_rec,
                                                iaddr_view(curr),
                                                to_journal_reads(reads)[addr@],
                                            );
                                        }

                                        end = i_journal_record.seq_end();
                                        let start = if i_journal_record.header.start_lsn < bdy { bdy } else { i_journal_record.header.start_lsn };

                                        let ghost was_initialized = index_initialized;
                                        if !index_initialized {
                                            // TODO: true from system invariant, we are looking at the seq_end at freshest rec, 
                                            assume(bdy < end);
                                            index = ILsnAddrIndex::new(end, false); 
                                            index_initialized = true;
                                            assert(index@ == Map::<LSN, Address>::empty());
                                        } else {
                                            // TODO: true from system invariant, we are following pointer always gets smaller lsns
                                            // assume(end <= index.seq_start());
                                            // assert(i_journal_record.header.start_lsn <= end);
                                            // assert(bdy < end);
                                        }

                                        // if they are the same then we don't need to do anything                                             
                                        let ghost old_index = index@;
                                        let ghost index_pre = index;
                                        let old_bound = index.exec_seq_start();
                                        assert(index_pre.wf());
                                        assert(old_bound == index_pre.seq_start());
                                        assume(start < old_bound);
                                        // adjacency of journal records
                                        assume(end == old_bound);
                                        index.index_extend_bound(old_bound, start, addr);
                                        proof {
                                            if index_initialized {
                                                let ptr2_data = to_journal_reads(reads)[addr@];
                                                let start_lsn = vstd::math::max(bdy as int, ptr2_data.message_seq.seq_start as int) as nat;
                                                let end_lsn = ptr2_data.message_seq.seq_end;
                                                let update = singleton_index(start_lsn, end_lsn, addr@);
                                                assert(start_lsn == start as nat);
                                                assert(end_lsn == end as nat);
                                                assert(index@ == lsn_addr_index_append_record(
                                                    old_index,
                                                    start_lsn,
                                                    end_lsn,
                                                    addr@,
                                                ));
                                                assume(lsn_disjoint(old_index.dom(), start_lsn, end_lsn));
                                                let ghost reads_post =
                                                    to_journal_reads(reads_pre).insert(addr@, ptr2_data);
                                                assert(to_journal_reads(reads) == reads_post) by {
                                                    assert forall |k| #[trigger] to_journal_reads(reads).contains_key(k)
                                                    implies reads_post.contains_key(k)
                                                        && to_journal_reads(reads)[k] == reads_post[k] by {
                                                        if k == addr@ {
                                                            assert(reads_post.contains_key(k));
                                                            assert(reads_post[k] == ptr2_data);
                                                        } else {
                                                            assert(reads_pre.contains_key(k));
                                                            assert(to_journal_reads(reads_pre).contains_key(k));
                                                            assert(reads_post.contains_key(k));
                                                            assert(reads_post[k] == to_journal_reads(reads_pre)[k]);
                                                            assert(to_journal_reads(reads)[k] == to_journal_reads(reads_pre)[k]);
                                                        }
                                                    };
                                                    assert forall |k| #[trigger] reads_post.contains_key(k)
                                                    implies to_journal_reads(reads).contains_key(k)
                                                        && reads_post[k] == to_journal_reads(reads)[k] by {
                                                        if k == addr@ {
                                                            assert(to_journal_reads(reads).contains_key(k));
                                                            assert(reads_post[k] == ptr2_data);
                                                        } else {
                                                            assert(reads_pre.contains_key(k));
                                                            assert(to_journal_reads(reads_pre).contains_key(k));
                                                            assert(to_journal_reads(reads).contains_key(k));
                                                            assert(reads_post[k] == to_journal_reads(reads_pre)[k]);
                                                            assert(to_journal_reads(reads)[k] == to_journal_reads(reads_pre)[k]);
                                                        }
                                                    };
                                                };
                                                // show the build index extends by this record
                                                assume(lsn_disjoint(
                                                    build_lsn_addr_index_from_reads(
                                                        to_journal_reads(reads_pre),
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    ).dom(),
                                                    start_lsn,
                                                    end_lsn,
                                                ));
                                                build_lsn_addr_index_from_reads_extend_next_ptr(
                                                    to_journal_reads(reads_pre),
                                                    bdy as nat,
                                                    self@.snapshot.freshest_rec,
                                                    prev,
                                                    ptr2_data,
                                                );
                                                assert(
                                                    build_lsn_addr_index_from_reads(
                                                        to_journal_reads(reads_pre),
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    )
                                                    .union_prefer_right(singleton_index(start_lsn, end_lsn, addr@))
                                                    =~= build_lsn_addr_index_from_reads(
                                                        reads_post,
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    )
                                                );
                                                assert(build_lsn_addr_index_from_reads(
                                                    reads_post,
                                                    bdy as nat,
                                                    self@.snapshot.freshest_rec,
                                                ) =~= build_lsn_addr_index_from_reads(
                                                    to_journal_reads(reads),
                                                    bdy as nat,
                                                    self@.snapshot.freshest_rec,
                                                ));

                                                if was_initialized {
                                                    assert(old_index =~= build_lsn_addr_index_from_reads(
                                                        to_journal_reads(reads_pre),
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    ));
                                                } else {
                                                    assert(curr == self.snapshot.freshest_rec);
                                                    assert(self.snapshot.freshest_rec is Some);
                                                    assert(self.snapshot.freshest_rec.unwrap() == root);
                                                    assert(addr@ == root@);
                                                    assert(iaddr_view(curr) == self@.snapshot.freshest_rec);
                                                    build_lsn_addr_index_from_reads_next_ptr_not_in_reads(
                                                        to_journal_reads(reads_pre),
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                        iaddr_view(curr),
                                                    );
                                                    assert(!to_journal_reads(reads_pre).contains_key(iaddr_view(curr).unwrap()));
                                                    assert(build_lsn_addr_index_from_reads(
                                                        to_journal_reads(reads_pre),
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    ) == Map::<LSN, Address>::empty());
                                                    assert(old_index == Map::<LSN, Address>::empty());
                                                }
                                                assert(index@ == old_index.union_prefer_right(update));
                                                assert(old_index.union_prefer_right(update)
                                                    =~= build_lsn_addr_index_from_reads(
                                                        reads_post,
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    ));
                                                assert(index@ =~= build_lsn_addr_index_from_reads(
                                                    to_journal_reads(reads),
                                                    bdy as nat,
                                                    self@.snapshot.freshest_rec,
                                                ));

                                                if was_initialized {
                                                    assert(index_pre.seq_end() == seq_end);
                                                } else {
                                                    assert(ptr2_data.message_seq.seq_end == seq_end);
                                                    assert(index_pre.seq_end() == end);
                                                    assert(end as nat == seq_end);
                                                }
                                                assert(!index_pre.ascending);
                                                assert(!index.ascending);
                                                assert(index.seq_end() == index_pre.seq_end());
                                                assert(index.seq_end() == seq_end);
                                            }
                                        }
                                        let prior = i_journal_record.cropped_prior(bdy);
                                        curr = prior;

                                        proof {
                                            // Relate curr to the cropped_prior of the inserted record.
                                            let ghost i_result = i_journal_record.parsedv()@.cropped_prior(bdy as nat);
                                            if i_result is None {
                                                assert(prior is None);
                                                assert(iaddr_view(prior) is None);
                                            } else {
                                                if prior is None {
                                                    assert(i_result is None); // contradicts branch
                                                }
                                                assert(prior is Some);
                                                assert(i_result == Some(prior.unwrap()@));
                                                assert(iaddr_view(prior) == i_result);
                                            }
                                            assert(iaddr_view(prior) == i_result);
                                            assert(iaddr_view(prior) == to_journal_reads(reads)[addr@].cropped_prior(bdy as nat));
                                            // Re-establish next_ptr invariant after inserting the new read.
                                            build_lsn_addr_index_from_reads_next_ptr_after_insert(
                                                to_journal_reads(reads_pre),
                                                bdy as nat,
                                                self@.snapshot.freshest_rec,
                                                prev,
                                                to_journal_reads(reads)[addr@],
                                            );
                                            let ghost reads_post =
                                                to_journal_reads(reads_pre).insert(addr@, to_journal_reads(reads)[addr@]);
                                            assert(to_journal_reads(reads) == reads_post) by {
                                                assert forall |k| #[trigger] to_journal_reads(reads).contains_key(k)
                                                implies reads_post.contains_key(k)
                                                    && to_journal_reads(reads)[k] == reads_post[k] by {
                                                    if k == addr@ {
                                                        assert(reads_post.contains_key(k));
                                                        assert(reads_post[k] == to_journal_reads(reads)[addr@]);
                                                    } else {
                                                        assert(reads_pre.contains_key(k));
                                                        assert(to_journal_reads(reads_pre).contains_key(k));
                                                        assert(reads_post.contains_key(k));
                                                        assert(reads_post[k] == to_journal_reads(reads_pre)[k]);
                                                        assert(to_journal_reads(reads)[k] == to_journal_reads(reads_pre)[k]);
                                                    }
                                                };
                                                assert forall |k| #[trigger] reads_post.contains_key(k)
                                                implies to_journal_reads(reads).contains_key(k)
                                                    && reads_post[k] == to_journal_reads(reads)[k] by {
                                                    if k == addr@ {
                                                        assert(to_journal_reads(reads).contains_key(k));
                                                        assert(reads_post[k] == to_journal_reads(reads)[addr@]);
                                                    } else {
                                                        assert(reads_pre.contains_key(k));
                                                        assert(to_journal_reads(reads_pre).contains_key(k));
                                                        assert(to_journal_reads(reads).contains_key(k));
                                                        assert(reads_post[k] == to_journal_reads(reads_pre)[k]);
                                                        assert(to_journal_reads(reads)[k] == to_journal_reads(reads_pre)[k]);
                                                    }
                                                };
                                            };
                                            assert(
                                                iaddr_view(prior)
                                                    == build_lsn_addr_index_from_reads_next_ptr(
                                                        reads_post,
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    )
                                            );
                                            assert(
                                                iaddr_view(prior)
                                                    == build_lsn_addr_index_from_reads_next_ptr(
                                                        to_journal_reads(reads),
                                                        bdy as nat,
                                                        self@.snapshot.freshest_rec,
                                                    )
                                            );
                                            // Maintain the "frontier" invariant for reads.
                                            assert(prev == Some(addr@));
                                            assert forall |a| #[trigger] to_journal_reads(reads).contains_key(a)
                                            implies {
                                                let next = to_journal_reads(reads)[a].cropped_prior(bdy as nat);
                                                next is None
                                                    || to_journal_reads(reads).contains_key(next.unwrap())
                                                    || next == iaddr_view(curr)
                                            } by {
                                                if a == addr@ {
                                                    assert(to_journal_reads(reads)[a]
                                                        == to_journal_reads(reads)[addr@]);
                                                    assert(iaddr_view(curr)
                                                        == to_journal_reads(reads)[addr@].cropped_prior(bdy as nat));
                                                } else {
                                                    assert(reads_pre.contains_key(a));
                                                    assert(to_journal_reads(reads_pre).contains_key(a));
                                                    // old invariant with prev as frontier
                                                    assert({
                                                        let next = to_journal_reads(reads_pre)[a].cropped_prior(bdy as nat);
                                                        next is None
                                                            || to_journal_reads(reads_pre).contains_key(next.unwrap())
                                                            || next == prev
                                                    });
                                                    // carry forward to reads
                                                    assert(to_journal_reads(reads)[a]
                                                        == to_journal_reads(reads_pre)[a]);
                                                    let next = to_journal_reads(reads_pre)[a].cropped_prior(bdy as nat);
                                                    if next is None {
                                                        // ok
                                                    } else if to_journal_reads(reads_pre).contains_key(next.unwrap()) {
                                                        assert(to_journal_reads(reads).contains_key(next.unwrap()));
                                                    } else {
                                                        // next == prev, and prev is now in reads
                                                        assert(next == prev);
                                                        assert(to_journal_reads(reads).contains_key(next.unwrap()));
                                                    }
                                                }
                                            };
                                        }

                                        assume(curr is Some);
                                        assume(journal_disk.entries.contains_key(curr.unwrap()@));
                                        if index_initialized {
                                            assert(index.seq_end() == seq_end);
                                            assert(index@ =~= build_lsn_addr_index_from_reads(
                                                to_journal_reads(reads),
                                                bdy as nat,
                                                self@.snapshot.freshest_rec,
                                            ));
                                        }
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
                            index.reverse();
                            assert(index@ =~= build_lsn_addr_index_from_reads(to_journal_reads(reads), bdy as nat, self@.snapshot.freshest_rec));
                        } else {
                            // self.status = Some(IJournalStatus{
                            //     unmarshalled_tail,
                            //     lsn_addr_index: LsnAddrIndexImpl::new(),
                            //     unmarshalled_tail_start: self.snapshot.boundary_lsn,
                            //     clean_watermark_lsn: self.snapshot.boundary_lsn,
                            // });

                            // proof {
                            //     let (_, journal_lbl) = load_index_labels(reads);
                            //     let ptr = old(self)@.snapshot.freshest_rec;
                            //     let bdy = old(self)@.snapshot.boundary_lsn;
                            //     let journal_reads = to_journal_reads(reads);
                            //     let lsn_addr_index = CachedJournal_v::build_lsn_addr_index_from_reads(journal_reads, bdy, ptr, bdy);
                            //     assert(self@.status.unwrap().lsn_addr_index == lsn_addr_index);
                            //     assert(self@.status.unwrap().unmarshalled_tail == MsgHistory::empty_history_at(bdy));
                            //     assert( CachedJournal::State::load_index(old(self)@, self@, journal_lbl));
                            //     assert( CachedJournal::State::next_by(old(self)@, self@, journal_lbl, CachedJournal::Step::load_index{}) );
                            //     assert( CachedJournal::State::next(old(self)@, self@, journal_lbl) );    
                            // }
                            index = ILsnAddrIndex::new(bdy, true);
                        }

                        let i_seq_end = index.exec_seq_end();
                        self.status = Some(IJournalStatus{
                            unmarshalled_tail: vec![],
                            lsn_addr_index: index,
                            clean_watermark_lsn: i_seq_end,
                        });

                        assert(bdy == self.snapshot.boundary_lsn);
                        assert(bdy <= index.seq_end());
                        assert(self.snapshot.boundary_lsn <= index.seq_end());
                        
                        proof {
                            let (_, journal_lbl) = load_index_labels(reads);
                            let ptr = old(self)@.snapshot.freshest_rec;
                            let bdy = old(self)@.snapshot.boundary_lsn;
                            let journal_reads = to_journal_reads(reads);

                            let lsn_addr_index = build_lsn_addr_index_from_reads(journal_reads, bdy, ptr);
 
                            index.view_domain();
                            assert( index@.dom() == Set::new(|lsn: LSN| index.seq_start() <= lsn < index.seq_end()));
                            assert( lsn_addr_index =~= index@ );
                            assert( index.seq_end() == if ptr is Some { journal_reads[ptr.unwrap()].message_seq.seq_end} else { bdy } );

                            assert(self@.snapshot == old(self)@.snapshot);
                            assert(self@.status.unwrap().unmarshalled_tail == MsgHistory::empty_history_at(index.seq_end() as nat));

                            assert( CachedJournal::State::load_index(old(self)@, self@, journal_lbl));
                            assert( CachedJournal::State::next_by(old(self)@, self@, journal_lbl, CachedJournal::Step::load_index{}) );
                            assert( CachedJournal::State::next(old(self)@, self@, journal_lbl) );    
                        }
                        proof {
                            let (cache_lbl, _) = load_index_labels(reads);
                            assert( old(cache)@ == cache@ );
                            assert( self.index_ready() );

                            let updated_entries = old(cache)@.write_updated_entries(cache_lbl->writes);
                            let updated_status_map = old(cache)@.write_updated_status(cache_lbl->writes);

                            assert(updated_entries =~= map!{});
                            assert(old(cache)@.entries.union_prefer_right(updated_entries) =~= old(cache)@.entries);
                            assert(updated_status_map =~= map!{});
                            assert(old(cache)@.status_map.union_prefer_right(updated_status_map) =~= old(cache)@.status_map);
                            assert( Cache::State::access(old(cache)@, cache@, cache_lbl));
                            assert( Cache::State::next_by(old(cache)@, cache@, cache_lbl, Cache::Step::access{}) );
                            assert( Cache::State::next(old(cache)@, cache@, cache_lbl) );               
                        }
                        out = RecoverIndexResult::IndexComplete{reads: Ghost(reads)};
                        None
                    },
                    Some(addr) => {
                        // Can we read the next page from the cache?
                        match cache.fetch(&addr) {
                            FetchErrorCode::LoadInitiate{slot_handle} => {
                                // release previous handle
                                // Cache is going to do a fetch and call us later. Bail out.
                                // Re-construct the struct
                                out = RecoverIndexResult::CacheLoad{slot_handle, addr};
                                Some(builder)
                            },
                            FetchErrorCode::Success{slot_handle} => {
                                let all_slice = Slice::all(&slot_handle.rec);
                                assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                assert( self.fmt.parsable(all_slice@.i(slot_handle.rec@)) ) by {
                                    assume( false ); // system invariant
                                }
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
        assert( self.wf() );
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

//         assert( old(self)@.seq_start() == self.snapshot.boundary_lsn );
//         assert( old(self)@.seq_end() == old(self)@.status.unwrap().unmarshalled_tail.seq_end );
//         assert( old(self)@.seq_end() == old(self).status.tail_as_history().seq_end );
// 
//         assert( old(self).snapshot.boundary_lsn <= old(self).status.unmarshalled_tail_start@ );
//         assert( old(self).status.unmarshalled_tail_start@ <= old(self).status.tail_as_history().seq_end );
// 
//         assert( old(self)@.seq_start() <= old(self)@.seq_end() );
//         assert( self@.seq_start() == old(self)@.seq_start() );
//         assert( self@.seq_end() == old(self)@.seq_end() + 1 );
//         assert( self@.seq_start() <= self@.seq_end() );
//         assert( self@.wf() );

        proof {
            let messages = MsgHistory::singleton_at(old(self).seq_end(), KeyedMessage::from_kv(key, value));
            let old_tail = old(self)@.status.unwrap().unmarshalled_tail;
            let new_tail = self@.status.unwrap().unmarshalled_tail;
            assert( old_tail.seq_end == old(self).status.unwrap().tail_as_history().seq_end );
            assert( old_tail.seq_end == old(self).seq_end() );
            assert( old_tail.can_concat(messages) );

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
                assert(out.seq_start() == out.seq_end) by {
                    // From wf: freshest_rec is None ==> clean_watermark_lsn == boundary_lsn
                };
                assert(Self::lsn_range(out.seq_start() as LSN, out.seq_end as LSN) =~= Set::empty());
                assert(self.iaddrs_for_lsns(out.seq_start() as LSN, out.seq_end as LSN) =~= Set::empty());
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

//     // TODO maybe fold this promise right into a smarter freeze_journal, and then add a method that
//     // advances the clean watermark and provides a callback to let the caller know it could maybe
//     // sync more stuff now.
//     pub exec fn check_lsns_are_clean(&self, cache: &FracCacheImpl, out: FrozenJournal) -> (clean: bool)
//     ensures clean ==> self.lsns_are_clean(cache@, out)
//     {
//         proof { assume(false); }
//         true
//     }

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
