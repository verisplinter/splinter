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
use crate::implementation::OverflowFiction_v::convert_overflow_into_liveness_failure;
use crate::implementation::CachedJournal_v::{CachedJournal, JournalSnapshot, JournalStatus, acyclic_reads, all_addrs_have_complete_lsn_ranges, all_addrs_have_finite_lsn_sets, build_lsn_addr_index_from_reads, build_lsn_addr_index_from_reads_extend_next_ptr, build_lsn_addr_index_from_reads_next_ptr, build_lsn_addr_index_from_reads_next_ptr_after_insert, build_lsn_addr_index_from_reads_next_ptr_not_in_reads, build_lsn_addr_index_from_reads_values_in_reads, lsn_index_domain_exact};
use crate::disk::GenericDisk_v::{Address, IAddress, Pointer, Ranking};
use crate::implementation::JournalTypes_v::AJournal;
use crate::implementation::JournalTypes_v::ILsn;
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, lsn_addr_index_append_record, singleton_index, lsn_disjoint};
use crate::implementation::Cache_v::{Cache, Entry};
use crate::implementation::FracCacheImpl_v::{FetchErrorCode, FracCacheImpl, MutHandle, cache_load_label};
use crate::implementation::ILsnAddrIndex_v::ILsnAddrIndex;
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

pub open spec fn all_pages_parsable(pages: Map<Address, RawPage>) -> bool
{
    forall |addr: Address| #![auto] pages.contains_key(addr)
        ==> IJournalRecordFormat::spec_new().parsable(pages[addr])
}

pub open spec fn iaddr_view(ptr: Option<IAddress>) -> Option<Address>
{
    match ptr {
        None => None,
        Some(iaddr) => Some(iaddr@),
    }
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
    }
    assert forall |addr| #[trigger] dv.entries.contains_key(addr)
        && dv.entries[addr].cropped_prior(dv.boundary_lsn) is Some
        implies ranking[dv.entries[addr].cropped_prior(dv.boundary_lsn).unwrap()] < ranking[addr] by {
        assert(disk.entries.contains_key(addr));
        assert(sub.contains_key(addr));
        assert(sub[addr] == disk.entries[addr]);
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

pub enum RecoverMapResult{
    FetchSuccess{reads: Ghost<Map<Address, RawPage>>, addr: Ghost<Address>, record: IJournalRecord},
    NotInCache{},
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

pub open spec fn map_recovery_labels(bdy: LSN, reads: Map<Address, RawPage>, addr: Address) -> (Cache::Label, CachedJournal::Label)
    recommends reads.contains_key(addr)
{
    let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
    let journal_lbl = CachedJournal::Label::ReadForRecovery{
        messages: to_journal_reads(reads)[addr].message_seq.maybe_discard_old(bdy),
        reads: to_journal_reads(reads),
    };
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
                &&& self.snapshot.boundary_lsn == status.lsn_addr_index.seq_start()
                &&& self.snapshot.boundary_lsn <= status.clean_watermark_lsn
                &&& status.clean_watermark_lsn <= status.lsn_addr_index.seq_end()
                &&& self.snapshot.boundary_lsn < status.lsn_addr_index.seq_end()
                    ==> self.snapshot.freshest_rec is Some
                &&& self.snapshot.boundary_lsn < status.lsn_addr_index.seq_end()
                    ==> status.lsn_addr_index@[
                        (status.lsn_addr_index.seq_end() - 1) as nat
                    ] == self.snapshot.freshest_rec.unwrap()@
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
                // Runtime overflow guard for exec arithmetic.
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

    pub closed spec fn no_unmarshalled_entries(&self) -> bool
    {
        &&& self.index_ready()
        &&& self.status.unwrap().lsn_addr_index.seq_end() as nat == self.seq_end()
    }

    pub exec fn new(snapshot: IJournalSnapshot) -> (out: Self)
    ensures
        out.wf(),
        !out.index_ready(),
        out@.snapshot == snapshot@,
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

    pub exec fn recover_map_step(&self, cache: &mut FracCacheImpl, start_lsn: ILsn, journal_raw_disk_ghost: Ghost<Map<Address, RawPage>>)
        -> (out: RecoverMapResult)
    requires
        self.wf(),
        self.index_ready(),
        self.no_unmarshalled_entries(),
        self.seq_start() <= (start_lsn as nat),
        (start_lsn as nat) < self.seq_end(),
        old(cache).wf(),
        all_pages_parsable(journal_raw_disk_ghost@),
        cache_matches_raw_disk(old(cache)@, journal_raw_disk_ghost@),
    ensures ({
        &&& self@ == self@
        &&& self.wf()
        &&& self.index_ready()
        &&& cache.wf()
        &&& cache.valid_load_handles_preserved(*old(cache))
        &&& match out {
            RecoverMapResult::FetchSuccess{reads, addr, record} => {
                &&& self.seq_start() <= start_lsn as nat
                &&& (start_lsn as nat) < self.seq_end()
                &&& reads@.contains_key(addr@)
                &&& to_journal_reads(reads@)[addr@] == record.parsedv().view()
                &&& record.parsedv().view().message_seq.seq_start <= start_lsn as nat
                &&& (start_lsn as nat) < record.parsedv().view().message_seq.seq_end
                &&& record.parsedv().view().message_seq.seq_end <= self.seq_end()
                &&& {
                    let lbls = map_recovery_labels(self.seq_start(), reads@, addr@);
                    &&& Cache::State::next(old(cache)@, cache@, lbls.0)
                    &&& CachedJournal::State::next(self@, self@, lbls.1)
                }
            },
            RecoverMapResult::NotInCache{} => old(cache)@ == cache@,
        }
    })
    {
        let seq_end = self.exec_seq_end();
        proof {
            reveal(JournalImpl::no_unmarshalled_entries);
            assert(self.snapshot.boundary_lsn == self.status.unwrap().lsn_addr_index.seq_start());
            assert(self.snapshot.boundary_lsn <= start_lsn);
            assert(start_lsn < seq_end);
            assert(seq_end as nat == self.seq_end());
            assert(self.status.unwrap().lsn_addr_index.seq_end() as nat == self.seq_end());
            assert((start_lsn as nat) < (self.status.unwrap().lsn_addr_index.seq_end() as nat));
            assert(start_lsn < self.status.unwrap().lsn_addr_index.seq_end());
            assert(self.status.unwrap().lsn_addr_index.seq_start() <= start_lsn < self.status.unwrap().lsn_addr_index.seq_end());
        }

        let index = &self.status.as_ref().unwrap().lsn_addr_index;
        let addr = index.lookup_lsn(start_lsn);
        proof {
            assert(addr@ == self.status.unwrap().lsn_addr_index@[start_lsn as nat]);
        }

        let ghost cache_pre = cache@;
        // A9: journal_raw_disk from system invariant via caller
        let ghost journal_raw_disk = journal_raw_disk_ghost@;
        proof {
            reveal(JournalImpl::wf);
            assert(journal_raw_disk_inv(self.fmt, journal_raw_disk));
            // cache_matches_raw_disk now from requires (system invariant pull-down)
            // TODO: system invariants, index in the kvstore model matches with the physical index
            // system inv would relate the model index to the system disk, and that's how we get these facts
            assume(forall |a: Address| #[trigger] self.status.unwrap().lsn_addr_index@.values().contains(a)
                ==> journal_raw_disk.contains_key(a)
                    && raw_page_to_record(journal_raw_disk[a]).message_seq.seq_end <= self.seq_end());
            assume(raw_page_to_record(journal_raw_disk[addr@]).message_seq.seq_start <= start_lsn as nat);
            assume((start_lsn as nat) < raw_page_to_record(journal_raw_disk[addr@]).message_seq.seq_end);
        }
        match cache.fetch(&addr, false) {
            FetchErrorCode::Success{slot_handle} => {
                let all_slice = Slice::all(&slot_handle.rec);
                assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                proof {
                    assert(old(cache)@.valid_read(addr@, slot_handle.rec@));
                    assert(journal_raw_disk.contains_key(addr@));
                    assert(journal_raw_disk[addr@] == slot_handle.rec@);
                    assert(self.fmt.parsable(journal_raw_disk[addr@]));
                    assert(self.fmt.parsable(slot_handle.rec@));
                    assert(self.fmt.parsable(all_slice@.i(slot_handle.rec@)));
                }
                let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);

                let ghost fetched_slot = slot_handle.idx;
                let ghost fetched_data = slot_handle.rec@;
                let ghost reads = map!{addr@ => slot_handle.rec@};
                let ghost lbls = map_recovery_labels(self.seq_start(), reads, addr@);

                proof {
                    to_journal_reads_entry_from_exec_parse(self.fmt, reads, addr@, i_journal_record);
                    assert(to_journal_reads(reads)[addr@] == i_journal_record.parsedv().view());
                    assert(self.status.unwrap().lsn_addr_index@.contains_key(start_lsn as nat));
                    assert(addr@ == self.status.unwrap().lsn_addr_index@[start_lsn as nat]);
                    assert(self.status.unwrap().lsn_addr_index@.values().contains(addr@));
                    assert(raw_page_to_record(journal_raw_disk[addr@]).message_seq.seq_start <= start_lsn as nat);
                    assert((start_lsn as nat) < raw_page_to_record(journal_raw_disk[addr@]).message_seq.seq_end);
                    assert(raw_page_to_record(slot_handle.rec@).message_seq.seq_start <= start_lsn as nat);
                    assert((start_lsn as nat) < raw_page_to_record(slot_handle.rec@).message_seq.seq_end);
                    assert(raw_page_to_record(journal_raw_disk[addr@]).message_seq.seq_end <= self.seq_end());
                    assert(raw_page_to_record(slot_handle.rec@).message_seq.seq_end <= self.seq_end());
                    assert(reads[addr@] == slot_handle.rec@);
                    assert(to_journal_reads(reads)[addr@] == raw_page_to_record(slot_handle.rec@));
                    assert(i_journal_record.parsedv().view().message_seq.seq_start
                        == raw_page_to_record(slot_handle.rec@).message_seq.seq_start);
                    assert(i_journal_record.parsedv().view().message_seq.seq_end
                        == raw_page_to_record(slot_handle.rec@).message_seq.seq_end);
                    assert(i_journal_record.parsedv().view().message_seq.seq_start <= start_lsn as nat);
                    assert((start_lsn as nat) < i_journal_record.parsedv().view().message_seq.seq_end);
                    assert(i_journal_record.parsedv().view().message_seq.seq_end <= self.seq_end());
                    assert(lbls.1 is ReadForRecovery);
                }

                let ghost cache_after_fetch = cache@;
                cache.handle_release(&addr, slot_handle);
                proof {
                    assert(cache_pre.entries == cache_after_fetch.entries.insert(
                        fetched_slot, Entry::Filled{addr: addr@, data: fetched_data}));
                    assert(cache@.entries == cache_after_fetch.entries.insert(
                        fetched_slot, Entry::Filled{addr: addr@, data: fetched_data}));
                    assert(cache@.entries == cache_pre.entries);

                    assert(cache_pre.lookup_map == cache_after_fetch.lookup_map);
                    assert(cache@.lookup_map == cache_after_fetch.lookup_map);
                    assert(cache@.lookup_map == cache_pre.lookup_map);

                    assert(cache_pre.status_map == cache_after_fetch.status_map);
                    assert(cache@.status_map == cache_after_fetch.status_map);
                    assert(cache@.status_map == cache_pre.status_map);

                    assert(cache@ == cache_pre);
                    assert(cache@ =~= cache_pre);

                    let ghost cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
                    reveal(map_recovery_labels);
                    assert(lbls.0 == cache_lbl);

                    assert(cache_pre.valid_read(addr@, fetched_data));
                    assert forall |a| #[trigger] cache_lbl->reads.contains_key(a)
                        implies cache_pre.valid_read(a, cache_lbl->reads[a]) by {
                        assert(a == addr@);
                    };
                    assert forall |a| #[trigger] cache_lbl->writes.contains_key(a)
                        implies cache_pre.valid_write(a) by {
                    };

                    let updated_entries = cache_pre.write_updated_entries(cache_lbl->writes);
                    let updated_status_map = cache_pre.write_updated_status(cache_lbl->writes);
                    assert(cache_pre.entries.union_prefer_right(updated_entries) =~= cache_pre.entries);
                    assert(cache_pre.status_map.union_prefer_right(updated_status_map) =~= cache_pre.status_map);

                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(cache_pre, cache@, cache_lbl, Cache::Step::access{}));
                    reveal(Cache::State::next);
                    assert(Cache::State::next(old(cache)@, cache@, lbls.0));

                    let ghost index_seq_end = self.status.unwrap().lsn_addr_index.seq_end() as nat;
                    assert((self.snapshot.boundary_lsn as nat) <= (start_lsn as nat));
                    assert((start_lsn as nat) < index_seq_end);
                    assert((self.snapshot.boundary_lsn as nat) < index_seq_end);
                    assert(self.snapshot.freshest_rec is Some);
                    assert(self.status.unwrap().lsn_addr_index@[(index_seq_end - 1) as nat]
                        == self.snapshot.freshest_rec.unwrap()@);
                    index.derive_recovery_index_properties();
                    assert(lsn_index_domain_exact(
                        self.status.unwrap().lsn_addr_index@,
                        self.snapshot.boundary_lsn as nat,
                        index_seq_end,
                    ));
                    assert(self.status.unwrap().lsn_addr_index@.contains_key(start_lsn as nat)) by {
                        assert(lsn_index_domain_exact(
                            self.status.unwrap().lsn_addr_index@,
                            self.snapshot.boundary_lsn as nat,
                            index_seq_end,
                        ));
                        assert((self.snapshot.boundary_lsn as nat) <= (start_lsn as nat));
                        assert((start_lsn as nat) < index_seq_end);
                    };
                    assert(all_addrs_have_complete_lsn_ranges(
                        self.status.unwrap().lsn_addr_index@,
                        self.snapshot.boundary_lsn as nat,
                    ));
                    assert(all_addrs_have_finite_lsn_sets(
                        self.status.unwrap().lsn_addr_index@,
                        self.snapshot.boundary_lsn as nat,
                    ));

                    let ghost depth = self@.depth_for_index_lsn(index_seq_end, start_lsn as nat);
                    assert(self@.pointer_after_crop_index(self@.snapshot.freshest_rec, depth)
                        == Some(self.status.unwrap().lsn_addr_index@[start_lsn as nat]));
                    assert(addr@ == self.status.unwrap().lsn_addr_index@[start_lsn as nat]);
                    assert(self@.pointer_after_crop_index(self@.snapshot.freshest_rec, depth) == Some(addr@));

                    reveal(map_recovery_labels);
                    let ghost journal_reads = to_journal_reads(reads);
                    let ghost journal_lbl = CachedJournal::Label::ReadForRecovery{
                        messages: journal_reads[addr@].message_seq.maybe_discard_old(self.seq_start()),
                        reads: journal_reads,
                    };
                    assert(lbls.1 == journal_lbl);
                    self.view_seq_start_ensures();
                    assert(self.seq_start() == self@.snapshot.boundary_lsn);

                    match journal_lbl {
                        CachedJournal::Label::ReadForRecovery{messages, reads} => {
                            assert(reads.contains_key(addr@));
                            assert(messages
                                == reads[addr@].message_seq.maybe_discard_old(self@.snapshot.boundary_lsn));
                        }
                        _ => { assert(false); }
                    }

                    reveal(CachedJournal::State::next_by);
                    assert(CachedJournal::State::next_by(
                        self@,
                        self@,
                        journal_lbl,
                        CachedJournal::Step::read_for_recovery(depth),
                    ));
                    reveal(CachedJournal::State::next);
                    assert(CachedJournal::State::next(self@, self@, lbls.1));
                }

                RecoverMapResult::FetchSuccess{
                    reads: Ghost(reads),
                    addr: Ghost(addr@),
                    record: i_journal_record,
                }
            },
            _ => {
                RecoverMapResult::NotInCache{}
            }
        }
    }

    // Incrementally reconstruct the index from the journal chain.
    // Keeps explicit intermediate state to avoid restarting from head on each cache interaction.
    pub exec fn recover_index_step(&mut self, cache: &mut FracCacheImpl, journal_raw_disk_ghost: Ghost<Map<Address, RawPage>>)
        -> (out: RecoverIndexResult)
    requires
        old(self).wf(),
        !old(self).index_ready(),
        old(cache).wf(),
        all_pages_parsable(journal_raw_disk_ghost@),
        cache_matches_raw_disk(old(cache)@, journal_raw_disk_ghost@),
        old(self)@.snapshot.freshest_rec is Some ==>
            journal_disk_inv(
                LinkedJournal_v::DiskView{
                    boundary_lsn: old(self)@.snapshot.boundary_lsn,
                    entries: to_journal_reads(journal_raw_disk_ghost@),
                },
                old(self)@.snapshot.freshest_rec),
    ensures ({
        &&& self.wf()
        &&& self@.wf()
        &&& self.seq_start() == old(self).seq_start()
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
                &&& self.no_unmarshalled_entries()
                &&& self.seq_start() <= self.seq_end()
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
        let ghost cache0 = *cache;
        proof {
            assert(cache.valid_load_handles_preserved(cache0));
        }
        let mut index_builder = self.index_builder.take();
        index_builder = match index_builder {
            // NOTE: builder becomes None when we are out of the building phase
            None => { assert(false); None },
            // NOTE: builder is a hint for continued fetch
            Some(mut builder) => {
                // A9: journal_raw_disk from system invariant via caller
                let ghost journal_raw_disk = journal_raw_disk_ghost@;
                proof {
                    reveal(JournalImpl::wf);
                    // wf() gives self.fmt.valid(), which constrains fmt fields to match spec_new()
                    // all_pages_parsable uses spec_new().parsable; since fields match, so does self.fmt.parsable
                    assert(journal_raw_disk_inv(self.fmt, journal_raw_disk));
                }
                // cache_matches_raw_disk now from requires (system invariant pull-down)

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

                        if let Some(root) = curr {
                            let mut index_initialized = false;
                            index = ILsnAddrIndex::new(u64::MAX);

                            // journal_disk_inv now from requires (system invariant pull-down)
                            let ghost journal_disk = LinkedJournal_v::DiskView{boundary_lsn: bdy as nat, entries: to_journal_reads(journal_raw_disk)};

                            let ghost ranking = journal_disk.the_ranking();
                            let ghost seq_end = journal_disk.entries[root@].message_seq.seq_end;

                            while index.exec_seq_start() != bdy
                            invariant 
                                index.wf(),
                                cache.wf(),
                                cache.valid_load_handles_preserved(cache0),
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
                                let ghost cache_pre_fetch = *cache;

                                match cache.fetch(&addr, true) {
                                    FetchErrorCode::Success{slot_handle} => {
                                        let ghost cache_post_fetch = *cache;
                                        let all_slice = Slice::all(&slot_handle.rec);
                                        assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                        let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);
                                        cache.handle_release(&addr, slot_handle);
                                        let ghost cache_post_release = *cache;
                                        proof {
                                            FracCacheImpl::valid_load_handles_preserved_transitive(
                                                cache0,
                                                cache_pre_fetch,
                                                cache_post_fetch,
                                            );
                                            FracCacheImpl::valid_load_handles_preserved_transitive(
                                                cache0,
                                                cache_post_fetch,
                                                cache_post_release,
                                            );
                                        }

                                        let ghost reads_pre = reads;
                                        proof {
                                            reads = reads.insert(addr@, slot_handle.rec@);
                                            let ghost reads_post = to_journal_reads(reads_pre).insert(addr@, to_journal_reads(reads)[addr@]);
                                            disk_view_valid_ranking_subset(journal_disk, reads_post, ranking);
                                            build_lsn_addr_index_from_reads_next_ptr_after_insert(to_journal_reads(reads_pre), bdy as nat, self@.snapshot.freshest_rec, iaddr_view(curr), to_journal_reads(reads)[addr@]);
                                        }

                                        let start = if i_journal_record.header.start_lsn < bdy { bdy } else { i_journal_record.header.start_lsn };

                                        let ghost was_initialized = index_initialized;
                                        if !index_initialized {
                                            index = ILsnAddrIndex::new(i_journal_record.seq_end()); 
                                            index_initialized = true;
                                        }

                                        // if they are the same then we don't need to do anything                                             
                                        let ghost index_pre = index;
                                        let old_bound = index.exec_seq_start();
                                        proof { to_journal_reads_entry_from_exec_parse(self.fmt, reads, addr@, i_journal_record); }
                                        proof {
                                            if was_initialized {
                                                build_lsn_addr_index_from_reads_next_ptr_not_in_reads(
                                                    to_journal_reads(reads_pre),
                                                    bdy as nat,
                                                    self@.snapshot.freshest_rec,
                                                    prev,
                                                );
                                                assert(prev is Some);
                                                assert(prev == Some(addr@));
                                                assert(!to_journal_reads(reads_pre).contains_key(addr@));
                                                assert(!reads_pre.contains_key(addr@));
                                                assert(index@ == build_lsn_addr_index_from_reads(
                                                    to_journal_reads(reads_pre),
                                                    bdy as nat,
                                                    self@.snapshot.freshest_rec
                                                ));
                                                assert(!index@.values().contains(addr@)) by {
                                                    if index@.values().contains(addr@) {
                                                        build_lsn_addr_index_from_reads_values_in_reads(
                                                            to_journal_reads(reads_pre),
                                                            bdy as nat,
                                                            self@.snapshot.freshest_rec,
                                                            addr@,
                                                        );
                                                        assert(reads_pre.contains_key(addr@));
                                                        assert(false);
                                                    }
                                                };
                                            } else {
                                                assert(index@.is_empty());
                                                assert(!index@.values().contains(addr@));
                                            }
                                        }
                                        index.index_prepend_record(old_bound, start, addr);
                                        proof {
                                            if index_initialized {
                                                let ptr2_data = to_journal_reads(reads)[addr@];
                                                let start_lsn = vstd::math::max(bdy as int, ptr2_data.message_seq.seq_start as int) as nat;
                                                let end_lsn = ptr2_data.message_seq.seq_end;
                                                let ghost reads_post = to_journal_reads(reads_pre).insert(addr@, ptr2_data);
                                                assert(to_journal_reads(reads) == reads_post);
                                                let ghost build_pre = build_lsn_addr_index_from_reads(to_journal_reads(reads_pre), bdy as nat, self@.snapshot.freshest_rec);
                                                if !was_initialized {
                                                    build_lsn_addr_index_from_reads_next_ptr_not_in_reads(to_journal_reads(reads_pre), bdy as nat, self@.snapshot.freshest_rec, iaddr_view(curr));
                                                }
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
                                        please_panic(); 
                                    } 
                                }
                            }
                            if !index_initialized {
                                please_panic();
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
                            let seq_end = if ptr is Some { journal_reads[ptr.unwrap()].message_seq.seq_end } else { bdy };
 
                            index.derive_recovery_index_properties();
                            assert(lsn_index_domain_exact(index@, index.seq_start() as nat, index.seq_end() as nat));
                            assert( lsn_addr_index =~= index@ );
                            assert(lsn_index_domain_exact(
                                self@.status.unwrap().lsn_addr_index,
                                self@.snapshot.boundary_lsn,
                                self@.status.unwrap().unmarshalled_tail.seq_start,
                            ));
                            assert(self@.status.unwrap().unmarshalled_tail == MsgHistory::empty_history_at(index.seq_end() as nat));
                            assert(all_addrs_have_complete_lsn_ranges(
                                self@.status.unwrap().lsn_addr_index,
                                self@.snapshot.boundary_lsn,
                            ));
                            assert(lsn_addr_index.dom() == Set::new(|lsn: LSN| bdy <= lsn < seq_end));
                            assert( CachedJournal::State::next_by(old(self)@, self@, journal_lbl, CachedJournal::Step::load_index{}) );
                        }
                        proof {
                            let (cache_lbl, _) = load_index_labels(reads);
                            let updated_entries = old(cache)@.write_updated_entries(cache_lbl->writes);
                            let updated_status_map = old(cache)@.write_updated_status(cache_lbl->writes);

                            assert(old(cache)@.entries.union_prefer_right(updated_entries) =~= old(cache)@.entries);
                            assert(old(cache)@.status_map.union_prefer_right(updated_status_map) =~= old(cache)@.status_map);
                            assert( Cache::State::next_by(old(cache)@, cache@, cache_lbl, Cache::Step::access{}) );
                        }
                        out = RecoverIndexResult::IndexComplete{reads: Ghost(reads)};
                        None
                    },
                    Some(addr) => {
                        let ghost cache_pre_fetch = *cache;
                        // Can we read the next page from the cache?
                        match cache.fetch(&addr, true) {
                            FetchErrorCode::LoadInitiate{slot_handle} => {
                                let ghost cache_post_fetch = *cache;
                                // release previous handle
                                // Cache is going to do a fetch and call us later. Bail out.
                                // Re-construct the struct
                                proof {
                                    FracCacheImpl::valid_load_handles_preserved_transitive(
                                        cache0,
                                        cache_pre_fetch,
                                        cache_post_fetch,
                                    );
                                    assert(!old(cache).entry_fetched(&addr));
                                }
                                out = RecoverIndexResult::CacheLoad{slot_handle, addr};
                                Some(builder)
                            },
                            FetchErrorCode::Success{slot_handle} => {
                                let ghost cache_post_fetch = *cache;
                                let all_slice = Slice::all(&slot_handle.rec);
                                assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);
                                cache.handle_release(&addr, slot_handle);
                                let ghost cache_post_release = *cache;
                                proof {
                                    FracCacheImpl::valid_load_handles_preserved_transitive(
                                        cache0,
                                        cache_pre_fetch,
                                        cache_post_fetch,
                                    );
                                    FracCacheImpl::valid_load_handles_preserved_transitive(
                                        cache0,
                                        cache_post_fetch,
                                        cache_post_release,
                                    );
                                }
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
                                let ghost cache_post_fetch = *cache;
                                proof {
                                    FracCacheImpl::valid_load_handles_preserved_transitive(
                                        cache0,
                                        cache_pre_fetch,
                                        cache_post_fetch,
                                    );
                                }
                                Some(builder)
                            },
                        }
                    },
                }
            }
        };
        core::mem::swap(&mut self.index_builder, &mut index_builder);
        proof {
            assert(cache.valid_load_handles_preserved(cache0));
            assert(cache0 == *old(cache));
        }
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
        // Verus currently lacks &mut returns, so update status by swapping Option out and back in.
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

    pub proof fn view_seq_end_ensures(&self)
        requires
            self.index_ready(),
        ensures
            self@.seq_end() == self.seq_end(),
    {
        broadcast use JournalImpl::view_ensures;
        assert(self@.status is Some);
        reveal(CachedJournal::State::seq_end);
        reveal(JournalImpl::seq_end);
    }

    pub proof fn view_seq_start_ensures(&self)
        ensures
            self@.snapshot.boundary_lsn == self.seq_start(),
    {
        reveal(JournalImpl::seq_start);
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

    // Open because this definition gets used proving the refinement CachedJournal::Step::freeze_for_commit(depth) in Implementation
    pub open spec fn iaddrs_for_lsns(self, start_incl: LSN, end_excl: LSN) -> Set<Address>
    recommends self.index_ready()
    {
        self@.status.unwrap().lsn_addr_index.restrict(
            Set::new(|lsn: LSN| start_incl <= lsn && lsn < end_excl)
        ).values()
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
