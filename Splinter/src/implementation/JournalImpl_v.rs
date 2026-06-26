// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::LSN;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::spec::AsyncDisk_t::{DiskRequest, RawPage};
use crate::implementation::OverflowFiction_v::convert_overflow_into_liveness_failure;
use crate::implementation::CachedJournal_v::{CachedJournal, JournalRoot, JournalSnapshot, JournalStatus, acyclic_reads, all_addrs_have_complete_lsn_ranges, all_addrs_have_finite_lsn_sets, build_lsn_addr_index_from_reads, build_lsn_addr_index_from_reads_extend_next_ptr, build_lsn_addr_index_from_reads_next_ptr, build_lsn_addr_index_from_reads_next_ptr_after_insert, build_lsn_addr_index_from_reads_next_ptr_not_in_reads, build_lsn_addr_index_from_reads_values_in_reads, freeze_reads_for_seq_end, lsn_addr_index_to_au_index, lsn_index_domain_exact};
use crate::disk::GenericDisk_v::{Address, IAddress, Pointer, Ranking, to_aus};
use crate::implementation::JournalTypes_v::AJournal;
use crate::implementation::JournalTypes_v::ILsn;
use crate::implementation::JournalTypes_v::{journal_marshall_labels, raw_page_to_record, to_journal_records};
use crate::allocation_layer::AllocationJournal_v::{AUPageBounds, lsn_au_index_discard_up_to};
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, discard_old_ptr_by_index, largest_lsn_plus_one, lsn_addr_index_append_record, singleton_index, lsn_disjoint};
use crate::implementation::Cache_v::{Cache, Entry};
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle, ReserveWriteResult, WriteAcquireResult, WritebackHandle,
    WritebackAcquireResult, cache_load_label, cache_write_label, PAGE_SIZE_BYTES
};
use crate::implementation::ILsnAddrIndex_v::ILsnAddrIndex;
use crate::implementation::PageAllocator_v::PageAllocator;
use crate::marshalling::Slice_v::Slice;
use crate::spec::ImplDisk_t::IAU;
use crate::marshalling::IJournalRecordFormat_v::{IJournalHeader, IJournalRecord, IJournalRecordFormat};
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::JournalRecord;

verus!{

#[derive(Debug, Copy, Clone)]
pub struct IJournalSnapshot {
    pub boundary_lsn: u64,
    pub freshest_rec: Option<IAddress>,
    pub first: IAU,
}

impl IJournalSnapshot {
    pub open spec fn spec_new_empty(at_lsn: u64) -> Self {
        IJournalSnapshot{ boundary_lsn: at_lsn, freshest_rec: None, first: 0 }
    }

    pub exec fn new_empty(at_lsn: u64) -> (out: Self)
        ensures out == Self::spec_new_empty(at_lsn)
    {
        IJournalSnapshot{ boundary_lsn: at_lsn, freshest_rec: None, first: 0 }
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
    assert(dv.entries.dom().subset_of(ranking.dom()));
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

pub proof fn to_journal_records_entry_from_exec_parse(
    fmt: IJournalRecordFormat,
    reads: Map<Address, RawPage>,
    addr: Address,
    value: IJournalRecord,
)
requires
    fmt == IJournalRecordFormat::spec_new(),
    fmt.valid(),
    reads.contains_key(addr),
    fmt.parsable(reads[addr]),
    value.parsedv() == fmt.parse(reads[addr]),
ensures
    to_journal_records(reads)[addr] == value.parsedv().view(),
{
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
            root: if iaddr_view(self.freshest_rec) is Some {
                Some(JournalRoot{
                    freshest_rec: iaddr_view(self.freshest_rec).unwrap(),
                    first: self.first as nat,
                })
            } else {
                None
            },
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
}

pub struct IJournalStatus {
    pub lsn_addr_index: ILsnAddrIndex,
    pub unmarshalled_tail: Vec<KeyedMessage>,
    pub au_page_bounds: Ghost<AUPageBounds>,
    pub clean_watermark_lsn: ILsn,
}

impl IJournalStatus {
    spec fn wf(&self) -> bool
    {
        &&& self.lsn_addr_index.wf()
        &&& forall |i: int| 0 <= i < self.unmarshalled_tail.len()
            ==> #[trigger] self.unmarshalled_tail[i].message is Define
    }

    closed spec fn tail_as_history(&self) -> MsgHistory
    {
        AJournal {
            msg_history: self.unmarshalled_tail@,
            seq_start: self.lsn_addr_index.seq_end(),
        }@
    }
}

impl View for IJournalStatus {
    type V = JournalStatus;
    closed spec fn view(&self) -> Self::V {
        Self::V {
            unmarshalled_tail: self.tail_as_history(),
            lsn_au_index: lsn_addr_index_to_au_index(self.lsn_addr_index@),
            au_page_bounds: self.au_page_bounds@,
            clean_watermark_au_page_bounds: self.au_page_bounds@,
            clean_watermark_lsn: self.clean_watermark_lsn as nat,
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

pub struct JournalWritebackRequest {
    pub handle: WritebackHandle,
    pub addr: IAddress,
}

pub enum BeginWritebackForTargetResult {
    Acquired{request: JournalWritebackRequest, flushed_domain: Ghost<Set<Address>>},
    Complete{flushed_domain: Ghost<Set<Address>>},
}

impl BeginWritebackForTargetResult {
    pub open spec fn flushed_domain(&self) -> Set<Address>
    {
        match self {
            BeginWritebackForTargetResult::Acquired{flushed_domain, ..} => flushed_domain@,
            BeginWritebackForTargetResult::Complete{flushed_domain} => flushed_domain@,
        }
    }
}

pub enum CleanForCommitResult {
    Frozen{frozen_journal: FrozenJournal},
    NeedsFlush{},
}

pub enum MarshalReserveResult {
    Reserved{addr: IAddress, slot_handle: MutHandle},
    CacheFull{},
}

pub struct JournalImpl {
    pub snapshot: IJournalSnapshot,
    pub index_builder: Option<IndexBuilder>,
    pub status: Option<IJournalStatus>,
    pub fmt: IJournalRecordFormat,
    pub journal_alloc: PageAllocator,
}

closed spec fn flush_domain_from_index_range(
    index: LsnAddrIndex,
    start_incl: LSN,
    end_excl: LSN,
) -> Set<Address>
{
    index.restrict(Set::new(|lsn: LSN| start_incl <= lsn < end_excl)).values()
}

pub open spec fn cache_evictable_prop(cache: Cache::State, addrs: Set<Address>) -> bool
{
    forall |addr: Address|
        to_aus(addrs).contains(addr.au) && #[trigger] cache.lookup_map.contains_key(addr)
            ==> {
                &&& cache.entries[cache.lookup_map[addr]] is Filled
                &&& cache.status_map[cache.lookup_map[addr]] is Clean
            }
}

pub proof fn cache_evictable_prop_implies_next(cache: Cache::State, addrs: Set<Address>)
    requires
        cache_evictable_prop(cache, addrs),
    ensures
        Cache::State::next(cache, cache, Cache::Label::EvictableCheck{aus: to_aus(addrs)}),
{
    reveal(Cache::State::next_by);
    reveal(Cache::State::next);
    let lbl = Cache::Label::EvictableCheck{aus: to_aus(addrs)};
    assert(Cache::State::next_by(cache, cache, lbl, Cache::Step::evictable()));
}

pub proof fn cache_next_evictable_implies_prop(cache: Cache::State, addrs: Set<Address>)
    requires
        Cache::State::next(cache, cache, Cache::Label::EvictableCheck{aus: to_aus(addrs)}),
    ensures
        cache_evictable_prop(cache, addrs),
{
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
}

pub open spec fn load_index_labels(reads: Map<Address, RawPage>) -> (Cache::Label, CachedJournal::Label)
{
    let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
    let journal_lbl = CachedJournal::Label::LoadIndex{
        reads: to_journal_records(reads),
        discovered_aus: to_aus(reads.dom()),
    };
    (cache_lbl, journal_lbl)
}

pub open spec fn map_recovery_labels(bdy: LSN, reads: Map<Address, RawPage>, addr: Address) -> (Cache::Label, CachedJournal::Label)
    recommends reads.contains_key(addr)
{
    let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
    let journal_lbl = CachedJournal::Label::ReadForRecovery{
        messages: to_journal_records(reads)[addr].message_seq.maybe_discard_old(bdy),
        reads: to_journal_records(reads),
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
    pub closed spec fn format_ok(&self) -> bool {
        &&& self.fmt == IJournalRecordFormat::spec_new()
        &&& self.fmt.valid()
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.format_ok()
        &&& match self.status {
            None => { self.index_builder is Some },
            Some(status) => {
                &&& status.wf()
                &&& self.snapshot.boundary_lsn == status.lsn_addr_index.seq_start()
                &&& self.snapshot.boundary_lsn <= status.clean_watermark_lsn <= status.lsn_addr_index.seq_end()
                &&& (status.clean_watermark_lsn > self.snapshot.boundary_lsn
                    && status.clean_watermark_lsn < status.lsn_addr_index.seq_end()) ==> {
                    &&& status.lsn_addr_index@.contains_key((status.clean_watermark_lsn - 1) as nat)
                    &&& status.lsn_addr_index@.contains_key(status.clean_watermark_lsn as nat)
                    &&& status.lsn_addr_index@[(status.clean_watermark_lsn - 1) as nat]
                        != status.lsn_addr_index@[status.clean_watermark_lsn as nat]
                }
                &&& self.snapshot.freshest_rec is Some <==> self.snapshot.boundary_lsn < status.lsn_addr_index.seq_end()
                &&& self.snapshot.freshest_rec is Some  ==> {
                        let last_lsn = (status.lsn_addr_index.seq_end() - 1) as nat;
                        &&& status.lsn_addr_index@[last_lsn] == self.snapshot.freshest_rec.unwrap()@
                    }
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
        self.snapshot@.freshest_rec()
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

    pub closed spec fn marshalled_seq_end(&self) -> LSN {
        self.status.unwrap().lsn_addr_index.seq_end() as nat
    }

    pub closed spec fn lsn_addr_index_i(&self) -> LsnAddrIndex
        recommends self.status is Some
    {
        self.status.unwrap().lsn_addr_index@
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

    pub exec fn exec_index_ready(&self) -> (out: bool)
        ensures out == self.index_ready()
    {
        self.status.is_some()
    }

    pub closed spec fn no_unmarshalled_entries(&self) -> bool
    {
        &&& self.index_ready()
        &&& self.status.unwrap().lsn_addr_index.seq_end() as nat == self.seq_end()
    }

    pub exec fn new(snapshot: IJournalSnapshot, alloc_au: u32) -> (out: Self)
    ensures
        out.wf(),
        !out.index_ready(),
        out@.snapshot == snapshot@,
        out.alloc_au() == alloc_au as nat,
    {
        let start_page = match snapshot.freshest_rec {
            Some(ptr) => {
                if ptr.page == u32::MAX {
                    convert_overflow_into_liveness_failure();
                }
                ptr.page + 1
            }
            None => 0,
        };
        Self{
            snapshot,
            index_builder: Some(IndexBuilder{
                next_head: snapshot,
            }),
            status: None,
            fmt: IJournalRecordFormat::new(),
            journal_alloc: PageAllocator::new(alloc_au, start_page),
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
        // B15: when freshest_rec is Some, the journal on disk is structurally valid
        // and the model index matches the DiskView index
        self@.snapshot.freshest_rec() is Some ==> {
            let journal_dv = LinkedJournal_v::DiskView{
                boundary_lsn: self@.snapshot.boundary_lsn,
                entries: to_journal_records(journal_raw_disk_ghost@),
            };
            let tj = LinkedJournal_v::TruncatedJournal{
                freshest_rec: self@.snapshot.freshest_rec(),
                disk_view: journal_dv,
            };
            &&& journal_disk_inv(journal_dv, self@.snapshot.freshest_rec())
            &&& tj.build_lsn_addr_index() == self.status.unwrap().lsn_addr_index@
        },
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
                &&& to_journal_records(reads@)[addr@] == record.parsedv().view()
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
            // trigger
            assert(self.status.unwrap().lsn_addr_index.seq_start() <= start_lsn < self.status.unwrap().lsn_addr_index.seq_end());
        }

        let index = &self.status.as_ref().unwrap().lsn_addr_index;
        let (addr, _) = index.lookup_lsn_with_segment_end(start_lsn);

        let ghost cache_pre = cache@;
        let ghost journal_raw_disk = journal_raw_disk_ghost@;
        proof {

            // Construct DiskView and TruncatedJournal matching the requires
            let journal_dv = LinkedJournal_v::DiskView{
                boundary_lsn: self@.snapshot.boundary_lsn,
                entries: to_journal_records(journal_raw_disk),
            };
            let tj = LinkedJournal_v::TruncatedJournal{
                freshest_rec: self@.snapshot.freshest_rec(),
                disk_view: journal_dv,
            };
            let model_index = self.status.unwrap().lsn_addr_index@;

            // Explicitly call the broadcast proof to get index properties
            tj.build_lsn_addr_index_ensures();

            // Establish tj.seq_end() == self.seq_end() via domain equality
            reveal(LinkedJournal_v::TruncatedJournal::index_domain_valid);
            // index_domain_valid: model_index.contains_key(lsn) <==> tj.seq_start() <= lsn < tj.seq_end()
            self.status.unwrap().lsn_addr_index.view_domain();
            self.status.unwrap().lsn_addr_index.seq_start_le_seq_end();
            self.seq_start_le_seq_end();
            // view_domain: model_index.dom() =~= Set::new(|lsn| lai.seq_start() <= lsn < lai.seq_end())
            // wf: boundary_lsn == lai.seq_start(), so tj.seq_start() == lai.seq_start()
            // no_unmarshalled_entries: lai.seq_end() as nat == self.seq_end()
            let ghost lai_seq_end = self.status.unwrap().lsn_addr_index.seq_end() as nat;
            assert(tj.seq_start() == self.seq_start());
            assert(tj.seq_end() == lai_seq_end) by {
                if tj.seq_end() < lai_seq_end {
                    let lsn = tj.seq_end();
                    assert(self.seq_start() <= lsn) by {
                        assert(tj.seq_start() <= tj.seq_end());
                    }
                    assert(model_index.contains_key(lsn)) by {
                        assert(self.status.unwrap().lsn_addr_index@.dom() =~= Set::new(|lsn: LSN| self.seq_start() <= lsn < lai_seq_end));
                    }
                    assert(!model_index.contains_key(lsn));
                    assert(false);
                }
                if lai_seq_end < tj.seq_end() {
                    let lsn = lai_seq_end;
                    assert(self.seq_start() <= lsn) by {
                        assert(self.seq_start() <= self.seq_end());
                        assert(self.seq_end() == lai_seq_end);
                    }
                    assert(model_index.contains_key(lsn)) by {
                        assert(tj.seq_start() <= lsn < tj.seq_end());
                    }
                    assert(!model_index.contains_key(lsn)) by {
                        assert(self.status.unwrap().lsn_addr_index@.dom() =~= Set::new(|lsn: LSN| self.seq_start() <= lsn < lai_seq_end));
                    }
                    assert(false);
                }
            };
            assert(tj.seq_end() == self.seq_end()) by {
            };

            journal_dv.instantiate_index_keys_map_to_valid_entries(model_index, start_lsn as nat);

            assert forall |a: Address|
                #[trigger] model_index.values().contains(a)
            implies
                journal_raw_disk.contains_key(a)
                && raw_page_to_record(journal_raw_disk[a]).message_seq.seq_end <= self.seq_end()
            by {
                // Witness: some lsn maps to this address
                let lsn = choose |lsn: LSN| #![auto] model_index.contains_key(lsn) && model_index[lsn] == a;
                journal_dv.instantiate_index_keys_map_to_valid_entries(model_index, lsn);
                // → journal_dv.entries.contains_key(a) → journal_raw_disk.contains_key(a)

                // seq_end bound: contradiction if record.seq_end > tj.seq_end()
                let record = journal_dv.entries[a];
                if record.message_seq.seq_end > tj.seq_end() {
                    // From instantiate: entries[a].contains_lsn(bdy, lsn)
                    // = max(bdy, seq_start) <= lsn < record.seq_end
                    // From index_domain_valid: lsn < tj.seq_end()
                    // So max(bdy, seq_start) <= lsn < tj.seq_end() < record.seq_end
                    assert(lsn < tj.seq_end());
                    // Therefore cropped_msg_seq_contains_lsn(bdy, record.message_seq, tj.seq_end())
                    assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(
                        journal_dv.boundary_lsn,
                        record.message_seq,
                        tj.seq_end()));
                    // From index_range_valid: every_lsn_at_addr_indexed_to_addr(model_index, a)
                    // Trigger fires on cropped_msg_seq_contains_lsn → model_index.contains_key(tj.seq_end())
                    // But index_domain_valid: contains_key(tj.seq_end()) ==> tj.seq_end() < tj.seq_end()
                    assert(false);
                }
                // Now record.seq_end <= tj.seq_end() == self.seq_end()
                assert(record.message_seq.seq_end <= self.seq_end());
            };
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
                    to_journal_records_entry_from_exec_parse(self.fmt, reads, addr@, i_journal_record);
                    assert(to_journal_records(reads)[addr@] == i_journal_record.parsedv().view());
                    assert(self.status.unwrap().lsn_addr_index@.contains_key(start_lsn as nat));
                    assert(addr@ == self.status.unwrap().lsn_addr_index@[start_lsn as nat]);
                    assert(self.status.unwrap().lsn_addr_index@.values().contains(addr@));
                    assert(raw_page_to_record(slot_handle.rec@).message_seq.seq_start <= start_lsn as nat);
                    assert((start_lsn as nat) < raw_page_to_record(slot_handle.rec@).message_seq.seq_end);
                    assert(raw_page_to_record(slot_handle.rec@).message_seq.seq_end <= self.seq_end());
                    assert(to_journal_records(reads)[addr@] == raw_page_to_record(slot_handle.rec@));
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

                    assert(cache@.lookup_map == cache_pre.lookup_map);

                    assert(cache@.status_map == cache_pre.status_map);

                    assert(cache@ == cache_pre);

                    let ghost cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
                    assert(lbls.0 == cache_lbl);

                    assert(cache_pre.valid_read(addr@, fetched_data));
                    assert forall |a| #[trigger] cache_lbl->reads.contains_key(a)
                        implies cache_pre.valid_read(a, cache_lbl->reads[a]) by {
                        assert(a == addr@);
                    };
                    assert(forall |a| #[trigger] cache_lbl->writes.contains_key(a)
                        ==> cache_pre.valid_write(a));

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

                    assert(addr@ == self.status.unwrap().lsn_addr_index@[start_lsn as nat]);

                    let ghost journal_reads = to_journal_records(reads);
                    let ghost actual_start_lsn = journal_reads[addr@].message_seq.maybe_discard_old(
                        self@.snapshot.boundary_lsn,
                    ).seq_start;
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
                    assert(actual_start_lsn
                        == journal_reads[addr@].message_seq.maybe_discard_old(self.seq_start()).seq_start);
                    assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(
                        self@.snapshot.boundary_lsn,
                        journal_reads[addr@].message_seq,
                        actual_start_lsn,
                    ));
                    let ghost journal_dv = LinkedJournal_v::DiskView{
                        boundary_lsn: self@.snapshot.boundary_lsn,
                        entries: to_journal_records(journal_raw_disk),
                    };
                    let ghost tj = LinkedJournal_v::TruncatedJournal{
                        freshest_rec: self@.snapshot.freshest_rec(),
                        disk_view: journal_dv,
                    };
                    let ghost model_index = self.status.unwrap().lsn_addr_index@;
                    assert(journal_dv.entries[addr@] == journal_reads[addr@]);
                    tj.build_lsn_addr_index_ensures();
                    assert(tj.index_range_valid(model_index));
                    assert(tj.every_lsn_at_addr_indexed_to_addr(model_index, addr@));
                    assert(model_index.contains_key(actual_start_lsn));
                    assert(model_index[actual_start_lsn] == addr@);

                    assume(false);
                    reveal(CachedJournal::State::next_by);
                    assert(CachedJournal::State::next_by(
                        self@,
                        self@,
                        journal_lbl,
                        CachedJournal::Step::read_for_recovery(actual_start_lsn, addr@),
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
        old(self)@.snapshot.freshest_rec() is Some ==>
            journal_disk_inv(
                LinkedJournal_v::DiskView{
                    boundary_lsn: old(self)@.snapshot.boundary_lsn,
                    entries: to_journal_records(journal_raw_disk_ghost@),
                },
                old(self)@.snapshot.freshest_rec()),
    ensures ({
        &&& self.wf()
        &&& self@.wf()
        &&& self.alloc_au() == old(self).alloc_au()
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
                        assert(LinkedJournal_v::DiskView{boundary_lsn: bdy as nat, entries: to_journal_records(reads)}.valid_ranking(map!{})); // witness

                        if let Some(root) = curr {
                            let mut index_initialized = false;
                            index = ILsnAddrIndex::new(u64::MAX);

                            // journal_disk_inv now from requires (system invariant pull-down)
                            let ghost journal_disk = LinkedJournal_v::DiskView{boundary_lsn: bdy as nat, entries: to_journal_records(journal_raw_disk)};

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
                                forall |addr| #[trigger] to_journal_records(reads).contains_key(addr) ==> {
                                    let next = to_journal_records(reads)[addr].cropped_prior(bdy as nat);
                                    next is None || to_journal_records(reads).contains_key(next.unwrap()) || next == iaddr_view(curr)
                                },
                                iaddr_view(curr) == build_lsn_addr_index_from_reads_next_ptr(to_journal_records(reads), bdy as nat, self@.snapshot.freshest_rec()),
                                acyclic_reads(bdy as nat, to_journal_records(reads)),
                                !index_initialized ==> curr == self.snapshot.freshest_rec,
                                index_initialized ==> (index.seq_start() == bdy
                                    || index.seq_start() == journal_disk.entries[curr.unwrap()@].message_seq.seq_end),
                                bdy <= index.seq_start(),
                                index_initialized ==> {
                                    &&& index.seq_end() == seq_end
                                    &&& reads.contains_key(root@)
                                    &&& index@ =~= build_lsn_addr_index_from_reads(to_journal_records(reads), bdy as nat, self@.snapshot.freshest_rec())
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
                                            let ghost reads_post = to_journal_records(reads_pre).insert(addr@, to_journal_records(reads)[addr@]);
                                            disk_view_valid_ranking_subset(journal_disk, reads_post, ranking);
                                            build_lsn_addr_index_from_reads_next_ptr_after_insert(to_journal_records(reads_pre), bdy as nat, self@.snapshot.freshest_rec(), iaddr_view(curr), to_journal_records(reads)[addr@]);
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
                                        proof { to_journal_records_entry_from_exec_parse(self.fmt, reads, addr@, i_journal_record); }
                                        proof {
                                            if was_initialized {
                                                build_lsn_addr_index_from_reads_next_ptr_not_in_reads(
                                                    to_journal_records(reads_pre),
                                                    bdy as nat,
                                                    self@.snapshot.freshest_rec(),
                                                    prev,
                                                );
                                                assert(prev is Some);
                                                assert(prev == Some(addr@));
                                                assert(!to_journal_records(reads_pre).contains_key(addr@));
                                                assert(!reads_pre.contains_key(addr@));
                                                assert(index@ == build_lsn_addr_index_from_reads(
                                                    to_journal_records(reads_pre),
                                                    bdy as nat,
                                                    self@.snapshot.freshest_rec()
                                                ));
                                                assert(!index@.values().contains(addr@)) by {
                                                    if index@.values().contains(addr@) {
                                                        build_lsn_addr_index_from_reads_values_in_reads(
                                                            to_journal_records(reads_pre),
                                                            bdy as nat,
                                                            self@.snapshot.freshest_rec(),
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
                                                let ptr2_data = to_journal_records(reads)[addr@];
                                                let start_lsn = vstd::math::max(bdy as int, ptr2_data.message_seq.seq_start as int) as nat;
                                                let end_lsn = ptr2_data.message_seq.seq_end;
                                                let ghost reads_post = to_journal_records(reads_pre).insert(addr@, ptr2_data);
                                                assert(to_journal_records(reads) == reads_post);
                                                let ghost build_pre = build_lsn_addr_index_from_reads(to_journal_records(reads_pre), bdy as nat, self@.snapshot.freshest_rec());
                                                if !was_initialized {
                                                    build_lsn_addr_index_from_reads_next_ptr_not_in_reads(to_journal_records(reads_pre), bdy as nat, self@.snapshot.freshest_rec(), iaddr_view(curr));
                                                }
                                                assert(lsn_disjoint(build_pre.dom(), start_lsn, end_lsn)) by {
                                                    index_pre.view_domain();
                                                };
                                                build_lsn_addr_index_from_reads_extend_next_ptr(to_journal_records(reads_pre), bdy as nat, self@.snapshot.freshest_rec(), prev, ptr2_data);
                                            }
                                            build_lsn_addr_index_from_reads_next_ptr_after_insert(to_journal_records(reads_pre), bdy as nat, self@.snapshot.freshest_rec(), prev, to_journal_records(reads)[addr@]);
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
                            au_page_bounds: Ghost(Map::empty()),
                            clean_watermark_lsn: i_seq_end,
                        });

                        
                        proof {
                            let (_, journal_lbl) = load_index_labels(reads);
                            let ptr = old(self)@.snapshot.freshest_rec();
                            let bdy = old(self)@.snapshot.boundary_lsn;
                            let journal_reads = to_journal_records(reads);
                            let lsn_addr_index = build_lsn_addr_index_from_reads(journal_reads, bdy, ptr);
                            let seq_end = if ptr is Some { journal_reads[ptr.unwrap()].message_seq.seq_end } else { bdy };
 
                            index.derive_recovery_index_properties();
                            assert(lsn_index_domain_exact(index@, index.seq_start() as nat, index.seq_end() as nat));
                            assert( lsn_addr_index =~= index@ );
                            assert(lsn_index_domain_exact(
                                self.status.unwrap().lsn_addr_index@,
                                self@.snapshot.boundary_lsn,
                                self@.status.unwrap().unmarshalled_tail.seq_start,
                            ));
                            assert(self@.status.unwrap().unmarshalled_tail == MsgHistory::empty_history_at(index.seq_end() as nat));
                            assert(all_addrs_have_complete_lsn_ranges(
                                self.status.unwrap().lsn_addr_index@,
                                self@.snapshot.boundary_lsn,
                            ));
                            assert(lsn_addr_index.dom() == Set::new(|lsn: LSN| bdy <= lsn < seq_end));
                            assume( exists |au_depth: nat, page_depth: nat| #![auto]
                                CachedJournal::State::next_by(old(self)@, self@, journal_lbl, CachedJournal::Step::load_index(au_depth, page_depth)) );
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
        self.alloc_au() == old(self).alloc_au(),
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
                status.unmarshalled_tail.push(KeyedMessage{key, message: Message::Define{value}});
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

    pub exec fn peek_next_addr(&self) -> (out: IAddress)
        ensures
            out.au as nat == self.alloc_au(),
            out@.au == self.alloc_au(),
    {
        self.journal_alloc.peek_next_addr()
    }

    pub exec fn advance_next_addr(&mut self)
        ensures
            self@ == old(self)@,
            self.format_ok() == old(self).format_ok(),
            self.alloc_au() == old(self).alloc_au(),
            old(self).wf() ==> self.wf(),
            old(self).index_ready() ==> self.index_ready(),
            self.seq_start() == old(self).seq_start(),
            self.seq_end() == old(self).seq_end(),
    {
        self.journal_alloc.advance_next_addr();
    }

    pub closed spec fn alloc_au(&self) -> nat
    {
        self.journal_alloc.alloc_au() as nat
    }

    fn record_fits_in_page(&self, message_len: usize) -> (fits: bool)
        ensures
            fits <==> message_len <= self.fmt.field2_fmt.max_length,
    {
        message_len <= self.fmt.field2_fmt.max_length
    }

    pub exec fn internal_journal_marshall_reserve_slot(&mut self, cache: &mut FracCacheImpl) -> (out: MarshalReserveResult)
        requires
            old(self).wf(),
            old(self).index_ready(),
            old(cache).wf(),
            old(cache)@.inv(),
        ensures
            self.wf(),
            old(self)@ == self@,
            self.seq_start() == old(self).seq_start(),
            self.alloc_au() == old(self).alloc_au(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match out {
                MarshalReserveResult::Reserved{addr, slot_handle} => {
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_write_handle(&addr, slot_handle)
                    &&& cache@.valid_write(addr@)
                    &&& !self.status.unwrap().lsn_addr_index@.values().contains(addr@)
                    &&& Cache::State::next(old(cache)@, cache@, Cache::Label::Internal)
                },
                MarshalReserveResult::CacheFull{} => {
                    &&& *cache == *old(cache)
                },
            },
    {
        let ghost cache0 = *cache;
        let addr = self.peek_next_addr();
        proof {
            assume(!old(self).status.unwrap().lsn_addr_index@.values().contains(addr@));
            assume(!cache0.entry_fetched(&addr));
        }
        match cache.reserve_for_write_absent(&addr) {
            ReserveWriteResult::Reserved{slot_handle} => {
                self.advance_next_addr();
                proof {
                    assert(Cache::State::next(cache0@, cache@, Cache::Label::Internal));
                    Cache::State::inv_next(cache0@, cache@, Cache::Label::Internal);
                    assume(!self.status.unwrap().lsn_addr_index@.values().contains(addr@));
                }
                MarshalReserveResult::Reserved{addr, slot_handle}
            },
            ReserveWriteResult::CacheFull => {
                proof {
                    assert(cache@ == cache0@);
                }
                MarshalReserveResult::CacheFull{}
            },
        }
    }

    pub exec fn internal_journal_marshall_commit_reserved(
        &mut self,
        cache: &mut FracCacheImpl,
        addr: IAddress,
        mut slot_handle: MutHandle,
    ) -> (out_raw_page: Ghost<RawPage>)
        requires
            old(self).wf(),
            old(self).index_ready(),
            old(self).seq_end() != old(self).marshalled_seq_end(),
            old(cache).wf(),
            old(cache)@.inv(),
            old(cache).entry_fetched(&addr),
            old(cache).valid_write_handle(&addr, slot_handle),
            old(cache)@.valid_write(addr@),
            !old(self).status.unwrap().lsn_addr_index@.values().contains(addr@),
        ensures ({
            &&& self.wf()
            &&& self.index_ready()
            &&& self.alloc_au() == old(self).alloc_au()
            &&& self.seq_start() == old(self).seq_start()
            &&& self.seq_end() == old(self).seq_end()
            &&& old(self)@.status.unwrap().unmarshalled_tail.seq_start
                <= self@.status.unwrap().unmarshalled_tail.seq_start
            &&& cache.wf()
            &&& cache.valid_load_handles_preserved(*old(cache))
            &&& cache.valid_writeback_handles_preserved(*old(cache))
            &&& CachedJournal::State::next(
                old(self)@,
                self@,
                journal_marshall_labels(addr@, out_raw_page@).0,
            )
            &&& Cache::State::next(
                old(cache)@,
                cache@,
                journal_marshall_labels(addr@, out_raw_page@).1,
            )
        }),
    {
        let ghost pre_journal = self@;
        let ghost pre_cache = cache@;

        let mut status_opt = None;
        core::mem::swap(&mut self.status, &mut status_opt);
        let mut status = match status_opt {
            Some(s) => s,
            None => {
                proof { assert(false); }
                unreached()
            },
        };

        let tail_start = status.lsn_addr_index.exec_seq_end();
        let tail_len = status.unmarshalled_tail.len();
        let max_msgs = self.fmt.field2_fmt.max_length;
        let cut_count: usize = if tail_len > max_msgs { max_msgs } else { tail_len };
        if cut_count == 0 {
            self.status = Some(status);
            please_panic();
            return unreached();
        }

        let ghost old_unmarshalled_tail = status.unmarshalled_tail@;
        // split off to get our marshalled pairs and new tail
        let mut marshalled_pairs = status.unmarshalled_tail.split_off(cut_count);
        core::mem::swap(&mut status.unmarshalled_tail, &mut marshalled_pairs);
        proof {
            assert(status.unmarshalled_tail@ == old_unmarshalled_tail.subrange(cut_count as int, old_unmarshalled_tail.len() as int));
        }

        let msgs: Vec<KeyedMessage> = marshalled_pairs;
        let record = IJournalRecord{
            header: IJournalHeader{
                prior_rec: self.snapshot.freshest_rec,
                start_lsn: tail_start,
            },
            messages: msgs,
        };

        proof {
            assert(forall |i: int| 0 <= i < record.messages.len()
                ==> self.fmt.field2_fmt.marshallable_at(record.messages@, i));
        }
        let end = self.fmt.exec_marshall(&record, &mut slot_handle.rec, 0);
        if end > PAGE_SIZE_BYTES {
            self.status = Some(status);
            please_panic();
            return unreached();
        }

        let ghost raw = slot_handle.rec@;
        cache.write_release(&addr, slot_handle);

        if u64::MAX - tail_start < cut_count as u64 {
            convert_overflow_into_liveness_failure();
        }

        let ghost old_index = status.lsn_addr_index@;
        let new_tail_start = tail_start + cut_count as u64;
        status.lsn_addr_index.index_append_record(tail_start, new_tail_start, addr);
        status.au_page_bounds = Ghost(status.au_page_bounds@.insert(addr@.au, addr@.page));
        self.snapshot.freshest_rec = Some(addr);
        self.status = Some(status);

        proof {
            let ghost writes = map!{addr@ => raw};
            let ghost cut = new_tail_start as nat;
            let ghost marshalled_record = JournalRecord{
                message_seq: pre_journal.status.unwrap().unmarshalled_tail.discard_recent(cut),
                prior_rec: pre_journal.snapshot.freshest_rec(),
            };
            let ghost lbls = journal_marshall_labels(addr@, raw);
            let ghost journal_lbl = lbls.0;
            let ghost cache_lbl = lbls.1;
            assert(to_journal_records(writes)[addr@] == record.parsedv().view()) by {
                assert(self.fmt.parsable(raw.subrange(0, end as int)));
                assert(self.fmt.parse(raw.subrange(0, end as int)) == record.parsedv());

                let ghost f1_end = self.fmt.field1_fmt.uniform_size() as int;
                let ghost f2_end = f1_end + self.fmt.field2_fmt.uniform_size() as int;
                assert(raw.subrange(0, end as int).subrange(0, f1_end) == raw.subrange(0, f1_end));
                assert(raw.subrange(0, end as int).subrange(f1_end, f2_end) == raw.subrange(f1_end, f2_end));

                assert(self.fmt.parsable(raw));
                assert(self.fmt.parse(raw) == self.fmt.parse(raw.subrange(0, end as int)));
                assert(self.fmt.parse(raw) == record.parsedv());
                assert(raw_page_to_record(raw) == record.parsedv().view());
                assert(to_journal_records(writes)[addr@] == raw_page_to_record(raw));
            };
            assert(to_journal_records(writes) == map!{addr@ => marshalled_record}) by {
                assert forall |a: Address|
                    #[trigger] to_journal_records(writes).contains_key(a)
                    implies map!{addr@ => marshalled_record}.contains_key(a)
                        && to_journal_records(writes)[a] == map!{addr@ => marshalled_record}[a] by {
                    assert(a == addr@);
                };
                assert forall |a: Address|
                    #[trigger] map!{addr@ => marshalled_record}.contains_key(a)
                    implies to_journal_records(writes).contains_key(a)
                        && to_journal_records(writes)[a] == map!{addr@ => marshalled_record}[a] by {
                    assert(a == addr@);
                };
            }
            assert(journal_lbl == CachedJournal::Label::JournalMarshal{writes: map!{addr@ => marshalled_record}});
            assert(self@.status.unwrap().unmarshalled_tail
                == pre_journal.status.unwrap().unmarshalled_tail.discard_old(cut));
            assert(self@.status.unwrap().unmarshalled_tail.seq_start == cut);
            reveal(CachedJournal::State::next_by);
            reveal(CachedJournal::State::next);
            assume(CachedJournal::State::next_by(
                pre_journal,
                self@,
                CachedJournal::Label::JournalMarshal{writes: map!{addr@ => marshalled_record}},
                CachedJournal::Step::internal_journal_marshal(cut, addr@),
            ));
            assert(CachedJournal::State::next(
                pre_journal,
                self@,
                journal_lbl,
            ));
            assert(Cache::State::next(
                pre_cache,
                cache@,
                cache_lbl,
            ));

            let clean = self.status.unwrap().clean_watermark_lsn;
            let bdy = self.snapshot.boundary_lsn;
            let new_seq_end = self.status.unwrap().lsn_addr_index.seq_end();
            if clean > bdy && clean < new_seq_end {
                self.status.unwrap().lsn_addr_index.view_domain();
                assert(self.status.unwrap().lsn_addr_index@.contains_key((clean - 1) as nat));
                assert(self.status.unwrap().lsn_addr_index@.contains_key(clean as nat));
                if clean < tail_start {
                    assert(self.status.unwrap().lsn_addr_index@[(clean - 1) as nat]
                        != self.status.unwrap().lsn_addr_index@[clean as nat]);
                } else {
                    assert(clean == tail_start);
                    assert(self.status.unwrap().lsn_addr_index@[clean as nat] == addr@);
                    assert(self.status.unwrap().lsn_addr_index@[(clean - 1) as nat]
                        == old_index[(clean - 1) as nat]);
                    assert(!old_index.values().contains(addr@));
                    assert(old_index[(clean - 1) as nat] != addr@);
                    assert(self.status.unwrap().lsn_addr_index@[(clean - 1) as nat]
                        != self.status.unwrap().lsn_addr_index@[clean as nat]);
                }
            }
        }
        Ghost(raw)
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
    }

    pub proof fn view_marshaled_seq_end_ensures(&self)
        requires
            self.index_ready(),
        ensures
            self@.marshalled_seq_end() == self.marshalled_seq_end(),
    {
        broadcast use JournalImpl::view_ensures;
    }

    pub proof fn view_seq_start_ensures(&self)
        ensures
            self@.snapshot.boundary_lsn == self.seq_start(),
    {
    }

    pub proof fn seq_start_le_marshalled_end(&self)
        requires self.wf(), self.index_ready()
        ensures self.seq_start() as nat <= self@.status.unwrap().unmarshalled_tail.seq_start
    {
    }

    pub proof fn clean_watermark_le_marshaled_seq_end(&self)
        requires self.wf(), self.index_ready()
        ensures self.clean_watermark() <= self.marshalled_seq_end()
    {
    }

    pub proof fn seq_start_le_seq_end(&self)
        requires self.wf(), self.index_ready()
        ensures self.seq_start() <= self.seq_end()
    {
        match &self.status {
            Some(status) => {
                status.lsn_addr_index.seq_start_le_seq_end();
                assert(self.snapshot.boundary_lsn == status.lsn_addr_index.seq_start());
                assert(self.snapshot.boundary_lsn as nat <= status.lsn_addr_index.seq_end() as nat);
                assert(status.lsn_addr_index.seq_end() as nat
                    <= status.lsn_addr_index.seq_end() as nat + status.unmarshalled_tail.len() as nat);
            }
            None => {
                assert(false);
            }
        }
    }

    /// All keys in the model-level lsn_addr_index are >= boundary_lsn.
    /// This follows from ILsnAddrIndex::view_domain() + wf() connecting boundary_lsn to seq_start.
    pub proof fn lsn_addr_index_keys_bounded_below(&self)
        requires self.wf(), self.index_ready()
        ensures forall |lsn: LSN| self.status.unwrap().lsn_addr_index@.contains_key(lsn)
            ==> lsn >= self@.snapshot.boundary_lsn,
    {
        // wf: self.snapshot.boundary_lsn == status.lsn_addr_index.seq_start()
        // view_domain: keys in [seq_start, seq_end), so all keys >= seq_start == boundary_lsn
        match &self.status {
            Some(status) => {
                status.lsn_addr_index.view_domain();
            }
            None => {}
        }
    }

    /// When the journal is empty (exec seq_start == model seq_end), freshest_rec is None.
    pub proof fn freshest_rec_none_when_empty(&self)
        requires self.wf(), self.index_ready(), self.seq_start() == self.seq_end()
        ensures self@.snapshot.freshest_rec() is None
    {
        self.view_seq_end_ensures();
        match &self.status {
            Some(status) => {
                assert(self@.seq_end() == self.seq_end());
                assert(self.snapshot.boundary_lsn as nat == self@.seq_end()) by {
                    assert(self.seq_start() as nat == self@.seq_end());
                }
                assert(self.snapshot.boundary_lsn as nat
                    == status.lsn_addr_index.seq_end() as nat + status.unmarshalled_tail.len() as nat);
                assert(status.lsn_addr_index.seq_end() as nat <= self.snapshot.boundary_lsn as nat);

                assert(self.snapshot.boundary_lsn == status.lsn_addr_index.seq_end());
                if self.snapshot.freshest_rec is Some {
                    assert(self.snapshot.boundary_lsn < status.lsn_addr_index.seq_end());
                    assert(false);
                }
            }
            None => {
                assert(false);
            }
        }
    }

    pub fn is_empty(&self) -> bool
    requires self.index_ready()
    {
        self.status.as_ref().unwrap().unmarshalled_tail.len() > 0 || self.snapshot.freshest_rec.is_some()
    }

    /// The clean high water mark: the seq_end of the highest page in the journal chain
    /// for which it and all lower pages are Filled+Clean in cache.
    /// Independent of marshalled_seq_end — marshalling may have raced ahead with dirty pages.
    pub closed spec fn clean_watermark(&self) -> LSN {
        self.status.unwrap().clean_watermark_lsn as nat
    }

    pub exec fn exec_clean_watermark(&self) -> (out: ILsn)
    requires
        self.wf(),
        self.index_ready(),
    ensures
        out as nat == self.clean_watermark(),
    {
        self.status.as_ref().unwrap().clean_watermark_lsn
    }

    pub exec fn exec_marshaled_seq_end(&self) -> (out: ILsn)
    requires
        self.wf(),
        self.index_ready(),
    ensures
        out as nat == self.marshalled_seq_end(),
    {
        self.status.as_ref().unwrap().lsn_addr_index.exec_seq_end()
    }

    /// Check whether the journal is ready to freeze for commit at target_lsn.
    /// Returns a frozen journal when target_lsn is already <= clean watermark;
    /// otherwise indicates that flush work is still needed.
    pub exec fn freeze_for_commit(&self, target_lsn: ILsn) -> (out: CleanForCommitResult)
    requires
        self.wf(),
        self.index_ready(),
    ensures
        match out {
            CleanForCommitResult::Frozen{frozen_journal} => {
                &&& target_lsn as nat <= self.clean_watermark()
                &&& frozen_journal.wf()
                &&& frozen_journal.seq_start() as nat == self.seq_start()
                &&& frozen_journal.seq_end as nat == self.clean_watermark()
                &&& CachedJournal::State::next(
                    self@,
                    self@,
                    CachedJournal::Label::FreezeForCommit{
                        frozen: frozen_journal.snapshot@,
                        reads: freeze_reads_for_seq_end(
                            frozen_journal.snapshot@,
                            frozen_journal.seq_end as nat,
                        ),
                    },
                )
            },
            CleanForCommitResult::NeedsFlush{} => {
                self.clean_watermark() < target_lsn as nat
            }
        },
    {
        let status = self.status.as_ref().unwrap();
        let clean = status.clean_watermark_lsn;
        if target_lsn <= clean {
            let boundary = self.snapshot.boundary_lsn;
            let mut clean_seg_end: ILsn = 0;
            let freshest_rec = if clean == boundary {
                None
            } else {
                let (addr, seg_end) = status.lsn_addr_index.lookup_lsn_with_segment_end(clean - 1);
                clean_seg_end = seg_end;
                Some(addr)
            };
            let frozen_journal = FrozenJournal{
                snapshot: IJournalSnapshot{
                    boundary_lsn: boundary,
                    freshest_rec,
                    first: match freshest_rec {
                        Some(_) => status.lsn_addr_index.lookup_lsn_with_segment_end(boundary).0.au,
                        None => 0,
                    },
                },
                seq_end: clean,
            };
            proof {
                let lbl = CachedJournal::Label::FreezeForCommit{
                    frozen: frozen_journal.snapshot@,
                    reads: freeze_reads_for_seq_end(
                        frozen_journal.snapshot@,
                        frozen_journal.seq_end as nat,
                    ),
                };
                reveal(CachedJournal::State::next_by);
                reveal(CachedJournal::State::next);

                if clean == boundary {
                    assume(CachedJournal::State::next_by(
                        self@,
                        self@,
                        lbl,
                        CachedJournal::Step::freeze_for_commit(),
                    ));
                    assert(CachedJournal::State::next(self@, self@, lbl));
                } else {
                    let ghost index_seq_end = status.lsn_addr_index.seq_end() as nat;
                    status.lsn_addr_index.derive_recovery_index_properties();
                    assert(lsn_index_domain_exact(
                        self.status.unwrap().lsn_addr_index@,
                        self@.snapshot.boundary_lsn,
                        index_seq_end,
                    ));
                    assert((self@.snapshot.boundary_lsn) < index_seq_end);

                    assert(frozen_journal.snapshot@.freshest_rec()
                        == Some(self.status.unwrap().lsn_addr_index@[(clean - 1) as nat]));

                    let addr = frozen_journal.snapshot.freshest_rec.unwrap();
                    let ghost seg_values = self.status.unwrap().lsn_addr_index@.restrict(
                        Set::new(|k: LSN| (clean - 1) as nat <= k < clean_seg_end as nat)
                    ).values();
                    assert(seg_values == set![addr@]);
                    assert(clean_seg_end <= clean) by {
                        if clean_seg_end > clean {
                            assert(self.status.unwrap().lsn_addr_index@.contains_key(clean as nat));
                            assert(self.status.unwrap().lsn_addr_index@.contains_key((clean - 1) as nat));
                            assert(self.status.unwrap().lsn_addr_index@[(clean - 1) as nat] == addr@);
                            assert((clean as nat) < (clean_seg_end as nat));
                            assert(seg_values.contains(self.status.unwrap().lsn_addr_index@[clean as nat])) by {
                                assert(self.status.unwrap().lsn_addr_index@.restrict(
                                    Set::new(|k: LSN| (clean - 1) as nat <= k < clean_seg_end as nat)
                                ).contains_key(clean as nat));
                            };
                            assert(set![addr@].contains(self.status.unwrap().lsn_addr_index@[clean as nat]));
                            assert(self.status.unwrap().lsn_addr_index@[clean as nat] == addr@);
                            assert(self.status.unwrap().lsn_addr_index@[(clean - 1) as nat]
                                == self.status.unwrap().lsn_addr_index@[clean as nat]);
                            assert(clean < status.lsn_addr_index.seq_end());
                            assert(self.status.unwrap().lsn_addr_index@[(clean - 1) as nat]
                                != self.status.unwrap().lsn_addr_index@[clean as nat]);
                            assert(false);
                        }
                    }
                    assert(clean <= clean_seg_end);
                    assert(clean_seg_end == clean);
                    assert(largest_lsn_plus_one(self.status.unwrap().lsn_addr_index@, Some(addr@))
                        == clean_seg_end as nat);
                    assert(largest_lsn_plus_one(self.status.unwrap().lsn_addr_index@, Some(addr@))
                        == clean as nat);
                    assert(discard_old_ptr_by_index(
                        self.status.unwrap().lsn_addr_index@,
                        Some(addr@),
                        frozen_journal.snapshot.boundary_lsn as nat,
                    ) == Some(addr@));
                    assert(frozen_journal.seq_end as nat
                        == largest_lsn_plus_one(self.status.unwrap().lsn_addr_index@, Some(addr@)));
                    let ghost freeze_reads = freeze_reads_for_seq_end(
                        frozen_journal.snapshot@,
                        frozen_journal.seq_end as nat,
                    );
                    assert(frozen_journal.snapshot@.freshest_rec() == Some(addr@));
                    assert(freeze_reads.contains_key(addr@));
                    assert(freeze_reads[addr@].message_seq.seq_end == frozen_journal.seq_end as nat);

                    assume(CachedJournal::State::next_by(
                        self@,
                        self@,
                        lbl,
                        CachedJournal::Step::freeze_for_commit(),
                    ));
                    assume(CachedJournal::State::next(self@, self@, lbl));
                }
            }
            CleanForCommitResult::Frozen{frozen_journal}
        } else {
            CleanForCommitResult::NeedsFlush{}
        }
    }

    pub exec fn discard_old(&mut self, boundary_lsn: ILsn)
    requires
        old(self).wf(),
        old(self).index_ready(),
        old(self).seq_start() <= boundary_lsn <= old(self).marshalled_seq_end(),
    ensures
        self.wf(),
        self.index_ready(),
        self.alloc_au() == old(self).alloc_au(),
        self.seq_start() == boundary_lsn as nat,
        self.seq_end() == old(self).seq_end(),
        ({
            let new_lsn_au_index = lsn_au_index_discard_up_to(
                old(self)@.status.unwrap().lsn_au_index,
                boundary_lsn as nat,
            );
            let deallocs = old(self)@.status.unwrap().lsn_au_index.values()
                - new_lsn_au_index.values();
            CachedJournal::State::next(
                old(self)@,
                self@,
                CachedJournal::Label::DiscardOld{
                    start_lsn: boundary_lsn as nat,
                    require_end: old(self).seq_end(),
                    deallocs,
                },
            )
        }),
    {
        let ghost pre_journal = old(self)@;
        let old_seq_end = self.exec_seq_end();
        let old_freshest_rec = self.snapshot.freshest_rec;
        let mut status = self.status.take().unwrap();
        let ghost old_index = status.lsn_addr_index@;
        let old_index_seq_end = status.lsn_addr_index.exec_seq_end();
        proof {
            status.lsn_addr_index.derive_lsn_index_domain_exact();
        }
        let old_clean = status.clean_watermark_lsn;
        status.lsn_addr_index.discard_up_to(boundary_lsn);
        let ghost new_lsn_au_index_for_bounds = lsn_au_index_discard_up_to(
            pre_journal.status.unwrap().lsn_au_index,
            boundary_lsn as nat,
        );
        status.au_page_bounds = Ghost(status.au_page_bounds@.restrict(new_lsn_au_index_for_bounds.values()));

        if old_clean < boundary_lsn {
            status.clean_watermark_lsn = boundary_lsn;
        }
        self.snapshot.boundary_lsn = boundary_lsn;
        self.snapshot.freshest_rec =
            if boundary_lsn == old_index_seq_end { None } else { old_freshest_rec };
        self.status = Some(status);

        proof {
            assert(self.wf()) by {
                assert(self.status is Some);
                assert(self.status.unwrap().wf());
                assert(self.status.unwrap().lsn_addr_index.seq_start() == boundary_lsn);
                assert(self.status.unwrap().lsn_addr_index.seq_end() == old_index_seq_end);
                assert(self.snapshot.boundary_lsn == self.status.unwrap().lsn_addr_index.seq_start());
                assert(self.snapshot.boundary_lsn <= self.status.unwrap().clean_watermark_lsn);
                assert(self.status.unwrap().clean_watermark_lsn <= self.status.unwrap().lsn_addr_index.seq_end());
                assert(self.snapshot.freshest_rec is Some <==> self.snapshot.boundary_lsn < self.status.unwrap().lsn_addr_index.seq_end()) by {
                    assert(boundary_lsn <= old_index_seq_end);
                    if boundary_lsn == old_index_seq_end {
                        assert(self.snapshot.freshest_rec is None);
                    } else {
                        assert(boundary_lsn < old_index_seq_end) by {
                            if !(boundary_lsn < old_index_seq_end) {
                                assert(old_index_seq_end <= boundary_lsn);
                                assert(boundary_lsn == old_index_seq_end);
                            }
                        }
                        assert(self.snapshot.boundary_lsn < self.status.unwrap().lsn_addr_index.seq_end());
                        assert(pre_journal.snapshot.boundary_lsn <= boundary_lsn as nat);
                        assert(pre_journal.snapshot.boundary_lsn < pre_journal.seq_end());
                        assert(pre_journal.snapshot.freshest_rec() is Some);
                        assert(self.snapshot.freshest_rec == old_freshest_rec);
                        assert(self.snapshot.freshest_rec is Some);
                    }
                }
                if self.snapshot.freshest_rec is Some {
                    let last_lsn = (self.status.unwrap().lsn_addr_index.seq_end() - 1) as nat;
                    assert(self.snapshot.boundary_lsn < self.status.unwrap().lsn_addr_index.seq_end());
                    assert(self.snapshot.freshest_rec == old_freshest_rec);
                    assert(pre_journal.snapshot.freshest_rec() is Some);
                    crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to_ensures(old_index, boundary_lsn as nat);
                    assert(boundary_lsn as nat <= last_lsn);
                    assert(old_index.contains_key(last_lsn));
                    assert(crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to(
                        old_index,
                        boundary_lsn as nat,
                    ).contains_key(last_lsn));
                    assert(self.status.unwrap().lsn_addr_index@.contains_key(last_lsn));
                    assert(pre_journal.snapshot.freshest_rec().unwrap() == old_index[last_lsn]);
                    assert(self.status.unwrap().lsn_addr_index@[last_lsn] == old_index[last_lsn]);
                    assert(self.status.unwrap().lsn_addr_index@[last_lsn]
                        == self.snapshot.freshest_rec.unwrap()@);
                }
            }
            let ghost new_lsn_au_index = lsn_au_index_discard_up_to(
                pre_journal.status.unwrap().lsn_au_index,
                boundary_lsn as nat,
            );
            let ghost deallocs = pre_journal.status.unwrap().lsn_au_index.values()
                - new_lsn_au_index.values();
            let lbl = CachedJournal::Label::DiscardOld{
                start_lsn: boundary_lsn as nat,
                require_end: pre_journal.seq_end(),
                deallocs,
            };
            reveal(CachedJournal::State::next_by);
            reveal(CachedJournal::State::next);
            assume(CachedJournal::State::next_by(
                pre_journal,
                self@,
                lbl,
                CachedJournal::Step::discard_old(),
            ));
            assert(CachedJournal::State::next(pre_journal, self@, lbl));
        }
    }

    pub exec fn begin_writeback_for_target(
        &mut self,
        cache: &mut FracCacheImpl,
        target_lsn: ILsn,
    ) -> (out: BeginWritebackForTargetResult)
    requires
        old(self).wf(),
        old(self).index_ready(),
        old(cache).wf(),
        target_lsn as nat <= old(self).marshalled_seq_end(),
    ensures
        self.wf(),
        self.index_ready(),
        self.alloc_au() == old(self).alloc_au(),
        cache.wf(),
        cache.valid_load_handles_preserved(*old(cache)),
        cache.valid_writeback_handles_preserved(*old(cache)),
        self.seq_start() == old(self).seq_start(),
        self.seq_end() == old(self).seq_end(),
        old(self).clean_watermark() <= self.clean_watermark(),
        self.clean_watermark() <= old(self).marshalled_seq_end(),
        self.marshalled_seq_end() == old(self).marshalled_seq_end(),
        old(self).clean_watermark() == self.clean_watermark() ==> self@ == old(self)@,
        match out {
            BeginWritebackForTargetResult::Acquired{request, flushed_domain} => {
                &&& target_lsn as nat > old(self).clean_watermark()
                &&& cache.valid_writeback_handle(&request.addr, request.handle)
                &&& Cache::State::next(
                    old(cache)@,
                    old(cache)@,
                    Cache::Label::EvictableCheck{aus: to_aus(flushed_domain@)},
                )
                &&& Cache::State::next(
                    old(cache)@,
                    cache@,
                    Cache::Label::DiskOps{
                        requests: set![DiskRequest::WriteReq{to: request.addr@, data: request.handle.rec@}],
                        responses: map!{},
                    },
                )
                &&& old(self).clean_watermark() < self.clean_watermark() ==> CachedJournal::State::next(
                    old(self)@,
                    self@,
                    CachedJournal::Label::ObserveCleanAUs{aus: to_aus(flushed_domain@)},
                )
            },
            BeginWritebackForTargetResult::Complete{flushed_domain} => {
                &&& cache@ == old(cache)@
                &&& Cache::State::next(
                    old(cache)@,
                    old(cache)@,
                    Cache::Label::EvictableCheck{aus: to_aus(flushed_domain@)},
                )
                &&& old(self).clean_watermark() < self.clean_watermark() ==> CachedJournal::State::next(
                    old(self)@,
                    self@,
                    CachedJournal::Label::ObserveCleanAUs{aus: to_aus(flushed_domain@)},
                )
            },
        }
    {
        proof {
            assume(false);
        }
        let old_clean = self.status.as_ref().unwrap().clean_watermark_lsn;
        let ghost pre = self@;
        let ghost pre_index = self.status.unwrap().lsn_addr_index@;
        let ghost pre_cache = cache@;
        let ghost pre_cache_impl = *cache;
        let ghost pre_alloc_au = self.alloc_au();
        if target_lsn <= old_clean {
            let ghost flushed_domain = Set::<Address>::empty();
            proof {
                assert(self.alloc_au() == pre_alloc_au);
                assert(cache_evictable_prop(cache@, flushed_domain)) by {
                    assert(forall |a: Address|
                        flushed_domain.contains(a) && #[trigger] cache@.lookup_map.contains_key(a)
                        ==> {
                            &&& cache@.entries[cache@.lookup_map[a]] is Filled
                            &&& cache@.status_map[cache@.lookup_map[a]] is Clean
                        });
                }
                cache_evictable_prop_implies_next(cache@, flushed_domain);
                assert(cache.valid_load_handles_preserved(pre_cache_impl)) by {
                    assert(forall |addr: IAddress, handle: MutHandle|
                        pre_cache_impl.entry_fetched(&addr) && pre_cache_impl.valid_load_handle(&addr, handle)
                        ==> cache.entry_fetched(&addr) && cache.valid_load_handle(&addr, handle));
                }
                FracCacheImpl::valid_writeback_handles_preserved_if_same(pre_cache_impl, *cache);
            }
            return BeginWritebackForTargetResult::Complete{flushed_domain: Ghost(flushed_domain)};
        }
        proof {
            reveal(CachedJournal::State::next_by);
            reveal(CachedJournal::State::next);
        }

        let index_end = self.status.as_ref().unwrap().lsn_addr_index.exec_seq_end();
        let index_for_proof = &self.status.as_ref().unwrap().lsn_addr_index;
        let mut clean_scan = old_clean;
        let mut clean_commit = old_clean;
        let mut blocked = false;
        proof {
            index_for_proof.derive_recovery_index_properties();
            assert(lsn_index_domain_exact(pre_index, self.snapshot.boundary_lsn as nat, index_end as nat));
            let ghost init_flushed = flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
            assert(init_flushed =~= Set::<Address>::empty()) by {
                assert forall |a: Address| #[trigger] init_flushed.contains(a) implies false by {
                    let range = Set::new(|k: LSN| old_clean as nat <= k < clean_commit as nat);
                    let restricted = pre_index.restrict(range);
                    let lsn = choose |lsn: LSN|
                        #[trigger] restricted.contains_key(lsn)
                        && restricted[lsn] == a;
                    assert(old_clean as nat <= lsn < clean_commit as nat);
                };
            }
            assert(cache_evictable_prop(cache@, init_flushed));
        }

        while clean_scan < target_lsn
            invariant
                self.wf(),
                self.index_ready(),
                cache.wf(),
                self.status is Some,
                self.status.unwrap().clean_watermark_lsn == old_clean,
                self.status.unwrap().lsn_addr_index@ == pre_index,
                self@.snapshot == pre.snapshot,
                self@.status.unwrap().unmarshalled_tail == pre.status.unwrap().unmarshalled_tail,
                self@.status.unwrap().au_page_bounds == pre.status.unwrap().au_page_bounds,
                self.alloc_au() == pre_alloc_au,
                self.status.unwrap().lsn_addr_index.seq_end() == index_end,
                old_clean <= clean_commit <= clean_scan,
                clean_scan <= index_end,
                target_lsn <= index_end,
                !blocked ==> clean_commit == clean_scan,
                (clean_commit > self.snapshot.boundary_lsn && clean_commit < index_end) ==> {
                    &&& pre_index.contains_key((clean_commit - 1) as nat)
                    &&& pre_index.contains_key(clean_commit as nat)
                    &&& pre_index[(clean_commit - 1) as nat] != pre_index[clean_commit as nat]
                },
                cache@ == pre_cache,
                cache.valid_load_handles_preserved(pre_cache_impl),
                cache.valid_writeback_handles_preserved(pre_cache_impl),
                cache_evictable_prop(cache@,
                    flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat)),
            decreases if clean_scan < target_lsn { target_lsn - clean_scan } else { 0 }
        {
            let status = self.status.as_ref().unwrap();
            assert(clean_scan < status.lsn_addr_index.seq_end());

            let ghost flushed_before = flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
            let index = &status.lsn_addr_index;
            let (addr, seg_end) = index.lookup_lsn_with_segment_end(clean_scan);
            let ghost scan_seg_values = index@.restrict(
                Set::new(|k: LSN| clean_scan <= k < seg_end)
            ).values();
            proof {
                assert(scan_seg_values == set![addr@]);
            }
            let ghost cache_before = cache@;
            let ghost cache_before_impl = *cache;
            match cache.begin_writeback(&addr) {
                WritebackAcquireResult::Acquired{handle} => {
                    if clean_commit > old_clean {
                        let mut dummy: Option<IJournalStatus> = None;
                        core::mem::swap(&mut self.status, &mut dummy);
                        let old_status = dummy.unwrap();
                        let status = IJournalStatus{
                            clean_watermark_lsn: clean_commit,
                            ..old_status
                        };
                        dummy = Some(status);
                        core::mem::swap(&mut self.status, &mut dummy);
                    }
                    let ghost flushed_domain = flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
                    proof {
                        assert(self.alloc_au() == pre_alloc_au);
                        let req = DiskRequest::WriteReq{to: addr@, data: handle.rec@};
                        let lbl = Cache::Label::DiskOps{
                            requests: set![req],
                            responses: map!{},
                        };
                        assert(cache_before == pre_cache);
                        assert(Cache::State::next(cache_before, cache@, lbl));
                        assert(Cache::State::next(pre_cache, cache@, lbl));
                        assert(flushed_before == flushed_domain);
                        assert(cache_evictable_prop(cache_before, flushed_domain));
                        cache_evictable_prop_implies_next(cache_before, flushed_domain);
                        assert(Cache::State::next(pre_cache, pre_cache, Cache::Label::EvictableCheck{aus: to_aus(flushed_domain)}));
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            pre_cache_impl,
                            cache_before_impl,
                            *cache,
                        );
                        FracCacheImpl::valid_writeback_handles_preserved_transitive(
                            pre_cache_impl,
                            cache_before_impl,
                            *cache,
                        );
                        if clean_commit > old_clean {
                            assume(CachedJournal::State::next_by(
                                pre,
                                self@,
                                CachedJournal::Label::ObserveCleanAUs{aus: to_aus(flushed_domain)},
                                CachedJournal::Step::advance_watermark(clean_commit as nat)
                            ));
                        }
                    }
                    return BeginWritebackForTargetResult::Acquired{
                        request: JournalWritebackRequest{handle, addr},
                        flushed_domain: Ghost(flushed_domain),
                    };
                },
                WritebackAcquireResult::Busy => {
                    proof {
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            pre_cache_impl,
                            cache_before_impl,
                            *cache,
                        );
                        FracCacheImpl::valid_writeback_handles_preserved_transitive(
                            pre_cache_impl,
                            cache_before_impl,
                            *cache,
                        );
                    }
                    blocked = true;
                    clean_scan = seg_end;
                },
                WritebackAcquireResult::NotPresent | WritebackAcquireResult::NotDirty => {
                    proof {
                        FracCacheImpl::valid_load_handles_preserved_transitive(
                            pre_cache_impl,
                            cache_before_impl,
                            *cache,
                        );
                        FracCacheImpl::valid_writeback_handles_preserved_transitive(
                            pre_cache_impl,
                            cache_before_impl,
                            *cache,
                        );
                        cache_next_evictable_implies_prop(cache@, set![addr@]);
                    }
                    if !blocked {
                        proof {
                            let ghost seg_values = pre_index.restrict(
                                Set::new(|k: LSN| clean_commit <= k < seg_end)
                            ).values();
                            assert(clean_commit == clean_scan);
                            assert(seg_values == set![addr@]) by {
                                assert(seg_values == pre_index.restrict(
                                    Set::new(|k: LSN| clean_scan <= k < seg_end)
                                ).values());
                                assert(status.lsn_addr_index@ == pre_index);
                                assert(scan_seg_values == set![addr@]);
                            }
                            let ghost flushed_after = flush_domain_from_index_range(pre_index, old_clean as nat, seg_end as nat);
                            assert(cache_evictable_prop(cache@, flushed_after)) by {
                                let range_before = pre_index.restrict(
                                    Set::new(|k: LSN| old_clean as nat <= k < clean_commit as nat)
                                );
                                let range_after = pre_index.restrict(
                                    Set::new(|k: LSN| old_clean as nat <= k < seg_end as nat)
                                );
                                let range_seg = pre_index.restrict(
                                    Set::new(|k: LSN| clean_commit <= k < seg_end)
                                );
                                assert forall |a: Address|
                                    flushed_after.contains(a) && #[trigger] cache@.lookup_map.contains_key(a)
                                    implies {
                                        &&& cache@.entries[cache@.lookup_map[a]] is Filled
                                        &&& cache@.status_map[cache@.lookup_map[a]] is Clean
                                    } by {
                                    if flushed_before.contains(a) {
                                        assert(cache_evictable_prop(cache@, flushed_before));
                                    } else {
                                        let l = choose |l: LSN| #![auto] range_after.contains_key(l) && range_after[l] == a;
                                        if l < clean_commit as nat {
                                            assert(range_before.contains_key(l));
                                            assert(flushed_before.contains(a));
                                            assert(false);
                                        }
                                        assert(clean_commit as nat <= l < seg_end as nat);
                                        assert(range_seg.contains_key(l));
                                        assert(range_seg[l] == a);
                                        assert(range_seg.values().contains(a));
                                        assert(seg_values == range_seg.values());
                                        assert(seg_values.contains(a));
                                        assert(a == addr@);
                                        assert(cache_evictable_prop(cache@, set![addr@]));
                                    }
                                };
                            }
                        }
                        if seg_end < index_end {
                            assert(pre_index.contains_key(seg_end as nat));
                            assert(pre_index.contains_key((seg_end - 1) as nat));
                            assert(scan_seg_values.contains(pre_index[(seg_end - 1) as nat])) by {
                                assert(index@.restrict(Set::new(|k: LSN| clean_scan <= k < seg_end)).contains_key((seg_end - 1) as nat));
                            }
                            assert(set![addr@].contains(pre_index[(seg_end - 1) as nat])) by {
                                assert(scan_seg_values == set![addr@]);
                            }
                            assert(pre_index[(seg_end - 1) as nat] == addr@);
                            assert(pre_index[seg_end as nat] != addr@);
                            assert(pre_index[(seg_end - 1) as nat] != pre_index[seg_end as nat]);
                        }
                        clean_commit = seg_end;
                    }
                    clean_scan = seg_end;
                },
            };   
        }

        // TODO: is this an assertion instead?
        if clean_commit > old_clean {
            let mut dummy: Option<IJournalStatus> = None;
            core::mem::swap(&mut self.status, &mut dummy);
            let old_status = dummy.unwrap();
            let status = IJournalStatus{
                clean_watermark_lsn: clean_commit,
                ..old_status
            };
            dummy = Some(status);
            core::mem::swap(&mut self.status, &mut dummy);
            proof {
                let ghost flushed_domain = flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
                assume(CachedJournal::State::next_by(
                    pre,
                    self@,
                    CachedJournal::Label::ObserveCleanAUs{aus: to_aus(flushed_domain)},
                    CachedJournal::Step::advance_watermark(clean_commit as nat)
                ));
            }
        }
        let ghost flushed_domain = flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
        proof {
            assert(self.alloc_au() == pre_alloc_au);
            assert(cache_evictable_prop(cache@, flushed_domain));
            assert(cache@ == pre_cache);
            assert(cache_evictable_prop(pre_cache, flushed_domain));
            cache_evictable_prop_implies_next(pre_cache, flushed_domain);
            assert(Cache::State::next(pre_cache, pre_cache, Cache::Label::EvictableCheck{aus: to_aus(flushed_domain)}));
        }
        BeginWritebackForTargetResult::Complete{flushed_domain: Ghost(flushed_domain)}
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
