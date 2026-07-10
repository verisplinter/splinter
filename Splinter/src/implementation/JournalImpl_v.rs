// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::assert_maps_equal;
use crate::abstract_system::MsgHistory_v::{MsgHistory, KeyedMessage};
use crate::abstract_system::StampedMap_v::LSN;
use crate::marshalling::Marshalling_v::Parsedview;
use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::{Message, Value};
use crate::spec::AsyncDisk_t::{DiskRequest, RawPage};
use crate::implementation::OverflowFiction_v::convert_overflow_into_liveness_failure;
use crate::implementation::CachedJournal_v::{CachedJournal, JournalRoot, JournalSnapshot, JournalStatus, acyclic_reads, all_addrs_have_complete_lsn_ranges, all_addrs_have_finite_lsn_sets, au_page_bounds_observe_addr, build_au_page_bounds_from_reads_au_walk_depth, build_lsn_addr_index_from_reads, build_lsn_addr_index_from_reads_extend_next_ptr, build_lsn_addr_index_from_reads_key_range, build_lsn_addr_index_from_reads_next_ptr, build_lsn_addr_index_from_reads_next_ptr_after_insert, build_lsn_addr_index_from_reads_next_ptr_not_in_reads, build_lsn_addr_index_from_reads_to_au_index_au_walk_depth, build_lsn_addr_index_from_reads_values_bounded_by_au_page_bounds, build_lsn_addr_index_from_reads_values_bounded_by_page_bounds, build_lsn_addr_index_from_reads_values_in_reads, build_lsn_au_index_from_reads_au_walk_depth, freeze_reads_for_seq_end, largest_lsn_plus_one_au, lsn_addr_index_to_au_index, lsn_addr_index_to_au_index_append_record, lsn_index_domain_exact, maxmax_au, page_walk_reads_cover_addr_build_matches_full_by_value, page_walk_reads_cover_to_au_walk_reads_cover, page_walk_reads_prefix, page_walk_reads_prefix_complete, page_walk_reads_prefix_extend};
use crate::disk::GenericDisk_v::{Address, AU, IAddress, Pointer, Ranking, page_count, to_aus, to_aus_domain};
use crate::implementation::AllocationBranchStackRefinement_v::{append_put_message, append_puts};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::AJournal;
use crate::implementation::JournalTypes_v::ILsn;
use crate::implementation::JournalTypes_v::{journal_marshall_labels, raw_page_to_record, to_journal_records};
use crate::allocation_layer::AllocationJournal_v::{
    AUPageBounds, LsnAUIndex, lsn_au_index_append_record,
    lsn_au_index_append_record_ensures, lsn_au_index_discard_up_to,
};
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::allocation_layer::LikesJournal_v::{LsnAddrIndex, discard_old_ptr_by_index, largest_lsn_plus_one, lsn_addr_index_append_record, lsn_addr_index_append_record_ensures, lsn_addr_index_discard_up_to, singleton_index, lsn_disjoint};
use crate::implementation::Cache_v::{Cache, Entry};
use crate::implementation::FracCacheImpl_v::{
    FetchErrorCode, FracCacheImpl, MutHandle, ReserveWriteResult, WritebackHandle,
    WritebackAcquireResult, cache_load_label, cache_write_label, PAGE_SIZE_BYTES
};
use crate::implementation::ILsnAddrIndex_v::ILsnAddrIndex;
use crate::implementation::AuPoolImpl_v::{iau_vec_set, AuAllocation, AuPoolImpl};
// use crate::implementation::PageAllocator_v::PageAllocator;
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::marshalling::Slice_v::Slice;
use crate::spec::ImplDisk_t::{IAU, IPage};
use crate::marshalling::IJournalRecordFormat_v::{IJournalHeader, IJournalRecord, IJournalRecordFormat};
use crate::marshalling::Marshalling_v::Marshal;
use crate::marshalling::UniformSized_v::UniformSized;
use crate::journal::LinkedJournal_v;
use crate::journal::LinkedJournal_v::JournalRecord;

verus!{

pub const JOURNAL_FREE_AU_THRESHOLD: IAU = 5;

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

fn please_panic()
    ensures false
{
    convert_overflow_into_liveness_failure();
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

    pub open spec fn geometry_bounded(self, total_aus: IAU) -> bool {
        self.snapshot@.root is Some ==> {
            &&& self.snapshot@.root.unwrap().freshest_rec.au < total_aus as nat
            &&& self.snapshot@.root.unwrap().first < total_aus as nat
        }
    }

    pub exec fn empty_at(boundary_lsn: ILsn) -> (out: Self)
        ensures
            out.wf(),
            out.seq_start() == boundary_lsn,
            out.seq_end == boundary_lsn,
            out.snapshot@ == (crate::implementation::CachedJournal_v::JournalSnapshot{
                boundary_lsn: boundary_lsn as nat,
                root: None,
            }),
    {
        Self {
            snapshot: IJournalSnapshot {
                boundary_lsn,
                freshest_rec: None,
                first: 0,
            },
            seq_end: boundary_lsn,
        }
    }
}

pub struct IJournalStatus {
    pub lsn_addr_index: ILsnAddrIndex,
    pub unmarshalled_tail: Vec<KeyedMessage>,
    pub au_page_bounds: Ghost<AUPageBounds>,
    pub clean_watermark_au_page_bounds: Ghost<AUPageBounds>,
    pub clean_watermark_lsn: ILsn,
    pub recovery_reads: Ghost<Map<Address, RawPage>>,
}

impl IJournalStatus {
    spec fn wf(&self) -> bool
    {
        &&& self.lsn_addr_index.wf()
        &&& forall |addr: Address| #[trigger] self.lsn_addr_index@.values().contains(addr) ==> {
            &&& self.au_page_bounds@.contains_key(addr.au)
            &&& addr.page <= self.au_page_bounds@[addr.au]
        }
        &&& self.clean_watermark_au_page_bounds@.dom() <= self.au_page_bounds@.dom()
        &&& forall |au: AU| #[trigger] self.clean_watermark_au_page_bounds@.contains_key(au) ==>
            self.clean_watermark_au_page_bounds@[au] <= self.au_page_bounds@[au]
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
            clean_watermark_au_page_bounds: self.clean_watermark_au_page_bounds@,
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
    InvalidRecord{},
}

pub enum UnifiedRecoverIndexResult {
    CacheLoad{slot_handle: MutHandle, addr: IAddress},
    IndexComplete{reads: Ghost<Map<Address, RawPage>>, discovered_aus: Vec<IAU>},
    IndexProgress{},
}

pub enum UnifiedRecoverMapResult {
    FetchSuccess{
        reads: Ghost<Map<Address, RawPage>>,
        addr: Ghost<Address>,
        record: IJournalRecord,
        keys: Vec<Key>,
        msgs: Vec<Message>,
    },
    NotInCache{},
    InvalidRecord{},
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
    // pub journal_alloc: PageAllocator,
    pub journal_alloc: MiniAllocatorImpl,
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

pub open spec fn cache_agrees_with_raw_disk_on_domain(cache: Cache::State, disk: Map<Address, RawPage>) -> bool
{
    forall |addr, data| #[trigger] cache.valid_read(addr, data)
        && disk.contains_key(addr)
        ==> disk[addr] == data
}

pub open spec fn journal_disk_inv(disk: LinkedJournal_v::DiskView, root: Pointer) -> bool
{
    &&& disk.acyclic()
    &&& disk.decodable(root)
    &&& disk.boundary_lsn < disk.entries[root.unwrap()].message_seq.seq_end
}

pub open spec fn journal_disk_load_index_inv(
    disk: LinkedJournal_v::DiskView,
    root: Pointer,
    first: AU,
) -> bool
{
    &&& journal_disk_inv(disk, root)
    &&& disk.path_decodable(root)
    &&& disk.path_build_tight(root).pointer_is_upstream(root, first)
}

proof fn lsn_addr_index_to_au_index_values_match(index: LsnAddrIndex)
    ensures
        lsn_addr_index_to_au_index(index).values() =~= to_aus(index.values()),
{
    let au_index = lsn_addr_index_to_au_index(index);
    assert forall |au: AU| #[trigger] au_index.values().contains(au)
        implies to_aus(index.values()).contains(au) by {
        let lsn = choose |lsn: LSN| #[trigger] au_index.contains_key(lsn)
            && au_index[lsn] == au;
        assert(index.contains_key(lsn));
        let addr = index[lsn];
        assert(index.values().contains(addr));
        assert(addr.au == au);
        to_aus_domain(index.values());
        assert(to_aus(index.values()).contains(au));
    }
    assert forall |au: AU| #[trigger] to_aus(index.values()).contains(au)
        implies au_index.values().contains(au) by {
        let addr = choose |addr: Address| #[trigger] index.values().contains(addr)
            && addr.au == au;
        let lsn = choose |lsn: LSN| #[trigger] index.contains_key(lsn)
            && index[lsn] == addr;
        assert(au_index.contains_key(lsn));
        assert(au_index[lsn] == au);
        assert(au_index.values().contains(au));
    }
}

proof fn lsn_addr_index_to_au_index_restrict_values_match(index: LsnAddrIndex, range: Set<LSN>)
    ensures
        lsn_addr_index_to_au_index(index).restrict(range).values()
            =~= to_aus(index.restrict(range).values()),
{
    let au_index = lsn_addr_index_to_au_index(index);
    let restricted_au_index = au_index.restrict(range);
    let restricted_addr_index = index.restrict(range);
    assert forall |au: AU| #[trigger] restricted_au_index.values().contains(au)
        implies to_aus(restricted_addr_index.values()).contains(au) by {
        let lsn = choose |lsn: LSN| #[trigger] restricted_au_index.contains_key(lsn)
            && restricted_au_index[lsn] == au;
        assert(range.contains(lsn));
        assert(au_index.contains_key(lsn));
        assert(index.contains_key(lsn));
        assert(au_index[lsn] == index[lsn].au);
        let addr = index[lsn];
        assert(restricted_addr_index.contains_key(lsn));
        assert(restricted_addr_index[lsn] == addr);
        assert(restricted_addr_index.values().contains(addr));
        assert(addr.au == au);
        to_aus_domain(restricted_addr_index.values());
    }
    assert forall |au: AU| #[trigger] to_aus(restricted_addr_index.values()).contains(au)
        implies restricted_au_index.values().contains(au) by {
        let addr = choose |addr: Address| #[trigger] restricted_addr_index.values().contains(addr)
            && addr.au == au;
        let lsn = choose |lsn: LSN| #[trigger] restricted_addr_index.contains_key(lsn)
            && restricted_addr_index[lsn] == addr;
        assert(range.contains(lsn));
        assert(index.contains_key(lsn));
        assert(index[lsn] == addr);
        assert(au_index.contains_key(lsn));
        assert(au_index[lsn] == addr.au);
        assert(restricted_au_index.contains_key(lsn));
        assert(restricted_au_index[lsn] == au);
    }
}

proof fn lsn_au_index_has_max_below(
    index: LsnAUIndex,
    au: AU,
    lo: LSN,
    hi: LSN,
    witness: LSN,
)
    requires
        lo <= witness < hi,
        index.contains_key(witness),
        index[witness] == au,
        forall |lsn: LSN| #[trigger] index.contains_key(lsn) && index[lsn] == au
            ==> lo <= lsn < hi,
    ensures
        exists |max_lsn: LSN| maxmax_au(index, au, max_lsn),
    decreases hi - lo,
{
    let last = (hi - 1) as nat;
    if index.contains_key(last) && index[last] == au {
        assert(maxmax_au(index, au, last)) by {
            assert(index.contains_pair(last, au));
            assert forall |other_lsn: LSN| #[trigger] index.contains_key(other_lsn)
                && index[other_lsn] == au
                implies other_lsn <= last by {
                assert(other_lsn < hi);
                if !(other_lsn <= last) {
                    assert(last < other_lsn);
                    assert(hi <= other_lsn);
                    assert(false);
                }
            }
        }
    } else {
        assert(witness < last) by {
            if !(witness < last) {
                assert(last <= witness);
                assert(witness < hi);
                assert(witness == last);
                assert(index.contains_key(last));
                assert(index[last] == au);
                assert(false);
            }
        }
        assert forall |lsn: LSN| #[trigger] index.contains_key(lsn) && index[lsn] == au
            implies lo <= lsn < last by {
            assert(lo <= lsn < hi);
            if !(lsn < last) {
                assert(last <= lsn);
                assert(lsn < hi);
                assert(lsn == last);
                assert(index.contains_key(last));
                assert(index[last] == au);
                assert(false);
            }
        }
        lsn_au_index_has_max_below(index, au, lo, last, witness);
    }
}

proof fn lsn_au_index_largest_lsn_plus_one_after_witness(
    index: LsnAUIndex,
    au: AU,
    lo: LSN,
    hi: LSN,
    witness: LSN,
)
    requires
        lo <= witness < hi,
        index.contains_key(witness),
        index[witness] == au,
        forall |lsn: LSN| #[trigger] index.contains_key(lsn) && index[lsn] == au
            ==> lo <= lsn < hi,
    ensures
        witness < largest_lsn_plus_one_au(index, au),
{
    lsn_au_index_has_max_below(index, au, lo, hi, witness);
    assert(index.contains_pair(witness, au));
    assert(index.contains_value(au));
    let max_lsn = choose |lsn: LSN| maxmax_au(index, au, lsn);
    assert(maxmax_au(index, au, max_lsn));
    assert(witness <= max_lsn);
}

proof fn lsn_addr_index_to_au_index_discard(
    index: LsnAddrIndex,
    bdy: LSN,
)
    ensures
        lsn_addr_index_to_au_index(lsn_addr_index_discard_up_to(index, bdy))
            =~= lsn_au_index_discard_up_to(lsn_addr_index_to_au_index(index), bdy),
{
    crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to_ensures(index, bdy);
    crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to_ensures(
        lsn_addr_index_to_au_index(index),
        bdy,
    );
    assert_maps_equal!(
        lsn_addr_index_to_au_index(lsn_addr_index_discard_up_to(index, bdy)),
        lsn_au_index_discard_up_to(lsn_addr_index_to_au_index(index), bdy),
        lsn => {
            let addr_discard = lsn_addr_index_discard_up_to(index, bdy);
            let au_discard = lsn_au_index_discard_up_to(lsn_addr_index_to_au_index(index), bdy);
            if addr_discard.contains_key(lsn) {
                assert(index.contains_key(lsn));
                assert(bdy <= lsn);
                assert(lsn_addr_index_to_au_index(index).contains_key(lsn));
                assert(au_discard.contains_key(lsn));
                assert(addr_discard[lsn] == index[lsn]);
                assert(au_discard[lsn] == lsn_addr_index_to_au_index(index)[lsn]);
                assert(lsn_addr_index_to_au_index(index)[lsn] == index[lsn].au);
            }
            if au_discard.contains_key(lsn) {
                assert(lsn_addr_index_to_au_index(index).contains_key(lsn));
                assert(index.contains_key(lsn));
                assert(bdy <= lsn);
                assert(addr_discard.contains_key(lsn));
            }
        }
    );
}

proof fn append_preserves_addr_bounds(
    old_index: LsnAddrIndex,
    old_bounds: AUPageBounds,
    start: LSN,
    end: LSN,
    addr: Address,
)
    requires
        start < end,
        forall |a: Address| #[trigger] old_index.values().contains(a) ==> {
            &&& old_bounds.contains_key(a.au)
            &&& a.page <= old_bounds[a.au]
        },
    ensures
        forall |a: Address| #[trigger] lsn_addr_index_append_record(
            old_index,
            start,
            end,
            addr,
        ).values().contains(a) ==> {
            &&& au_page_bounds_observe_addr(old_bounds, addr).contains_key(a.au)
            &&& a.page <= au_page_bounds_observe_addr(old_bounds, addr)[a.au]
        },
{
    let update = singleton_index(start, end, addr);
    let new_index = lsn_addr_index_append_record(old_index, start, end, addr);
    let new_bounds = au_page_bounds_observe_addr(old_bounds, addr);
    reveal(lsn_addr_index_append_record);
    assert forall |a: Address| #[trigger] new_index.values().contains(a)
        implies new_bounds.contains_key(a.au) && a.page <= new_bounds[a.au] by {
        let lsn = choose |lsn: LSN| #[trigger] new_index.contains_key(lsn) && new_index[lsn] == a;
        if update.contains_key(lsn) {
            assert(update[lsn] == addr);
            assert(new_index[lsn] == addr);
            assert(a == addr);
            assert(new_bounds.contains_key(a.au));
            if old_bounds.contains_key(addr.au) && addr.page <= old_bounds[addr.au] {
                assert(new_bounds[a.au] == old_bounds[addr.au]);
            } else {
                assert(new_bounds[a.au] == addr.page);
            }
        } else {
            assert(old_index.contains_key(lsn));
            assert(old_index[lsn] == a);
            assert(old_index.values().contains(a));
            assert(old_bounds.contains_key(a.au));
            assert(a.page <= old_bounds[a.au]);
            assert(new_bounds.contains_key(a.au));
            if a.au == addr.au {
                if old_bounds.contains_key(addr.au) && addr.page <= old_bounds[addr.au] {
                    assert(new_bounds[a.au] == old_bounds[a.au]);
                } else {
                    assert(new_bounds[a.au] == addr.page);
                    assert(old_bounds[a.au] < addr.page);
                    assert(a.page <= addr.page);
                }
            } else {
                assert(new_bounds[a.au] == old_bounds[a.au]);
            }
        }
    }
}

proof fn discard_preserves_addr_bounds(
    old_index: LsnAddrIndex,
    old_bounds: AUPageBounds,
    bdy: LSN,
)
    requires
        forall |a: Address| #[trigger] old_index.values().contains(a) ==> {
            &&& old_bounds.contains_key(a.au)
            &&& a.page <= old_bounds[a.au]
        },
    ensures
        forall |a: Address| #[trigger] lsn_addr_index_discard_up_to(
            old_index,
            bdy,
        ).values().contains(a) ==> {
            let new_aus = lsn_au_index_discard_up_to(lsn_addr_index_to_au_index(old_index), bdy).values();
            let new_bounds = old_bounds.restrict(new_aus);
            &&& new_bounds.contains_key(a.au)
            &&& a.page <= new_bounds[a.au]
        },
{
    lsn_addr_index_to_au_index_discard(old_index, bdy);
    lsn_addr_index_to_au_index_values_match(lsn_addr_index_discard_up_to(old_index, bdy));
    assert forall |a: Address| #[trigger] lsn_addr_index_discard_up_to(old_index, bdy).values().contains(a)
        implies ({
            let new_aus = lsn_au_index_discard_up_to(lsn_addr_index_to_au_index(old_index), bdy).values();
            let new_bounds = old_bounds.restrict(new_aus);
            &&& new_bounds.contains_key(a.au)
            &&& a.page <= new_bounds[a.au]
        }) by {
        let new_index = lsn_addr_index_discard_up_to(old_index, bdy);
        let new_au_index = lsn_au_index_discard_up_to(lsn_addr_index_to_au_index(old_index), bdy);
        let new_bounds = old_bounds.restrict(new_au_index.values());
        crate::allocation_layer::LikesJournal_v::lsn_addr_index_discard_up_to_ensures(old_index, bdy);
        assert(new_index <= old_index);
        let lsn = choose |lsn: LSN| #[trigger] new_index.contains_key(lsn) && new_index[lsn] == a;
        assert(old_index.contains_key(lsn));
        assert(old_index[lsn] == a);
        assert(old_index.values().contains(a));
        assert(old_bounds.contains_key(a.au));
        assert(a.page <= old_bounds[a.au]);
        assert(lsn_addr_index_to_au_index(new_index) =~= new_au_index);
        assert(lsn_addr_index_to_au_index(new_index).values().contains(a.au)) by {
            assert(new_index.values().contains(a));
            lsn_addr_index_to_au_index_values_match(new_index);
            to_aus_domain(new_index.values());
        }
        assert(new_au_index.values().contains(a.au));
        assert(new_bounds.contains_key(a.au));
        assert(new_bounds[a.au] == old_bounds[a.au]);
    }
}

proof fn journal_record_suffix_is_append_puts(
    record: IJournalRecord,
    start_lsn: LSN,
    start_idx: nat,
    keys: Seq<Key>,
    msgs: Seq<Message>,
)
    requires
        record.parsedv().view().message_seq.seq_start <= start_lsn,
        start_lsn <= record.parsedv().view().message_seq.seq_end,
        start_idx == start_lsn - record.parsedv().view().message_seq.seq_start,
        start_idx <= record.messages@.len(),
        keys.len() == msgs.len(),
        keys.len() == record.messages@.len() - start_idx,
        forall |j: int| 0 <= j < keys.len() ==> {
            &&& keys[j] == record.messages@[start_idx as int + j].key
            &&& msgs[j] == record.messages@[start_idx as int + j].message
        },
    ensures
        record.parsedv().view().message_seq.maybe_discard_old(start_lsn)
            == append_puts(start_lsn, keys, msgs),
{
    let rec = record.parsedv().view();
    let lhs = rec.message_seq.maybe_discard_old(start_lsn);
    let rhs = append_puts(start_lsn, keys, msgs);
    assert(rec.message_seq.seq_start == record.header.start_lsn as nat);
    assert(rec.message_seq.seq_end == record.header.start_lsn as nat + record.messages@.len());
    assert(lhs.seq_start == start_lsn);
    assert(lhs.seq_end == rec.message_seq.seq_end);
    assert(rhs.seq_start == start_lsn);
    assert(rhs.seq_end == start_lsn + keys.len());
    assert(start_lsn + keys.len() == rec.message_seq.seq_end);

    assert(lhs.msgs =~= rhs.msgs) by {
        assert forall |lsn: LSN| #[trigger] lhs.msgs.contains_key(lsn)
            <==> rhs.msgs.contains_key(lsn) by {
            assert(lhs.msgs.contains_key(lsn) <==> lhs.contains(lsn));
            assert(rhs.msgs.contains_key(lsn) <==> rhs.contains(lsn));
        }
        assert forall |lsn: LSN| #[trigger] lhs.msgs.contains_key(lsn)
            implies lhs.msgs[lsn] == rhs.msgs[lsn] by {
            assert(lhs.contains(lsn));
            let j = (lsn - start_lsn) as int;
            let rec_idx = start_idx as int + j;
            assert(0 <= j < keys.len());
            assert(rec_idx == (lsn - rec.message_seq.seq_start) as int);
            assert(0 <= rec_idx < record.messages@.len());
            assert(lhs.msgs[lsn] == rec.message_seq.msgs[lsn]);
            assert(rec.message_seq.msgs[lsn] == record.messages@[rec_idx]);
            assert(rhs.msgs[lsn] == KeyedMessage{
                key: keys[j],
                message: append_put_message(msgs[j]),
            });
            assert(append_put_message(msgs[j]) == msgs[j]);
            assert(keys[j] == record.messages@[rec_idx].key);
            assert(msgs[j] == record.messages@[rec_idx].message);
        }
    }
    assert(lhs.ext_equal(rhs));
    MsgHistory::ext_equal_is_equality();
}

impl IJournalRecord {
    exec fn seq_end(&self) -> (out: ILsn)
        requires self.wf()
        ensures out@ == self.parsedv().header.start_lsn + self.parsedv().messages.len()
    {
        if u64::MAX - self.header.start_lsn < self.messages.len() as u64 {
            convert_overflow_into_liveness_failure();
        }
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

    pub closed spec fn basic_wf(&self) -> bool {
        &&& self.format_ok()
        &&& self.journal_alloc.wf()
        &&& match self.status {
            None => { self.index_builder is Some },
            Some(status) => {
                &&& status.wf()
                &&& self.snapshot.boundary_lsn == status.lsn_addr_index.seq_start()
                &&& self.snapshot.boundary_lsn <= status.clean_watermark_lsn <= status.lsn_addr_index.seq_end()
            }
        }
    }

    pub closed spec fn wf(&self) -> bool {
        &&& self.basic_wf()
        &&& match self.status {
            None => true,
            Some(status) => {
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

    pub open spec fn allocator_index_aligned(&self) -> bool
    {
        self@.status is Some ==> self.journal_alloc.i().allocated_aus()
            <= self@.status.unwrap().lsn_au_index.values()
    }

    pub open spec fn index_aus_bounded(&self, total_aus: IAU) -> bool
    {
        self@.status is Some ==> forall |au: AU|
            #[trigger] self@.status.unwrap().lsn_au_index.values().contains(au)
            ==> au < total_aus as nat
    }

    pub open spec fn ready_wf(&self, total_aus: IAU) -> bool
    {
        &&& self.wf()
        &&& self.index_ready()
        &&& self.journal_alloc.bounded(total_aus)
        &&& MiniAllocatorImpl::allocators_unique(self.journal_alloc.allocators@)
        &&& self.allocator_index_aligned()
        &&& self.index_aus_bounded(total_aus)
    }

    pub open spec fn owned_aus(&self) -> Set<AU>
    {
        MiniAllocatorImpl::allocators_au_set(self.journal_alloc.allocators@)
    }

    pub closed spec fn marshall_next_addr_root_ok(&self, addr: Address) -> bool {
        &&& self.journal_alloc.i().curr is None ==> {
            &&& self.journal_alloc.i().allocs.contains_key(addr.au)
            &&& self.journal_alloc.i().allocs[addr.au].all_pages_free()
            &&& addr.page == 0
        }
        &&& self.journal_alloc.i().curr is Some
            && self@.snapshot.freshest_rec() is Some
            ==> addr == self@.snapshot.freshest_rec().unwrap().next()
    }


    pub proof fn wf_implies_basic_wf(&self)
        requires
            self.wf(),
        ensures
            self.basic_wf(),
            self.journal_alloc.wf(),
    {
    }

    pub closed spec fn seq_start(&self) -> LSN {
        self.snapshot.boundary_lsn as nat
    }

    pub exec fn exec_seq_start(&self) -> (out: u64)
    ensures out == self.seq_start()
    {
        self.snapshot.boundary_lsn
    }

    pub exec fn indexed_aus(&self) -> (out: Vec<IAU>)
        requires
            self.wf(),
            self.index_ready(),
        ensures
            iau_vec_set(out@) =~= self@.status.unwrap().lsn_au_index.values(),
    {
        let status = self.status.as_ref().unwrap();
        let out = status.lsn_addr_index.au_vec();
        proof {
            lsn_addr_index_to_au_index_values_match(
                status.lsn_addr_index@,
            );
            assert(self@.status.unwrap().lsn_au_index
                == lsn_addr_index_to_au_index(
                    status.lsn_addr_index@,
                ));
        }
        out
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

    pub open spec fn snapshot_geometry_bounded(&self, total_aus: IAU) -> bool
    {
        self@.snapshot.root is Some ==> {
            &&& self@.snapshot.root.unwrap().freshest_rec.au < total_aus as nat
            &&& self@.snapshot.root.unwrap().first < total_aus as nat
        }
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
        out.basic_wf(),
        out.wf(),
        !out.index_ready(),
        out@.snapshot == snapshot@,
        !out.journal_alloc.allocation_ready(),
        out.journal_alloc.i() == MiniAllocator::empty(),
        out.journal_alloc.allocators@.len() == 0,
        MiniAllocatorImpl::allocators_unique(out.journal_alloc.allocators@),
        MiniAllocatorImpl::allocators_au_set(out.journal_alloc.allocators@) =~= Set::<AU>::empty(),
    {
        // Old bootstrap behavior pre-owned one AU immediately:
        //
        // let start_page = match snapshot.freshest_rec {
        //     Some(ptr) => {
        //         if ptr.page == u32::MAX {
        //             convert_overflow_into_liveness_failure();
        //         }
        //         ptr.page + 1
        //     }
        //     None => 0,
        // };
        // journal_alloc: MiniAllocatorImpl::new(alloc_au, start_page, JOURNAL_FREE_AU_THRESHOLD),
        let _bootstrap_au = alloc_au;
        Self{
            snapshot,
            index_builder: Some(IndexBuilder{
                next_head: snapshot,
            }),
            status: None,
            fmt: IJournalRecordFormat::new(),
            journal_alloc: MiniAllocatorImpl::empty(JOURNAL_FREE_AU_THRESHOLD),
        }
    }

    pub exec fn recover_empty_index(&mut self) -> (reads: Ghost<Map<Address, RawPage>>)
    requires
        old(self).basic_wf(),
        !old(self).index_ready(),
        old(self).freshest_rec() is None,
    ensures
        self.basic_wf(),
        self.wf(),
        self@.wf(),
        self.journal_alloc.i() == old(self).journal_alloc.i(),
        self.seq_start() == old(self).seq_start(),
        self.index_ready(),
        self.no_unmarshalled_entries(),
        self.seq_start() <= self.seq_end(),
        reads@ == Map::<Address, RawPage>::empty(),
        CachedJournal::State::load_index(
            old(self)@,
            self@,
            CachedJournal::Label::LoadIndex{
                reads: to_journal_records(reads@),
                discovered_aus: Set::<AU>::empty(),
            },
            0,
            0,
        ),
        CachedJournal::State::next(
            old(self)@,
            self@,
            CachedJournal::Label::LoadIndex{
                reads: to_journal_records(reads@),
                discovered_aus: Set::<AU>::empty(),
            },
        ),
    {
        let ghost pre = *self;
        let bdy = self.snapshot.boundary_lsn;
        let index = ILsnAddrIndex::new(bdy);
        self.index_builder = None;
        self.status = Some(IJournalStatus{
            lsn_addr_index: index,
            unmarshalled_tail: Vec::new(),
            au_page_bounds: Ghost(Map::empty()),
            clean_watermark_au_page_bounds: Ghost(Map::empty()),
            clean_watermark_lsn: bdy,
            recovery_reads: Ghost(Map::empty()),
        });
        let ghost reads_map = Map::<Address, RawPage>::empty();
        proof {
            let journal_reads = to_journal_records(reads_map);
            let discovered_aus = Set::<AU>::empty();
            let lbl = CachedJournal::Label::LoadIndex{
                reads: journal_reads,
                discovered_aus,
            };
            assert(journal_reads =~= Map::<Address, JournalRecord>::empty()) by {
                assert_maps_equal!(journal_reads, Map::<Address, JournalRecord>::empty(), addr => {
                });
            };
            assert(LinkedJournal_v::DiskView{
                boundary_lsn: self@.snapshot.boundary_lsn,
                entries: journal_reads,
            }.valid_ranking(map!{}));
            assert(acyclic_reads(self@.snapshot.boundary_lsn, journal_reads));
            assert(self.status.unwrap().lsn_addr_index@ =~= Map::<LSN, Address>::empty());
            assert(lsn_addr_index_to_au_index(self.status.unwrap().lsn_addr_index@)
                =~= Map::<LSN, AU>::empty()) by {
                assert_maps_equal!(
                    lsn_addr_index_to_au_index(self.status.unwrap().lsn_addr_index@),
                    Map::<LSN, AU>::empty(),
                    lsn => {
                    }
                );
            };
            assert(build_lsn_au_index_from_reads_au_walk_depth(
                journal_reads,
                pre@.snapshot.boundary_lsn,
                pre@.snapshot.freshest_rec(),
                pre@.snapshot.first(),
                0,
                0,
            ) =~= Map::<LSN, AU>::empty());
            assert(build_au_page_bounds_from_reads_au_walk_depth(
                journal_reads,
                pre@.snapshot.boundary_lsn,
                pre@.snapshot.freshest_rec(),
                pre@.snapshot.first(),
                0,
                0,
            ) =~= Map::<AU, nat>::empty());
            assert(discovered_aus == build_lsn_au_index_from_reads_au_walk_depth(
                journal_reads,
                pre@.snapshot.boundary_lsn,
                pre@.snapshot.freshest_rec(),
                pre@.snapshot.first(),
                0,
                0,
            ).values());
            let post_status = self.status.unwrap();
            let expected_tail = MsgHistory::empty_history_at(pre@.snapshot.boundary_lsn);
            reveal(IJournalStatus::tail_as_history);
            assert(post_status.tail_as_history().ext_equal(expected_tail)) by {
                assert(post_status.tail_as_history().seq_start == expected_tail.seq_start);
                assert(post_status.tail_as_history().seq_end == expected_tail.seq_end);
                assert_maps_equal!(
                    post_status.tail_as_history().msgs,
                    expected_tail.msgs,
                    lsn => {
                    }
                );
            }
            MsgHistory::ext_equal_is_equality();
            assert(post_status.tail_as_history() == expected_tail);
            assert(post_status@ == JournalStatus{
                lsn_au_index: build_lsn_au_index_from_reads_au_walk_depth(
                    journal_reads,
                    pre@.snapshot.boundary_lsn,
                    pre@.snapshot.freshest_rec(),
                    pre@.snapshot.first(),
                    0,
                    0,
                ),
                au_page_bounds: build_au_page_bounds_from_reads_au_walk_depth(
                    journal_reads,
                    pre@.snapshot.boundary_lsn,
                    pre@.snapshot.freshest_rec(),
                    pre@.snapshot.first(),
                    0,
                    0,
                ),
                clean_watermark_au_page_bounds: build_au_page_bounds_from_reads_au_walk_depth(
                    journal_reads,
                    pre@.snapshot.boundary_lsn,
                    pre@.snapshot.freshest_rec(),
                    pre@.snapshot.first(),
                    0,
                    0,
                ),
                unmarshalled_tail: MsgHistory::empty_history_at(pre@.snapshot.boundary_lsn),
                clean_watermark_lsn: pre@.snapshot.boundary_lsn,
            });
            assert(CachedJournal::State::load_index(pre@, self@, lbl, 0, 0)) by {
                reveal(CachedJournal::State::load_index);
            }
            assert(CachedJournal::State::next_by(
                pre@,
                self@,
                lbl,
                CachedJournal::Step::load_index(0, 0),
            )) by {
                reveal(CachedJournal::State::next_by);
            }
            reveal(CachedJournal::State::next);
            assert(CachedJournal::State::next(pre@, self@, lbl));
        }
        Ghost(reads_map)
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
            RecoverMapResult::InvalidRecord{} => old(cache)@ == cache@,
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
        proof {
            let model_index = self.status.unwrap().lsn_addr_index@;
            self.status.unwrap().lsn_addr_index.view_domain();
            self.status.unwrap().lsn_addr_index.seq_start_le_seq_end();
            self.seq_start_le_seq_end();
            let ghost lai_seq_end = self.status.unwrap().lsn_addr_index.seq_end() as nat;
            assert(lai_seq_end == self.seq_end());
            assert(model_index.contains_key(start_lsn as nat));
            assert(addr@ == model_index[start_lsn as nat]);
            assert(model_index.values().contains(addr@));
        }
        match cache.fetch(&addr, false) {
            FetchErrorCode::Success{slot_handle} => {
                let all_slice = Slice::all(&slot_handle.rec);
                assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                let parsable = self.fmt.exec_parsable(&all_slice, &slot_handle.rec);
                if !parsable {
                    let ghost fetched_slot = slot_handle.idx;
                    let ghost fetched_data = slot_handle.rec@;
                    let ghost cache_after_fetch = cache@;
                    cache.handle_release(&addr, slot_handle);
                    proof {
                        assert(cache_pre.entries == cache_after_fetch.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: addr@, data: fetched_data},
                        ));
                        assert(cache@.entries == cache_after_fetch.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: addr@, data: fetched_data},
                        ));
                        assert(cache@.entries == cache_pre.entries);
                        assert(cache@.lookup_map == cache_pre.lookup_map);
                        assert(cache@.status_map == cache_pre.status_map);
                        assert(cache@ == cache_pre);
                    }
                    return RecoverMapResult::InvalidRecord{};
                }
                proof {
                    assert(parsable);
                    assert(self.fmt.parsable(all_slice@.i(slot_handle.rec@)));
                    assert(old(cache)@.valid_read(addr@, slot_handle.rec@));
                    assert(self.fmt.parsable(slot_handle.rec@));
                    assert(self.fmt.parsable(all_slice@.i(slot_handle.rec@)));
                }
                let i_journal_record = self.fmt.exec_parse(&all_slice, &slot_handle.rec);

                let ghost fetched_slot = slot_handle.idx;
                let ghost fetched_data = slot_handle.rec@;
                let record_end = i_journal_record.seq_end();
                let cropped_start = if i_journal_record.header.start_lsn < self.snapshot.boundary_lsn {
                    self.snapshot.boundary_lsn
                } else {
                    i_journal_record.header.start_lsn
                };
                if cropped_start > start_lsn || start_lsn >= record_end || record_end > seq_end {
                    let ghost cache_after_fetch = cache@;
                    cache.handle_release(&addr, slot_handle);
                    proof {
                        assert(cache_pre.entries == cache_after_fetch.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: addr@, data: fetched_data},
                        ));
                        assert(cache@.entries == cache_after_fetch.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: addr@, data: fetched_data},
                        ));
                        assert(cache@.entries == cache_pre.entries);
                        assert(cache@.lookup_map == cache_pre.lookup_map);
                        assert(cache@.status_map == cache_pre.status_map);
                        assert(cache@ == cache_pre);
                    }
                    return RecoverMapResult::InvalidRecord{};
                }
                proof {
                    assert(self.status.unwrap().lsn_addr_index.seq_start() <= cropped_start);
                    assert(cropped_start < self.status.unwrap().lsn_addr_index.seq_end());
                }
                let (cropped_addr, _) = index.lookup_lsn_with_segment_end(cropped_start);
                if cropped_addr.au != addr.au {
                    let ghost cache_after_fetch = cache@;
                    cache.handle_release(&addr, slot_handle);
                    proof {
                        assert(cache_pre.entries == cache_after_fetch.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: addr@, data: fetched_data},
                        ));
                        assert(cache@.entries == cache_after_fetch.entries.insert(
                            fetched_slot,
                            Entry::Filled{addr: addr@, data: fetched_data},
                        ));
                        assert(cache@.entries == cache_pre.entries);
                        assert(cache@.lookup_map == cache_pre.lookup_map);
                        assert(cache@.status_map == cache_pre.status_map);
                        assert(cache@ == cache_pre);
                    }
                    return RecoverMapResult::InvalidRecord{};
                }
                let ghost reads = map!{addr@ => slot_handle.rec@};
                let ghost lbls = map_recovery_labels(self.seq_start(), reads, addr@);

                proof {
                    to_journal_records_entry_from_exec_parse(self.fmt, reads, addr@, i_journal_record);
                    assert(to_journal_records(reads)[addr@] == i_journal_record.parsedv().view());
                    assert(self.status.unwrap().lsn_addr_index@.contains_key(start_lsn as nat));
                    assert(addr@ == self.status.unwrap().lsn_addr_index@[start_lsn as nat]);
                    assert(self.status.unwrap().lsn_addr_index@.values().contains(addr@));
                    assert(raw_page_to_record(slot_handle.rec@).message_seq.maybe_discard_old(
                        self@.snapshot.boundary_lsn,
                    ).seq_start == cropped_start as nat);
                    assert(raw_page_to_record(slot_handle.rec@).message_seq.maybe_discard_old(
                        self@.snapshot.boundary_lsn,
                    ).seq_start <= start_lsn as nat);
                    assert((start_lsn as nat) < raw_page_to_record(slot_handle.rec@).message_seq.seq_end);
                    assert(raw_page_to_record(slot_handle.rec@).message_seq.seq_end <= self.seq_end());
                    assert(to_journal_records(reads)[addr@] == raw_page_to_record(slot_handle.rec@));
                    assert(i_journal_record.parsedv().view().message_seq.seq_start
                        == raw_page_to_record(slot_handle.rec@).message_seq.seq_start);
                    assert(i_journal_record.parsedv().view().message_seq.seq_end
                        == raw_page_to_record(slot_handle.rec@).message_seq.seq_end);
                    assert(i_journal_record.parsedv().view().message_seq.maybe_discard_old(
                        self@.snapshot.boundary_lsn,
                    ).seq_start <= start_lsn as nat);
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
                    let ghost model_index = self.status.unwrap().lsn_addr_index@;
                    assert(actual_start_lsn == cropped_start as nat);
                    assert(model_index.contains_key(actual_start_lsn));
                    assert(model_index[actual_start_lsn] == cropped_addr@);

                    assert(self@.status.unwrap().lsn_au_index
                        == lsn_addr_index_to_au_index(self.status.unwrap().lsn_addr_index@));
                    assert(self@.status.unwrap().lsn_au_index.contains_key(actual_start_lsn));
                    assert(self@.status.unwrap().lsn_au_index[actual_start_lsn] == cropped_addr@.au);
                    assert(self@.status.unwrap().lsn_au_index[actual_start_lsn] == addr@.au);
                    assert(self.status.unwrap().wf());
                    assert(self.status.unwrap().lsn_addr_index@.values().contains(addr@));
                    assert(self@.status.unwrap().au_page_bounds.contains_key(addr@.au));
                    assert(addr@.page <= self@.status.unwrap().au_page_bounds[addr@.au]);
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
            FetchErrorCode::NotPresent | FetchErrorCode::CacheFull | FetchErrorCode::Awaiting => {
                RecoverMapResult::NotInCache{}
            },
            FetchErrorCode::LoadInitiate{..} => {
                RecoverMapResult::NotInCache{}
            }
        }
    }

    // Incrementally reconstruct the index from the journal chain.
    // Keeps explicit intermediate state to avoid restarting from head on each cache interaction.
    pub exec fn recover_index_step(
        &mut self,
        cache: &mut FracCacheImpl,
        journal_raw_disk_ghost: Ghost<Map<Address, RawPage>>,
        total_aus: IAU,
    )
        -> (out: RecoverIndexResult)
    requires
        old(self).wf(),
        !old(self).index_ready(),
        old(self).snapshot_geometry_bounded(total_aus),
        old(cache).wf(),
        cache_agrees_with_raw_disk_on_domain(old(cache)@, journal_raw_disk_ghost@),
        old(self)@.snapshot.freshest_rec() is Some ==>
            journal_disk_load_index_inv(
                LinkedJournal_v::DiskView{
                    boundary_lsn: old(self)@.snapshot.boundary_lsn,
                    entries: to_journal_records(journal_raw_disk_ghost@),
                },
                old(self)@.snapshot.freshest_rec(),
                old(self)@.snapshot.first()),
    ensures ({
        &&& self.wf()
        &&& self@.wf()
        &&& self.journal_alloc.i() == old(self).journal_alloc.i()
        &&& self.seq_start() == old(self).seq_start()
        &&& self.snapshot_geometry_bounded(total_aus)
        &&& cache.wf()
        &&& cache.valid_load_handles_preserved(*old(cache))
        &&& match out {
            RecoverIndexResult::CacheLoad{slot_handle, addr} => {
                &&& self@ == old(self)@
                &&& addr@ != spec_superblock_addr()
                &&& addr@.au < total_aus as nat
                &&& !old(cache).entry_fetched(&addr)
                &&& cache.entry_fetched(&addr)
                &&& cache.valid_load_handle(&addr, slot_handle)
                &&& Cache::State::next(old(cache)@, cache@, cache_load_label(&addr))
            },
            RecoverIndexResult::IndexComplete{reads} => {
                let (cache_lbl, journal_lbl) = load_index_labels(reads@);
                &&& old(cache)@ == cache@
                &&& self.index_ready()
                &&& self.index_aus_bounded(total_aus)
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
                    // Each fetched record is checked with exec_parsable before exec_parse.
                }
                // The caller supplies cache/raw agreement on the journal raw-disk domain.

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
                        let ghost mut load_index_walk_depth: nat = 0;
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
                                cache_agrees_with_raw_disk_on_domain(cache@, journal_raw_disk),
                                self.fmt.valid(),
                                self.fmt == IJournalRecordFormat::spec_new(),
                                self.snapshot == old(self).snapshot,
                                self.status == old(self).status,
                                self.journal_alloc == old(self).journal_alloc,
                                index.seq_start() != bdy ==> curr is Some,
                                curr is Some ==> journal_disk.entries.contains_key(curr.unwrap()@),
                                to_journal_records(reads) <= journal_disk.entries,
                                curr is Some ==> (forall |a| #[trigger] reads.contains_key(a) ==> ranking[a] >= ranking[curr.unwrap()@]),
                                forall |addr| #[trigger] reads.contains_key(addr) ==> cache@.valid_read(addr, reads[addr]),
                                forall |addr| #[trigger] reads.contains_key(addr)
                                    ==> addr.au < total_aus as nat,
                                forall |addr| #[trigger] to_journal_records(reads).contains_key(addr) ==> {
                                    let next = to_journal_records(reads)[addr].cropped_prior(bdy as nat);
                                    next is None || to_journal_records(reads).contains_key(next.unwrap()) || next == iaddr_view(curr)
                                },
                                page_walk_reads_prefix(
                                    to_journal_records(reads),
                                    bdy as nat,
                                    self@.snapshot.freshest_rec(),
                                    load_index_walk_depth,
                                    iaddr_view(curr),
                                ),
                                iaddr_view(curr) == build_lsn_addr_index_from_reads_next_ptr(to_journal_records(reads), bdy as nat, self@.snapshot.freshest_rec()),
                                acyclic_reads(bdy as nat, to_journal_records(reads)),
                                !index_initialized ==> curr == self.snapshot.freshest_rec,
                                !index_initialized ==> reads.dom() =~= Set::<Address>::empty(),
                                index_initialized ==> (index.seq_start() == bdy
                                    || index.seq_start() == journal_disk.entries[curr.unwrap()@].message_seq.seq_end),
                                index_initialized && index.seq_start() == bdy ==> curr is None,
                                bdy <= index.seq_start(),
                                index_initialized ==> {
                                    &&& index.seq_end() == seq_end
                                    &&& reads.contains_key(root@)
                                    &&& index@ =~= build_lsn_addr_index_from_reads(to_journal_records(reads), bdy as nat, self@.snapshot.freshest_rec())
                                    &&& index@.values() =~= reads.dom()
                                },
                            decreases journal_disk.the_rank_of(iaddr_view(curr))
                            {
                                let ghost prev = iaddr_view(curr);
                                let addr = curr.unwrap();
                                if addr.au >= total_aus {
                                    self.index_builder = Some(builder);
                                    proof {
                                        assert(cache@ == old(cache)@);
                                        assert(self.snapshot == old(self).snapshot);
                                        assert(self.status == old(self).status);
                                        assert(self.fmt == old(self).fmt);
                                        assert(self.journal_alloc == old(self).journal_alloc);
                                        assert(self@ == old(self)@);
                                        assert(self.basic_wf());
                                        assert(self.wf());
                                    }
                                    return RecoverIndexResult::IndexProgress{};
                                }
                                if addr.au == 0 && addr.page == 0 {
                                    self.index_builder = Some(builder);
                                    proof {
                                        assert(addr@ == spec_superblock_addr());
                                        assert(cache@ == old(cache)@);
                                        assert(self.snapshot == old(self).snapshot);
                                        assert(self.status == old(self).status);
                                        assert(self.fmt == old(self).fmt);
                                        assert(self.journal_alloc == old(self).journal_alloc);
                                        assert(self@ == old(self)@);
                                        assert(self.basic_wf());
                                        assert(self.wf());
                                    }
                                    return RecoverIndexResult::IndexProgress{};
                                }
                                let ghost cache_pre_fetch = *cache;

                                match cache.fetch(&addr, true) {
                                    FetchErrorCode::Success{slot_handle} => {
                                        let ghost cache_post_fetch = *cache;
                                        let all_slice = Slice::all(&slot_handle.rec);
                                        assert( all_slice@.i(slot_handle.rec@) == slot_handle.rec@ );
                                        let parsable = self.fmt.exec_parsable(&all_slice, &slot_handle.rec);
                                        if !parsable {
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
                                                assert(cache@ == cache_pre_fetch@);
                                                assert(cache@ == old(cache)@);
                                            }
                                            self.index_builder = Some(builder);
                                            proof {
                                                assert(self.snapshot == old(self).snapshot);
                                                assert(self.status == old(self).status);
                                                assert(self.fmt == old(self).fmt);
                                                assert(self.journal_alloc == old(self).journal_alloc);
                                                assert(self@ == old(self)@);
                                                assert(self.basic_wf());
                                                assert(self.wf());
                                            }
                                            return RecoverIndexResult::IndexProgress{};
                                        }
                                        proof {
                                            assert(parsable);
                                            assert(self.fmt.parsable(all_slice@.i(slot_handle.rec@)));
                                        }
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
                                            assert(curr is Some);
                                            assert(addr@ == curr.unwrap()@);
                                            assert(journal_disk.entries.contains_key(addr@));
                                            assert(journal_raw_disk.contains_key(addr@));
                                            assert(cache_pre_fetch@.valid_read(addr@, slot_handle.rec@));
                                            assert(cache@ == cache_pre_fetch@);
                                            assert(journal_raw_disk[addr@] == slot_handle.rec@);
                                            reads = reads.insert(addr@, slot_handle.rec@);
                                            assert(addr@.au < total_aus as nat);
                                            to_journal_records_entry_from_exec_parse(self.fmt, reads, addr@, i_journal_record);
                                            assert(to_journal_records(reads)[addr@] == journal_disk.entries[addr@]);
                                            let ghost reads_post = to_journal_records(reads_pre).insert(addr@, to_journal_records(reads)[addr@]);
                                            assert(reads_post <= journal_disk.entries) by {
                                                assert(reads_post.dom() <= journal_disk.entries.dom()) by {
                                                    assert forall |a: Address| #[trigger] reads_post.contains_key(a)
                                                        implies journal_disk.entries.contains_key(a) by {
                                                        if a == addr@ {
                                                        } else {
                                                            assert(to_journal_records(reads_pre).contains_key(a));
                                                            assert(to_journal_records(reads_pre) <= journal_disk.entries);
                                                        }
                                                    }
                                                }
                                                assert forall |a: Address| #[trigger] reads_post.contains_key(a)
                                                    implies reads_post[a] == journal_disk.entries[a] by {
                                                    if a == addr@ {
                                                    } else {
                                                        assert(to_journal_records(reads_pre).contains_key(a));
                                                        assert(to_journal_records(reads_pre) <= journal_disk.entries);
                                                    }
                                                }
                                            }
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
                                        proof {
                                            assert(self.fmt == IJournalRecordFormat::spec_new());
                                            to_journal_records_entry_from_exec_parse(self.fmt, reads, addr@, i_journal_record);
                                        }
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
                                                assert(index@.is_empty());
                                                assert(!index@.values().contains(addr@));
                                            }
                                        }
                                        index.index_prepend_record(old_bound, start, addr);
                                        proof {
                                            assert((start as nat) < (old_bound as nat));
                                            lsn_addr_index_append_record_ensures(
                                                index_pre@,
                                                start as nat,
                                                old_bound as nat,
                                                addr@,
                                            );
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
                                                assert(lsn_disjoint(index_pre@.dom(), start as nat, old_bound as nat));
                                                build_lsn_addr_index_from_reads_extend_next_ptr(to_journal_records(reads_pre), bdy as nat, self@.snapshot.freshest_rec(), prev, ptr2_data);
                                            } else {
                                                assert(index_pre@.dom() =~= Set::<LSN>::empty());
                                                assert(lsn_disjoint(index_pre@.dom(), start as nat, old_bound as nat));
                                            }
                                            build_lsn_addr_index_from_reads_next_ptr_after_insert(to_journal_records(reads_pre), bdy as nat, self@.snapshot.freshest_rec(), prev, to_journal_records(reads)[addr@]);
                                            if was_initialized {
                                                assert(index_pre@.values() =~= reads_pre.dom());
                                            } else {
                                                assert(reads_pre.dom() =~= Set::<Address>::empty());
                                                assert(index_pre@.values() =~= Set::<Address>::empty());
                                            }
                                            assert(index@.values() == index_pre@.values() + set![addr@]);
                                            assert(reads.dom() =~= reads_pre.dom().insert(addr@));
                                            assert(index@.values() =~= reads.dom()) by {
                                                assert forall |a: Address| #[trigger] index@.values().contains(a)
                                                    implies reads.dom().contains(a) by {
                                                    assert((index_pre@.values() + set![addr@]).contains(a));
                                                    if index_pre@.values().contains(a) {
                                                        if was_initialized {
                                                            assert(reads_pre.dom().contains(a));
                                                        } else {
                                                            assert(false);
                                                        }
                                                        assert(reads.dom().contains(a));
                                                    } else {
                                                        assert(a == addr@);
                                                        assert(reads.dom().contains(a));
                                                    }
                                                };
                                                assert forall |a: Address| #[trigger] reads.dom().contains(a)
                                                    implies index@.values().contains(a) by {
                                                    if reads_pre.dom().contains(a) {
                                                        if was_initialized {
                                                            assert(index_pre@.values().contains(a));
                                                        } else {
                                                            assert(false);
                                                        }
                                                        assert((index_pre@.values() + set![addr@]).contains(a));
                                                    } else {
                                                        assert(a == addr@);
                                                        assert((index_pre@.values() + set![addr@]).contains(a));
                                                    }
                                                };
                                            };
                                        }
                                        let prior = i_journal_record.cropped_prior(bdy);
                                        proof {
                                            let ptr2_data = to_journal_records(reads)[addr@];
                                            page_walk_reads_prefix_extend(
                                                to_journal_records(reads_pre),
                                                bdy as nat,
                                                self@.snapshot.freshest_rec(),
                                                load_index_walk_depth,
                                                addr@,
                                                ptr2_data,
                                            );
                                            assert(to_journal_records(reads) == to_journal_records(reads_pre).insert(addr@, ptr2_data));
                                            assert(ptr2_data == i_journal_record.parsedv().view());
                                            assert(iaddr_view(prior) == ptr2_data.cropped_prior(bdy as nat));
                                            load_index_walk_depth = load_index_walk_depth + 1;
                                        }
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
                            proof {
                                assert(index.seq_start() == bdy);
                                assert(curr is None);
                                assert(iaddr_view(curr) == build_lsn_addr_index_from_reads_next_ptr(
                                    to_journal_records(reads),
                                    bdy as nat,
                                    self@.snapshot.freshest_rec(),
                                ));
                                assert(build_lsn_addr_index_from_reads_next_ptr(
                                    to_journal_records(reads),
                                    bdy as nat,
                                    self@.snapshot.freshest_rec(),
                                ) is None);
                                page_walk_reads_prefix_complete(
                                    to_journal_records(reads),
                                    bdy as nat,
                                    self@.snapshot.freshest_rec(),
                                    load_index_walk_depth,
                                );
                            }
                        } else {
                            index = ILsnAddrIndex::new(bdy);
                            proof {
                                assert(build_lsn_addr_index_from_reads_next_ptr(
                                    to_journal_records(reads),
                                    bdy as nat,
                                    self@.snapshot.freshest_rec(),
                                ) is None);
                                assert(page_walk_reads_prefix(
                                    to_journal_records(reads),
                                    bdy as nat,
                                    self@.snapshot.freshest_rec(),
                                    load_index_walk_depth,
                                    None,
                                ));
                                page_walk_reads_prefix_complete(
                                    to_journal_records(reads),
                                    bdy as nat,
                                    self@.snapshot.freshest_rec(),
                                    load_index_walk_depth,
                                );
                            }
                        }

                        let i_seq_end = index.exec_seq_end();
                        let ghost load_index_ptr = self@.snapshot.freshest_rec();
                        let ghost load_index_bdy = self@.snapshot.boundary_lsn;
                        let ghost load_index_first = self@.snapshot.first();
                        let ghost load_index_reads = to_journal_records(reads);
                        let ghost load_index_depth: nat = load_index_walk_depth;
                        let ghost load_index_page_bounds =
                            build_au_page_bounds_from_reads_au_walk_depth(
                                load_index_reads,
                                load_index_bdy,
                                load_index_ptr,
                                load_index_first,
                                load_index_depth,
                                load_index_depth,
                            );
                        self.status = Some(IJournalStatus{
                            unmarshalled_tail: vec![],
                            lsn_addr_index: index,
                            au_page_bounds: Ghost(load_index_page_bounds),
                            clean_watermark_au_page_bounds: Ghost(load_index_page_bounds),
                            clean_watermark_lsn: i_seq_end,
                            recovery_reads: Ghost(reads),
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
                            assert(build_lsn_addr_index_from_reads_next_ptr(journal_reads, bdy, ptr) is None);
                            page_walk_reads_prefix_complete(journal_reads, bdy, ptr, load_index_depth);
                            let full_journal_reads = to_journal_records(journal_raw_disk);
                            if ptr is Some {
                                let full_dv = LinkedJournal_v::DiskView{
                                    boundary_lsn: bdy,
                                    entries: full_journal_reads,
                                };
                                let tight_dv = full_dv.path_build_tight(ptr);
                                let tight_journal_reads = tight_dv.entries;
                                assert(journal_disk_load_index_inv(
                                    full_dv,
                                    ptr,
                                    load_index_first,
                                ));
                                assert(LinkedJournal_v::DiskView{
                                    boundary_lsn: bdy,
                                    entries: tight_journal_reads,
                                } == tight_dv);
                                assert forall |addr: Address| #[trigger] journal_reads.contains_key(addr)
                                    && tight_journal_reads.contains_key(addr)
                                    implies journal_reads[addr] == tight_journal_reads[addr] by {
                                    assert(reads.contains_key(addr));
                                    assert(cache@.valid_read(addr, reads[addr]));
                                    assert(cache_agrees_with_raw_disk_on_domain(cache@, journal_raw_disk));
                                    full_dv.path_build_tight_is_sub_disk(ptr);
                                    assert(tight_journal_reads <= full_journal_reads);
                                    assert(full_journal_reads.contains_key(addr));
                                    assert(journal_raw_disk.contains_key(addr));
                                    assert(journal_raw_disk[addr] == reads[addr]);
                                    assert(journal_reads[addr] == full_journal_reads[addr]);
                                    assert(tight_journal_reads[addr] == full_journal_reads[addr]);
                                }
                                page_walk_reads_cover_to_au_walk_reads_cover(
                                    journal_reads,
                                    tight_journal_reads,
                                    bdy,
                                    ptr,
                                    load_index_first,
                                    load_index_depth,
                                );
                                build_lsn_addr_index_from_reads_to_au_index_au_walk_depth(
                                    journal_reads,
                                    tight_journal_reads,
                                    bdy,
                                    ptr,
                                    load_index_first,
                                    load_index_depth,
                                    load_index_depth,
                                );
                                assert forall |addr: Address|
                                    #[trigger] self.status.unwrap().lsn_addr_index@.values().contains(addr)
                                    implies self.status.unwrap().au_page_bounds@.contains_key(addr.au)
                                        && addr.page <= self.status.unwrap().au_page_bounds@[addr.au] by {
                                    assert(lsn_addr_index.values().contains(addr));
                                    build_lsn_addr_index_from_reads_values_bounded_by_au_page_bounds(
                                        journal_reads,
                                        tight_journal_reads,
                                        bdy,
                                        ptr,
                                        load_index_first,
                                        load_index_depth,
                                        load_index_depth,
                                        addr,
                                    );
                                    assert(self.status.unwrap().au_page_bounds@
                                        == load_index_page_bounds);
                                }
                                page_walk_reads_cover_addr_build_matches_full_by_value(
                                    journal_reads,
                                    full_journal_reads,
                                    bdy,
                                    ptr,
                                    load_index_depth,
                                );
                                let full_tj = LinkedJournal_v::TruncatedJournal{
                                    freshest_rec: ptr,
                                    disk_view: full_dv,
                                };
                                assert(lsn_addr_index =~= full_tj.build_lsn_addr_index());
                                full_tj.build_lsn_addr_index_ensures();
                                reveal(LinkedJournal_v::TruncatedJournal::index_domain_valid);
                                let model_index = self.status.unwrap().lsn_addr_index@;
                                let lai_seq_end = self.status.unwrap().lsn_addr_index.seq_end() as nat;
                                assert(full_tj.seq_end() == lai_seq_end) by {
                                    if full_tj.seq_end() < lai_seq_end {
                                        let lsn = full_tj.seq_end();
                                        assert(model_index.contains_key(lsn)) by {
                                            self.status.unwrap().lsn_addr_index.view_domain();
                                            assert(model_index.dom() =~= Set::new(|lsn: LSN|
                                                self.seq_start() <= lsn < lai_seq_end));
                                        }
                                        assert(!model_index.contains_key(lsn));
                                        assert(false);
                                    }
                                    if lai_seq_end < full_tj.seq_end() {
                                        let lsn = lai_seq_end;
                                        assert(model_index.contains_key(lsn)) by {
                                            assert(full_tj.index_domain_valid(model_index));
                                        }
                                        assert(!model_index.contains_key(lsn)) by {
                                            self.status.unwrap().lsn_addr_index.view_domain();
                                            assert(model_index.dom() =~= Set::new(|lsn: LSN|
                                                self.seq_start() <= lsn < lai_seq_end));
                                        }
                                        assert(false);
                                    }
                                };
                                assert(full_tj.seq_end() == self.seq_end());
                                assert forall |lsn: LSN|
                                    #[trigger] model_index.contains_key(lsn)
                                    implies {
                                        let addr = model_index[lsn];
                                        let record = journal_reads[addr];
                                        let cropped = record.message_seq.maybe_discard_old(bdy);
                                        &&& reads.contains_key(addr)
                                        &&& cropped.seq_start <= lsn
                                        &&& lsn < record.message_seq.seq_end
                                        &&& record.message_seq.seq_end <= self.status.unwrap().lsn_addr_index.seq_end() as nat
                                        &&& lsn_addr_index_to_au_index(model_index).contains_key(cropped.seq_start)
                                        &&& lsn_addr_index_to_au_index(model_index)[cropped.seq_start] == addr.au
                                    } by {
                                    let addr = model_index[lsn];
                                    assert(lsn_addr_index.contains_key(lsn));
                                    full_dv.instantiate_index_keys_map_to_valid_entries(model_index, lsn);
                                    build_lsn_addr_index_from_reads_values_in_reads(
                                        journal_reads,
                                        bdy,
                                        ptr,
                                        addr,
                                    );
                                    assert(reads.contains_key(addr));
                                    assert(journal_reads[addr] == full_journal_reads[addr]);
                                    let record = journal_reads[addr];
                                    let cropped = record.message_seq.maybe_discard_old(bdy);
                                    assert(cropped.seq_start <= lsn);
                                    assert(lsn < record.message_seq.seq_end);
                                    if record.message_seq.seq_end > full_tj.seq_end() {
                                        assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(
                                            full_dv.boundary_lsn,
                                            record.message_seq,
                                            full_tj.seq_end(),
                                        ));
                                        assert(full_tj.every_lsn_at_addr_indexed_to_addr(model_index, addr));
                                        assert(model_index.contains_key(full_tj.seq_end()));
                                        assert(!model_index.contains_key(full_tj.seq_end())) by {
                                            self.status.unwrap().lsn_addr_index.view_domain();
                                            assert(model_index.dom() =~= Set::new(|lsn: LSN|
                                                self.seq_start() <= lsn < lai_seq_end));
                                            assert(full_tj.seq_end() == lai_seq_end);
                                        }
                                        assert(false);
                                    }
                                    assert(record.message_seq.seq_end <= self.status.unwrap().lsn_addr_index.seq_end() as nat);
                                    assert(LinkedJournal_v::DiskView::cropped_msg_seq_contains_lsn(
                                        full_dv.boundary_lsn,
                                        record.message_seq,
                                        cropped.seq_start,
                                    ));
                                    assert(full_tj.every_lsn_at_addr_indexed_to_addr(model_index, addr));
                                    assert(model_index.contains_key(cropped.seq_start));
                                    assert(model_index[cropped.seq_start] == addr);
                                    assert(lsn_addr_index_to_au_index(model_index).contains_key(cropped.seq_start));
                                    assert(lsn_addr_index_to_au_index(model_index)[cropped.seq_start] == addr.au);
                                };
                            } else {
                                assert(load_index_depth == 0);
                                assert(build_lsn_au_index_from_reads_au_walk_depth(
                                    journal_reads,
                                    bdy,
                                    ptr,
                                    load_index_first,
                                    load_index_depth,
                                    load_index_depth,
                                ) =~= Map::<LSN, AU>::empty());
                                assert forall |addr: Address|
                                    #[trigger] self.status.unwrap().lsn_addr_index@.values().contains(addr)
                                    implies self.status.unwrap().au_page_bounds@.contains_key(addr.au)
                                        && addr.page <= self.status.unwrap().au_page_bounds@[addr.au] by {
                                    assert(lsn_addr_index =~= Map::<LSN, Address>::empty());
                                    assert(!lsn_addr_index.values().contains(addr));
                                }
                            }
                            assert(self@.status.unwrap().lsn_au_index
                                == lsn_addr_index_to_au_index(self.status.unwrap().lsn_addr_index@));
                            assert(self.status.unwrap().lsn_addr_index@ =~= lsn_addr_index);
                            assert(self@.status.unwrap().lsn_au_index
                                =~= build_lsn_au_index_from_reads_au_walk_depth(
                                    journal_reads,
                                    bdy,
                                    ptr,
                                    load_index_first,
                                    load_index_depth,
                                    load_index_depth,
                                ));
                            lsn_addr_index_to_au_index_values_match(self.status.unwrap().lsn_addr_index@);
                            assert(self.status.unwrap().lsn_addr_index@.values() =~= reads.dom());
                            assert(self@.status.unwrap().lsn_au_index.values() =~= to_aus(reads.dom()));
                            assert(self.index_aus_bounded(total_aus)) by {
                                assert forall |au: AU| #[trigger]
                                    self@.status.unwrap().lsn_au_index.values().contains(au)
                                    implies au < total_aus as nat by {
                                    assert(to_aus(reads.dom()).contains(au));
                                    let addr = choose |addr: Address|
                                        #[trigger] reads.contains_key(addr) && addr.au == au;
                                    assert(reads.contains_key(addr));
                                    assert(addr.au < total_aus as nat);
                                    assert(au < total_aus as nat);
                                }
                            }
                            assert(to_aus(reads.dom()) =~= build_lsn_au_index_from_reads_au_walk_depth(
                                journal_reads,
                                bdy,
                                ptr,
                                load_index_first,
                                load_index_depth,
                                load_index_depth,
                            ).values());
                            assert(CachedJournal::State::load_index(
                                old(self)@,
                                self@,
                                journal_lbl,
                                load_index_depth,
                                load_index_depth,
                            )) by {
                                reveal(CachedJournal::State::load_index);
                            }
                            assert(CachedJournal::State::next_by(
                                old(self)@,
                                self@,
                                journal_lbl,
                                CachedJournal::Step::load_index(load_index_depth, load_index_depth),
                            )) by {
                                reveal(CachedJournal::State::next_by);
                            }
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
                        if addr.au >= total_aus {
                            out = RecoverIndexResult::IndexProgress{};
                            Some(builder)
                        } else if addr.au == 0 && addr.page == 0 {
                            out = RecoverIndexResult::IndexProgress{};
                            Some(builder)
                        } else {
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
                                let parsable = self.fmt.exec_parsable(&all_slice, &slot_handle.rec);
                                if !parsable {
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
                                        assert(cache@ == cache_pre_fetch@);
                                        assert(cache@ == old(cache)@);
                                    }
                                    out = RecoverIndexResult::IndexProgress{};
                                    Some(builder)
                                } else {
                                proof {
                                    assert(parsable);
                                    assert(self.fmt.parsable(all_slice@.i(slot_handle.rec@)));
                                }
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
                                }
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
        self.journal_alloc.i() == old(self).journal_alloc.i(),
        self.journal_alloc.allocators@ == old(self).journal_alloc.allocators@,
        self.journal_alloc.curr == old(self).journal_alloc.curr,
        self.journal_alloc.free_au_threshold == old(self).journal_alloc.free_au_threshold,
        forall |total_aus: IAU| old(self).journal_alloc.bounded(total_aus)
            ==> self.journal_alloc.bounded(total_aus),
        self.basic_wf(),
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
            self.wf_implies_basic_wf();
        }
    }

    pub exec fn peek_next_addr(&self) -> (out: IAddress)
        requires
            self.basic_wf(),
            self.journal_alloc.allocation_ready(),
        ensures
            out.au == self.journal_alloc.alloc_au(),
            out.au as nat == self.alloc_au(),
            out@.au == self.alloc_au(),
            out.page == self.journal_alloc.next_page(),
            out@ == self.journal_alloc.next_addr(),
    {
        self.journal_alloc.peek_next_addr()
    }

    pub exec fn marshall_next_addr_root_check(&self, addr: &IAddress) -> (ok: bool)
        requires
            self.basic_wf(),
            self.index_ready(),
            self.journal_alloc.allocation_ready(),
            MiniAllocatorImpl::allocators_unique(self.journal_alloc.allocators@),
            addr@ == self.journal_alloc.next_addr(),
        ensures
            ok ==> self.marshall_next_addr_root_ok(addr@),
    {
        match self.journal_alloc.curr {
            None => {
                if addr.page != 0 {
                    return false;
                }
                proof {
                    assert(self.journal_alloc.i().curr is None);
                    assert(self.journal_alloc.next_addr().page == 0);
                    self.journal_alloc.curr_none_page_zero_next_addr_all_pages_free();
                    assert(self.journal_alloc.i().allocs.contains_key(addr@.au));
                    assert(self.journal_alloc.i().allocs[addr@.au].all_pages_free());
                    assert(self.marshall_next_addr_root_ok(addr@));
                }
                true
            },
            Some(_) => {
                match self.snapshot.freshest_rec {
                    None => true,
                    Some(root) => {
                        if root.page == u32::MAX {
                            false
                        } else if addr.au == root.au && addr.page == root.page + 1 {
                            proof {
                                assert(self.journal_alloc.i().curr is Some);
                                assert(self@.snapshot.freshest_rec() is Some);
                                assert(self@.snapshot.freshest_rec().unwrap() == root@);
                                assert(addr@ == root@.next());
                                assert(self.marshall_next_addr_root_ok(addr@));
                            }
                            true
                        } else {
                            false
                        }
                    },
                }
            },
        }
    }

    pub exec fn advance_next_addr(&mut self)
        requires
            old(self).basic_wf(),
            old(self).journal_alloc.allocation_ready(),
        ensures
            self@ == old(self)@,
            self.format_ok() == old(self).format_ok(),
            self.alloc_au() == old(self).alloc_au(),
            old(self).wf() ==> self.wf(),
            old(self).index_ready() ==> self.index_ready(),
            old(self).index_ready() ==>
                self.status.unwrap().lsn_addr_index@ == old(self).status.unwrap().lsn_addr_index@,
            self.seq_start() == old(self).seq_start(),
            self.seq_end() == old(self).seq_end(),
    {
        self.journal_alloc.advance_next_addr();
    }

    pub closed spec fn alloc_au(&self) -> nat
        recommends
            self.journal_alloc.wf(),
    {
        if self.journal_alloc.allocation_ready() {
            self.journal_alloc.alloc_au_nat()
        } else {
            0
        }
    }

    pub exec fn reset_free_au_threshold(&mut self, free_au_threshold: IAU)
        requires
            old(self).basic_wf(),
        ensures
            self.basic_wf(),
            self@ == old(self)@,
            self.alloc_au() == old(self).alloc_au(),
    {
        self.journal_alloc.reset_threshold(free_au_threshold);
    }

    pub exec fn free_aus_below_threshold(&self) -> (out: bool)
        requires
            self.basic_wf(),
    {
        self.journal_alloc.free_aus_below_threshold()
    }

    pub exec fn prune_allocated_aus(
        &mut self,
        disk_au_count: IAU,
    ) -> (out: Vec<IAU>)
        requires
            old(self).wf(),
            old(self).index_ready(),
            MiniAllocatorImpl::allocators_unique(old(self).journal_alloc.allocators@),
            old(self).journal_alloc.bounded(disk_au_count),
            0 < page_count(),
        ensures
            self.wf(),
            self.index_ready(),
            self@ == old(self)@,
            self.seq_start() == old(self).seq_start(),
            self.seq_end() == old(self).seq_end(),
            MiniAllocatorImpl::allocators_unique(self.journal_alloc.allocators@),
            self.journal_alloc.bounded(disk_au_count),
            iau_vec_set(out@) =~= old(self).journal_alloc.i().allocated_aus(),
            self.journal_alloc.i()
                == old(self).journal_alloc.i().prune(iau_vec_set(out@)),
            self.journal_alloc.i().allocated_aus() =~= Set::<AU>::empty(),
            MiniAllocatorImpl::allocators_au_set(self.journal_alloc.allocators@) =~=
                MiniAllocatorImpl::allocators_au_set(old(self).journal_alloc.allocators@)
                    - iau_vec_set(out@),
    {
        let ghost pre_allocator = self.journal_alloc.i();
        let out = self.journal_alloc.prune_allocated_aus(disk_au_count);
        proof {
            pre_allocator.prune_allocated_aus_empty();
        }
        out
    }

    pub exec fn background_refill_aus(
        &mut self,
        pool: &mut AuPoolImpl,
        total_aus: IAU,
    ) -> (out: Option<AuAllocation>)
        requires
            old(self).basic_wf(),
            MiniAllocatorImpl::allocators_unique(old(self).journal_alloc.allocators@),
            old(pool).canonical_wf(total_aus),
            old(pool)@.disjoint(
                MiniAllocatorImpl::allocators_au_set(old(self).journal_alloc.allocators@),
            ),
        ensures
            self.basic_wf(),
            MiniAllocatorImpl::allocators_unique(self.journal_alloc.allocators@),
            old(self).journal_alloc.bounded(total_aus) ==> self.journal_alloc.bounded(total_aus),
            self.snapshot == old(self).snapshot,
            self.status == old(self).status,
            self@ == old(self)@,
            self.seq_start() == old(self).seq_start(),
            self.seq_end() == old(self).seq_end(),
            pool.canonical_wf(total_aus),
            pool@.disjoint(
                MiniAllocatorImpl::allocators_au_set(self.journal_alloc.allocators@),
            ),
            match out {
                Some(allocation) => {
                    &&& allocation.wf(total_aus)
                    &&& allocation.as_set() <= old(pool)@
                    &&& pool@ =~= old(pool)@ - allocation.as_set()
                    &&& self.journal_alloc.i()
                        == old(self).journal_alloc.i().add_aus(allocation.as_set())
                },
                None => {
                    &&& pool@ =~= old(pool)@
                    &&& self.journal_alloc.i() == old(self).journal_alloc.i()
                    &&& self.journal_alloc.allocators@ == old(self).journal_alloc.allocators@
                    &&& self.journal_alloc.curr == old(self).journal_alloc.curr
                    &&& self.journal_alloc.free_au_threshold
                        == old(self).journal_alloc.free_au_threshold
                },
            },
    {
        self.journal_alloc.refill_from_pool_allow_empty(pool, total_aus)
    }

    pub exec fn recovered_index_aus(&self) -> (out: Vec<IAU>)
        requires
            self.wf(),
            self.index_ready(),
        ensures
            iau_vec_set(out@) =~= to_aus(self.status.unwrap().lsn_addr_index@.values()),
    {
        match &self.status {
            Some(status) => status.lsn_addr_index.au_vec(),
            None => Vec::new(),
        }
    }

    pub exec fn recover_index_step_for_unified(
        &mut self,
        cache: &mut FracCacheImpl,
        journal_raw_disk_ghost: Ghost<Map<Address, RawPage>>,
        total_aus: IAU,
    ) -> (out: UnifiedRecoverIndexResult)
        requires
            old(self).basic_wf(),
            !old(self).index_ready(),
            old(self).snapshot_geometry_bounded(total_aus),
            old(cache).wf(),
            cache_agrees_with_raw_disk_on_domain(old(cache)@, journal_raw_disk_ghost@),
            old(self)@.snapshot.freshest_rec() is Some ==>
                journal_disk_load_index_inv(
                    LinkedJournal_v::DiskView{
                        boundary_lsn: old(self)@.snapshot.boundary_lsn,
                        entries: to_journal_records(journal_raw_disk_ghost@),
                    },
                    old(self)@.snapshot.freshest_rec(),
                    old(self)@.snapshot.first()),
        ensures ({
            &&& self.basic_wf()
            &&& self@.wf()
            &&& self.journal_alloc.i() == old(self).journal_alloc.i()
            &&& self.seq_start() == old(self).seq_start()
            &&& self.snapshot_geometry_bounded(total_aus)
            &&& cache.wf()
            &&& cache.valid_load_handles_preserved(*old(cache))
            &&& match out {
                UnifiedRecoverIndexResult::CacheLoad{slot_handle, addr} => {
                    &&& self@ == old(self)@
                &&& addr@ != spec_superblock_addr()
                &&& addr@.au < total_aus as nat
                    &&& !old(cache).entry_fetched(&addr)
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_load_handle(&addr, slot_handle)
                    &&& Cache::State::next(old(cache)@, cache@, cache_load_label(&addr))
                },
                UnifiedRecoverIndexResult::IndexComplete{reads, discovered_aus} => {
                    let (cache_lbl, journal_lbl) = load_index_labels(reads@);
                    &&& old(cache)@ == cache@
                    &&& self.wf()
                    &&& self.index_ready()
                    &&& self.index_aus_bounded(total_aus)
                    &&& self.no_unmarshalled_entries()
                    &&& self.seq_start() <= self.seq_end()
                    &&& iau_vec_set(discovered_aus@) =~= to_aus(reads@.dom())
                    &&& Cache::State::next(old(cache)@, cache@, cache_lbl)
                    &&& CachedJournal::State::next(old(self)@, self@, journal_lbl)
                    &&& exists |au_depth: nat, page_depth: nat| CachedJournal::State::load_index(
                        old(self)@,
                        self@,
                        journal_lbl,
                        au_depth,
                        page_depth,
                    )
                },
                UnifiedRecoverIndexResult::IndexProgress{} => {
                    &&& old(cache)@ == cache@
                    &&& self@ == old(self)@
                },
            }
        })
    {
        match self.recover_index_step(cache, journal_raw_disk_ghost, total_aus) {
            RecoverIndexResult::CacheLoad{slot_handle, addr} => {
                UnifiedRecoverIndexResult::CacheLoad{slot_handle, addr}
            },
            RecoverIndexResult::IndexComplete{reads} => {
                let discovered_aus = self.recovered_index_aus();
                proof {
                    CachedJournal::State::load_index_effect(
                        old(self)@,
                        self@,
                        to_journal_records(reads@),
                        to_aus(reads@.dom()),
                    );
                    lsn_addr_index_to_au_index_values_match(
                        self.status.unwrap().lsn_addr_index@,
                    );
                    assert(self@.status.unwrap().lsn_au_index
                        == lsn_addr_index_to_au_index(self.status.unwrap().lsn_addr_index@));
                    assert(self@.status.unwrap().lsn_au_index.values()
                        =~= to_aus(self.status.unwrap().lsn_addr_index@.values()));
                    assert(to_aus(self.status.unwrap().lsn_addr_index@.values())
                        =~= to_aus(reads@.dom()));
                    assert(iau_vec_set(discovered_aus@)
                        =~= to_aus(reads@.dom()));
                }
                UnifiedRecoverIndexResult::IndexComplete{reads, discovered_aus}
            },
            RecoverIndexResult::IndexProgress{} => {
                UnifiedRecoverIndexResult::IndexProgress{}
            },
        }
    }

    pub exec fn recover_map_step_for_unified(
        &self,
        cache: &mut FracCacheImpl,
        start_lsn: ILsn,
        journal_raw_disk_ghost: Ghost<Map<Address, RawPage>>,
    ) -> (out: UnifiedRecoverMapResult)
        requires
            self.wf(),
            self.index_ready(),
            self.no_unmarshalled_entries(),
            self.seq_start() <= (start_lsn as nat),
            (start_lsn as nat) < self.seq_end(),
            old(cache).wf(),
        ensures ({
            &&& self.wf()
            &&& self.index_ready()
            &&& cache.wf()
            &&& cache.valid_load_handles_preserved(*old(cache))
            &&& match out {
                UnifiedRecoverMapResult::FetchSuccess{reads, addr, record, keys, msgs} => {
                    let lbls = map_recovery_labels(self.seq_start(), reads@, addr@);
                    &&& self.seq_start() <= start_lsn as nat
                    &&& (start_lsn as nat) < self.seq_end()
                    &&& reads@.contains_key(addr@)
                    &&& to_journal_records(reads@)[addr@] == record.parsedv().view()
                    &&& record.parsedv().view().message_seq.seq_start <= start_lsn as nat
                    &&& (start_lsn as nat) < record.parsedv().view().message_seq.seq_end
                    &&& record.parsedv().view().message_seq.seq_end <= self.seq_end()
                    &&& keys@.len() == msgs@.len()
                    &&& to_journal_records(reads@)[addr@].message_seq.maybe_discard_old(start_lsn as nat)
                        == append_puts(start_lsn as nat, keys@, msgs@)
                    &&& Cache::State::next(old(cache)@, cache@, lbls.0)
                    &&& CachedJournal::State::next(self@, self@, lbls.1)
                },
                UnifiedRecoverMapResult::NotInCache{} => old(cache)@ == cache@,
                UnifiedRecoverMapResult::InvalidRecord{} => old(cache)@ == cache@,
            }
        })
    {
        match self.recover_map_step(cache, start_lsn, journal_raw_disk_ghost) {
            RecoverMapResult::FetchSuccess{reads, addr, record} => {
                let mut keys = Vec::<Key>::new();
                let mut msgs = Vec::<Message>::new();
                let mut idx: usize = 0;
                if record.header.start_lsn < start_lsn {
                    let offset = start_lsn - record.header.start_lsn;
                    if offset > usize::MAX as u64 {
                        convert_overflow_into_liveness_failure();
                    }
                    idx = offset as usize;
                }
                let start_idx = idx;
                proof {
                    assert(record.parsedv().view().message_seq.seq_start
                        == record.header.start_lsn as nat);
                    if !(record.header.start_lsn < start_lsn) {
                        assert(record.header.start_lsn as nat == start_lsn as nat);
                    } else {
                        let offset = start_lsn - record.header.start_lsn;
                        assert(offset <= usize::MAX as u64);
                        assert(offset as nat == start_lsn as nat
                            - record.header.start_lsn as nat);
                        assert(start_idx as nat == offset as nat);
                    }
                    assert(start_idx as nat == start_lsn as nat
                        - record.parsedv().view().message_seq.seq_start);
                }
                while idx < record.messages.len()
                    invariant
                        record.parsedv().view().message_seq.seq_start <= start_lsn as nat,
                        start_lsn as nat <= record.parsedv().view().message_seq.seq_end,
                        start_idx as nat == start_lsn as nat
                            - record.parsedv().view().message_seq.seq_start,
                        start_idx <= idx,
                        idx <= record.messages.len(),
                        keys@.len() == (idx - start_idx) as nat,
                        msgs@.len() == (idx - start_idx) as nat,
                        keys@.len() == msgs@.len(),
                        forall |j: int| 0 <= j < keys@.len() ==> {
                            &&& keys@[j] == record.messages@[start_idx as int + j].key
                            &&& msgs@[j] == record.messages@[start_idx as int + j].message
                        },
                    decreases record.messages.len() - idx,
                {
                    let msg = record.messages[idx];
                    keys.push(msg.key);
                    msgs.push(msg.message);
                    idx = idx + 1;
                }
                proof {
                    journal_record_suffix_is_append_puts(
                        record,
                        start_lsn as nat,
                        start_idx as nat,
                        keys@,
                        msgs@,
                    );
                }
                UnifiedRecoverMapResult::FetchSuccess{reads, addr, record, keys, msgs}
            },
            RecoverMapResult::NotInCache{} => {
                UnifiedRecoverMapResult::NotInCache{}
            },
            RecoverMapResult::InvalidRecord{} => {
                UnifiedRecoverMapResult::InvalidRecord{}
            },
        }
    }

    pub exec fn internal_journal_marshall_reserve_slot(
        &mut self,
        cache: &mut FracCacheImpl,
        disk_au_count: IAU,
        disk_page_count: IPage,
    ) -> (out: MarshalReserveResult)
        requires
            old(self).wf(),
            old(self).index_ready(),
            MiniAllocatorImpl::allocators_unique(old(self).journal_alloc.allocators@),
            old(self).journal_alloc.bounded(disk_au_count),
            0 < (disk_page_count as nat),
            (disk_page_count as nat) == page_count(),
            old(cache).wf(),
            old(cache)@.inv(),
        ensures
            self.wf(),
            self.index_ready(),
            self.snapshot == old(self).snapshot,
            self.status == old(self).status,
            old(self).journal_alloc.bounded(disk_au_count)
                ==> self.journal_alloc.bounded(disk_au_count),
            MiniAllocatorImpl::allocators_unique(self.journal_alloc.allocators@),
            MiniAllocatorImpl::allocators_au_set(self.journal_alloc.allocators@) =~=
                MiniAllocatorImpl::allocators_au_set(old(self).journal_alloc.allocators@),
            old(self)@ == self@,
            self.seq_start() == old(self).seq_start(),
            self.seq_end() == old(self).seq_end(),
            cache.wf(),
            cache.valid_load_handles_preserved(*old(cache)),
            match out {
                MarshalReserveResult::Reserved{addr, slot_handle} => {
                    &&& cache.entry_fetched(&addr)
                    &&& cache.valid_write_handle(&addr, slot_handle)
                    &&& cache@.valid_write(addr@)
                    &&& !self.status.unwrap().lsn_addr_index@.values().contains(addr@)
                    &&& old(self).journal_alloc.allocation_ready()
                    &&& addr@ == old(self).journal_alloc.next_addr()
                    &&& old(self).journal_alloc.i().can_allocate(addr@)
                    &&& old(self).journal_alloc.i().tight_next_addr(
                        old(self)@.snapshot.freshest_rec(),
                        addr@,
                    )
                    &&& self.journal_alloc.i() == old(self).journal_alloc.i().allocate(addr@)
                    &&& Cache::State::next(old(cache)@, cache@, Cache::Label::Internal)
                },
                MarshalReserveResult::CacheFull{} => {
                    &&& *cache == *old(cache)
                    &&& self.journal_alloc.i() == old(self).journal_alloc.i()
                    &&& self.journal_alloc.allocators@ == old(self).journal_alloc.allocators@
                    &&& self.journal_alloc.curr == old(self).journal_alloc.curr
                    &&& self.journal_alloc.free_au_threshold
                        == old(self).journal_alloc.free_au_threshold
                },
            },
    {
        let ghost cache0 = *cache;
        if !self.journal_alloc.is_allocation_ready() {
            proof {
                assert(*cache == cache0);
                assert(self@ == old(self)@);
            }
            return MarshalReserveResult::CacheFull{};
        }
        let addr = self.peek_next_addr();
        let ghost pre_alloc = self.journal_alloc;
        let ghost pre_next_addr = self.journal_alloc.next_addr();
        proof {
            assert(addr@ == pre_next_addr);
        }
        if addr.page >= disk_page_count {
            proof {
                assert(*cache == cache0);
                assert(self@ == old(self)@);
            }
            return MarshalReserveResult::CacheFull{};
        }
        if !self.marshall_next_addr_root_check(&addr) {
            proof {
                assert(*cache == cache0);
                assert(self@ == old(self)@);
            }
            return MarshalReserveResult::CacheFull{};
        }
        proof {
            assert(self.marshall_next_addr_root_ok(addr@));
            assert(old(self).marshall_next_addr_root_ok(addr@));
        }
        let already_indexed = self.status.as_ref().unwrap().lsn_addr_index.contains_addr(&addr);
        if already_indexed {
            proof {
                assert(*cache == cache0);
                assert(self@ == old(self)@);
            }
            return MarshalReserveResult::CacheFull{};
        }
        let already_cached = cache.contains_addr(&addr);
        if already_cached {
            proof {
                assert(*cache == cache0);
                assert(self@ == old(self)@);
            }
            return MarshalReserveResult::CacheFull{};
        }
        match cache.reserve_for_write_absent(&addr) {
            ReserveWriteResult::Reserved{slot_handle} => {
                proof {
                    assert(self.journal_alloc == pre_alloc);
                    assert(self.journal_alloc.allocation_ready());
                    assert(addr.page == self.journal_alloc.next_page());
                    assert((addr.page as nat) < (disk_page_count as nat));
                    assert((self.journal_alloc.next_page() as nat) < (disk_page_count as nat));
                }
                let allocated = self.journal_alloc.allocate_fresh_addr_checked(
                    disk_au_count,
                    disk_page_count,
                );
                let allocated_addr = match allocated {
                    Some(allocated_addr) => allocated_addr,
                    None => {
                        proof { assert(false); }
                        unreached()
                    },
                };
                proof {
                    assert(allocated is Some);
                    assert(allocated_addr.au == addr.au);
                    assert(allocated_addr.page == addr.page);
                    assert(allocated_addr == addr);
                    assert(addr@ == pre_next_addr);
                    assert(pre_next_addr == old(self).journal_alloc.next_addr());
                    assert(addr@ == old(self).journal_alloc.next_addr());
                    assert(old(self).marshall_next_addr_root_ok(addr@));
                    assert(old(self).journal_alloc.i().tight_next_addr(
                        old(self)@.snapshot.freshest_rec(),
                        addr@,
                    )) by {
                        assert(old(self).journal_alloc.i().can_allocate(addr@));
                        if old(self).journal_alloc.i().curr is None {
                            assert(old(self).marshall_next_addr_root_ok(addr@));
                            assert(old(self).journal_alloc.i().allocs[addr@.au].all_pages_free());
                            assert(addr@.page == 0);
                        }
                        if old(self).journal_alloc.i().curr is Some
                            && old(self)@.snapshot.freshest_rec() is Some {
                            assert(old(self).marshall_next_addr_root_ok(addr@));
                            assert(addr@ == old(self)@.snapshot.freshest_rec().unwrap().next());
                        }
                    }
                    assert(self@ == old(self)@);
                    assert(self.status.unwrap().lsn_addr_index@
                        =~= old(self).status.unwrap().lsn_addr_index@);
                    assert(self.status.unwrap().lsn_addr_index@.values()
                        =~= old(self).status.unwrap().lsn_addr_index@.values());
                    assert(Cache::State::next(cache0@, cache@, Cache::Label::Internal));
                    Cache::State::inv_next(cache0@, cache@, Cache::Label::Internal);
                    assert(self.status.unwrap().lsn_addr_index@.values().contains(addr@)
                        == old(self).status.unwrap().lsn_addr_index@.values().contains(addr@));
                }
                MarshalReserveResult::Reserved{addr, slot_handle}
            },
            ReserveWriteResult::CacheFull => {
                proof {
                    assert(cache@ == cache0@);
                    assert(self@ == old(self)@);
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
            &&& self.seq_start() == old(self).seq_start()
            &&& self.seq_end() == old(self).seq_end()
            &&& self.journal_alloc == old(self).journal_alloc
            &&& self.journal_alloc.i() == old(self).journal_alloc.i()
            &&& self@.status.unwrap().lsn_au_index.values() =~=
                old(self)@.status.unwrap().lsn_au_index.values().insert(addr@.au)
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

        proof {
            status.lsn_addr_index.derive_lsn_index_domain_exact();
        }
        let ghost old_index = status.lsn_addr_index@;
        let ghost old_bounds = status.au_page_bounds@;
        let new_tail_start = tail_start + cut_count as u64;
        status.lsn_addr_index.index_append_record(tail_start, new_tail_start, addr);
        status.au_page_bounds = Ghost(au_page_bounds_observe_addr(status.au_page_bounds@, addr@));
        if self.snapshot.freshest_rec.is_none() {
            self.snapshot.first = addr.au;
        }
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
            append_preserves_addr_bounds(
                old_index,
                old_bounds,
                tail_start as nat,
                new_tail_start as nat,
                addr@,
            );
            assert forall |a: Address|
                #[trigger] self.status.unwrap().lsn_addr_index@.values().contains(a)
                implies self.status.unwrap().au_page_bounds@.contains_key(a.au)
                    && a.page <= self.status.unwrap().au_page_bounds@[a.au] by {
                assert(self.status.unwrap().lsn_addr_index@
                    == lsn_addr_index_append_record(old_index, tail_start as nat, new_tail_start as nat, addr@));
                assert(self.status.unwrap().au_page_bounds@
                    == au_page_bounds_observe_addr(old_bounds, addr@));
            }
            assert(self.status.unwrap().wf());
            assert(self@.status.unwrap().unmarshalled_tail
                == pre_journal.status.unwrap().unmarshalled_tail.discard_old(cut));
            assert(self@.status.unwrap().unmarshalled_tail.seq_start == cut);
            let ghost marshalled_msgs = pre_journal.status.unwrap().unmarshalled_tail.discard_recent(cut);
            assert(marshalled_msgs == marshalled_record.message_seq);
            assert(marshalled_msgs.seq_start == tail_start as nat);
            assert(marshalled_msgs.seq_end == new_tail_start as nat);
            lsn_addr_index_to_au_index_append_record(
                old_index,
                tail_start as nat,
                new_tail_start as nat,
                addr@,
            );
            assert(pre_journal.status.unwrap().lsn_au_index
                == lsn_addr_index_to_au_index(old_index));
            assert(self@.status.unwrap().lsn_au_index
                =~= lsn_au_index_append_record(
                    pre_journal.status.unwrap().lsn_au_index,
                    marshalled_msgs,
                    addr@.au,
                )) by {
                let ghost au_update =
                    crate::allocation_layer::AllocationJournal_v::singleton_index(
                        marshalled_msgs.seq_start,
                        marshalled_msgs.seq_end,
                        addr@.au,
                    );
                assert(lsn_au_index_append_record(
                    pre_journal.status.unwrap().lsn_au_index,
                    marshalled_msgs,
                    addr@.au,
                ) == pre_journal.status.unwrap().lsn_au_index.union_prefer_right(au_update));
                assert(lsn_addr_index_to_au_index(
                    lsn_addr_index_append_record(
                        old_index,
                        tail_start as nat,
                        new_tail_start as nat,
                        addr@,
                    ),
                ) =~= pre_journal.status.unwrap().lsn_au_index.union_prefer_right(au_update));
                assert(self.status.unwrap().lsn_addr_index@
                    == lsn_addr_index_append_record(
                        old_index,
                        tail_start as nat,
                        new_tail_start as nat,
                        addr@,
                    ));
            }
            assert(lsn_disjoint(
                pre_journal.status.unwrap().lsn_au_index.dom(),
                marshalled_msgs.seq_start,
                marshalled_msgs.seq_end,
            )) by {
                assert(pre_journal.status.unwrap().lsn_au_index.dom()
                    == old_index.dom());
                assert(old_index.dom() =~= Set::new(|lsn: LSN|
                    pre_journal.snapshot.boundary_lsn <= lsn < tail_start as nat));
            }
            lsn_au_index_append_record_ensures(
                pre_journal.status.unwrap().lsn_au_index,
                marshalled_msgs,
                addr@.au,
            );
            assert(self@.status.unwrap().lsn_au_index.values() =~=
                pre_journal.status.unwrap().lsn_au_index.values().insert(addr@.au));
            assert(self@.status.unwrap().au_page_bounds
                == au_page_bounds_observe_addr(pre_journal.status.unwrap().au_page_bounds, addr@));
            assert(self@.status.unwrap().clean_watermark_au_page_bounds
                == pre_journal.status.unwrap().clean_watermark_au_page_bounds);
            assert(self@.status.unwrap().clean_watermark_lsn
                == pre_journal.status.unwrap().clean_watermark_lsn);
            assert(CachedJournal::State::internal_journal_marshal(
                pre_journal,
                self@,
                CachedJournal::Label::JournalMarshal{writes: map!{addr@ => marshalled_record}},
                cut,
                addr@,
            )) by {
                reveal(CachedJournal::State::internal_journal_marshal);
            }
            reveal(CachedJournal::State::next_by);
            reveal(CachedJournal::State::next);
            assert(CachedJournal::State::next_by(
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

    pub proof fn view_snapshot_ensures(&self)
        ensures
            self@.snapshot == self.snapshot@,
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

    pub proof fn view_clean_watermark_ensures(&self)
        requires
            self.index_ready(),
        ensures
            self@.clean_watermark() == self.clean_watermark(),
    {
        broadcast use JournalImpl::view_ensures;
    }

    pub proof fn marshalled_seq_end_le_seq_end(&self)
        requires
            self.wf(),
            self.index_ready(),
        ensures
            self.marshalled_seq_end() <= self.seq_end(),
    {
        broadcast use JournalImpl::view_ensures;
        assert(self@.status is Some);
        assert(self@.status.unwrap().unmarshalled_tail.wf());
        assert(self@.status.unwrap().unmarshalled_tail.seq_start
            <= self@.status.unwrap().unmarshalled_tail.seq_end);
        self.view_marshaled_seq_end_ensures();
        self.view_seq_end_ensures();
    }

    pub proof fn view_seq_start_ensures(&self)
        ensures
            self@.snapshot.boundary_lsn == self.seq_start(),
    {
    }

    pub proof fn tail_empty_implies_no_unmarshalled_entries(&self)
        requires
            self.wf(),
            self.index_ready(),
            self.status.unwrap().unmarshalled_tail.len() == 0,
        ensures
            self.no_unmarshalled_entries(),
    {
        match &self.status {
            Some(status) => {
                assert(status.unmarshalled_tail.len() == 0);
                assert(self.seq_end() == status.lsn_addr_index.seq_end() as nat);
            },
            None => {
                assert(false);
            },
        }
    }

    pub proof fn same_view_preserves_ready_wf(&self, pre: Self)
        requires
            pre.wf(),
            pre.index_ready(),
            self.basic_wf(),
            self.snapshot == pre.snapshot,
            self.status == pre.status,
        ensures
            self.wf(),
            self.index_ready(),
    {
    }

    pub proof fn allocator_index_alignment_preserved(pre: &Self, post: &Self)
        requires
            pre.allocator_index_aligned(),
            post.journal_alloc.i().allocated_aus()
                == pre.journal_alloc.i().allocated_aus(),
            post@.status is Some,
            pre@.status is Some,
            post@.status.unwrap().lsn_au_index
                == pre@.status.unwrap().lsn_au_index,
        ensures
            post.allocator_index_aligned(),
    {
    }

    pub proof fn seq_start_le_marshalled_end(&self)
        requires self.wf(), self.index_ready()
        ensures
            self.seq_start() as nat <= self@.status.unwrap().unmarshalled_tail.seq_start,
            self.seq_start() <= self.marshalled_seq_end(),
    {
        match &self.status {
            Some(status) => {
                assert(self.snapshot.boundary_lsn <= status.lsn_addr_index.seq_end());
            },
            None => {
                assert(false);
            },
        }
    }

    pub proof fn clean_watermark_le_marshaled_seq_end(&self)
        requires self.wf(), self.index_ready()
        ensures self.clean_watermark() <= self.marshalled_seq_end()
    {
    }

    pub proof fn discard_at_seq_start_deallocates_nothing(&self)
        requires
            self.wf(),
            self.index_ready(),
        ensures
            ({
                let index = self@.status.unwrap().lsn_au_index;
                let kept = lsn_au_index_discard_up_to(index, self.seq_start());
                index.values() - kept.values() =~= Set::<AU>::empty()
            }),
    {
        match &self.status {
            Some(status) => {
                status.lsn_addr_index.derive_lsn_index_domain_exact();
                let ghost addr_index = status.lsn_addr_index@;
                let ghost index = self@.status.unwrap().lsn_au_index;
                let ghost kept = lsn_au_index_discard_up_to(index, self.seq_start());
                assert(index == lsn_addr_index_to_au_index(addr_index));
                assert forall |lsn: LSN| #[trigger] index.contains_key(lsn)
                    implies self.seq_start() <= lsn by {
                    assert(addr_index.contains_key(lsn));
                    assert(lsn_index_domain_exact(
                        addr_index,
                        self.seq_start(),
                        status.lsn_addr_index.seq_end() as nat,
                    ));
                }
                crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to_ensures(
                    index,
                    self.seq_start(),
                );
                assert(kept =~= index) by {
                    assert_maps_equal!(kept, index, lsn => {
                        if index.contains_key(lsn) {
                            assert(self.seq_start() <= lsn);
                            assert(kept.contains_key(lsn));
                        }
                    });
                }
                assert(index.values() - kept.values() =~= Set::<AU>::empty());
            },
            None => {
                assert(false);
            },
        }
    }

    pub proof fn discard_at_seq_end_deallocates_all(&self)
        requires
            self.wf(),
            self.index_ready(),
        ensures
            ({
                let index = self@.status.unwrap().lsn_au_index;
                let kept = lsn_au_index_discard_up_to(index, self.seq_end());
                kept.values() =~= Set::<AU>::empty()
            }),
    {
        match &self.status {
            Some(status) => {
                status.lsn_addr_index.derive_lsn_index_domain_exact();
                let ghost addr_index = status.lsn_addr_index@;
                let ghost index = self@.status.unwrap().lsn_au_index;
                let ghost kept = lsn_au_index_discard_up_to(index, self.seq_end());
                assert(index == lsn_addr_index_to_au_index(addr_index));
                crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to_ensures(
                    index,
                    self.seq_end(),
                );
                assert(kept =~= Map::<LSN, AU>::empty()) by {
                    assert_maps_equal!(kept, Map::<LSN, AU>::empty(), lsn => {
                        if kept.contains_key(lsn) {
                            assert(index.contains_key(lsn));
                            assert(self.seq_end() <= lsn);
                            assert(addr_index.contains_key(lsn));
                            assert(lsn < status.lsn_addr_index.seq_end() as nat);
                            assert(status.lsn_addr_index.seq_end() as nat <= self.seq_end());
                            assert(false);
                        }
                    });
                }
            },
            None => assert(false),
        }
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
    pub exec fn freeze_for_commit(
        &self,
        target_lsn: ILsn,
        total_aus: IAU,
    ) -> (out: CleanForCommitResult)
    requires
        self.ready_wf(total_aus),
    ensures
        match out {
            CleanForCommitResult::Frozen{frozen_journal} => {
                &&& target_lsn as nat <= self.clean_watermark()
                &&& frozen_journal.wf()
                &&& frozen_journal.seq_start() as nat == self.seq_start()
                &&& frozen_journal.seq_end as nat == self.clean_watermark()
                &&& frozen_journal.geometry_bounded(total_aus)
                &&& (self.clean_watermark() == self.marshalled_seq_end()
                    ==> frozen_journal.snapshot.freshest_rec == self.snapshot.freshest_rec)
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
            let first = match freshest_rec {
                Some(_) => status.lsn_addr_index.lookup_lsn_with_segment_end(boundary).0.au,
                None => 0,
            };
            let frozen_journal = FrozenJournal{
                snapshot: IJournalSnapshot{
                    boundary_lsn: boundary,
                    freshest_rec,
                    first,
                },
                seq_end: clean,
            };
            proof {
                assert(frozen_journal.geometry_bounded(total_aus)) by {
                    if freshest_rec is Some {
                        let newest_lsn = (clean - 1) as nat;
                        let newest_addr = freshest_rec.unwrap()@;
                        assert(status.lsn_addr_index@.contains_key(newest_lsn));
                        assert(status.lsn_addr_index@[newest_lsn] == newest_addr);
                        assert(self@.status.unwrap().lsn_au_index.contains_key(newest_lsn));
                        assert(self@.status.unwrap().lsn_au_index[newest_lsn]
                            == newest_addr.au);
                        assert(self@.status.unwrap().lsn_au_index.values().contains(
                            newest_addr.au,
                        ));
                        assert(newest_addr.au < total_aus as nat);

                        let first_addr = status.lsn_addr_index@[boundary as nat];
                        assert(status.lsn_addr_index@.contains_key(boundary as nat));
                        assert(first as nat == first_addr.au);
                        assert(self@.status.unwrap().lsn_au_index.contains_key(
                            boundary as nat,
                        ));
                        assert(self@.status.unwrap().lsn_au_index[boundary as nat]
                            == first_addr.au);
                        assert(self@.status.unwrap().lsn_au_index.values().contains(
                            first_addr.au,
                        ));
                        assert(first_addr.au < total_aus as nat);
                    }
                }
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
                    assert(CachedJournal::State::freeze_for_commit(
                        self@,
                        self@,
                        lbl,
                    )) by {
                        reveal(CachedJournal::State::freeze_for_commit);
                    }
                    assert(CachedJournal::State::next_by(
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
                    assert(self@.status.unwrap().lsn_au_index.contains_key((clean - 1) as nat));
                    assert(self@.status.unwrap().lsn_au_index[(clean - 1) as nat] == addr@.au);
                    assert(self@.status.unwrap().lsn_au_index
                        == lsn_addr_index_to_au_index(self.status.unwrap().lsn_addr_index@));
                    assert forall |lsn: LSN| #[trigger] self@.status.unwrap().lsn_au_index.contains_key(lsn)
                        && self@.status.unwrap().lsn_au_index[lsn] == addr@.au
                        implies self@.snapshot.boundary_lsn <= lsn < index_seq_end by {
                        assert(lsn_index_domain_exact(
                            self.status.unwrap().lsn_addr_index@,
                            self@.snapshot.boundary_lsn,
                            index_seq_end,
                        ));
                        assert(self.status.unwrap().lsn_addr_index@.contains_key(lsn));
                    }
                    lsn_au_index_largest_lsn_plus_one_after_witness(
                        self@.status.unwrap().lsn_au_index,
                        addr@.au,
                        self@.snapshot.boundary_lsn,
                        index_seq_end,
                        (clean - 1) as nat,
                    );
                    assert(frozen_journal.snapshot@.freshest_rec().unwrap() == addr@);
                    assert(frozen_journal.snapshot@.boundary_lsn == self@.snapshot.boundary_lsn);
                    assert(self@.status.unwrap().lsn_au_index.contains_key(
                        frozen_journal.snapshot@.boundary_lsn,
                    ));
                    assert(frozen_journal.snapshot@.first()
                        == self@.status.unwrap().lsn_au_index[
                            frozen_journal.snapshot@.boundary_lsn
                        ]);
                    assert(self@.status.unwrap().lsn_au_index.contains_value(addr@.au));
                    assert(frozen_journal.snapshot@.boundary_lsn
                        < largest_lsn_plus_one_au(self@.status.unwrap().lsn_au_index, addr@.au));
                    assert(self.status.unwrap().lsn_addr_index@.values().contains(addr@)) by {
                        assert(self.status.unwrap().lsn_addr_index@.contains_key((clean - 1) as nat));
                        assert(self.status.unwrap().lsn_addr_index@[(clean - 1) as nat] == addr@);
                    }
                    assert(self.status.unwrap().au_page_bounds@.contains_key(addr@.au));
                    assert(addr@.page <= self.status.unwrap().au_page_bounds@[addr@.au]);
                    assert(self@.status.unwrap().au_page_bounds
                        == self.status.unwrap().au_page_bounds@);
                    assert(self@.status.unwrap().au_page_bounds.contains_key(addr@.au));
                    assert(addr@.page <= self@.status.unwrap().au_page_bounds[addr@.au]);
                    assert(frozen_journal.snapshot@.freshest_rec() is Some ==> {
                        let root = frozen_journal.snapshot@.freshest_rec().unwrap();
                        &&& freeze_reads.contains_key(root)
                        &&& frozen_journal.snapshot@.boundary_lsn
                            < freeze_reads[root].message_seq.seq_end
                        &&& self@.status.unwrap().lsn_au_index.contains_key(
                            frozen_journal.snapshot@.boundary_lsn,
                        )
                        &&& frozen_journal.snapshot@.first()
                            == self@.status.unwrap().lsn_au_index[
                                frozen_journal.snapshot@.boundary_lsn
                            ]
                        &&& self@.status.unwrap().lsn_au_index.contains_value(root.au)
                        &&& frozen_journal.snapshot@.boundary_lsn
                            < largest_lsn_plus_one_au(self@.status.unwrap().lsn_au_index, root.au)
                        &&& self@.status.unwrap().au_page_bounds.contains_key(root.au)
                        &&& root.page <= self@.status.unwrap().au_page_bounds[root.au]
                    });

                    assert(CachedJournal::State::freeze_for_commit(
                        self@,
                        self@,
                        lbl,
                    )) by {
                        reveal(CachedJournal::State::freeze_for_commit);
                    }
                    assert(CachedJournal::State::next_by(
                        self@,
                        self@,
                        lbl,
                        CachedJournal::Step::freeze_for_commit(),
                    ));
                    assert(CachedJournal::State::next(self@, self@, lbl));
                }
            }
            CleanForCommitResult::Frozen{frozen_journal}
        } else {
            CleanForCommitResult::NeedsFlush{}
        }
    }

    pub exec fn discard_old(&mut self, boundary_lsn: ILsn, total_aus: IAU)
    requires
        old(self).wf(),
        old(self).index_ready(),
        old(self).index_aus_bounded(total_aus),
        old(self).seq_start() <= boundary_lsn <= old(self).marshalled_seq_end(),
    ensures
        self.wf(),
        self.index_ready(),
        self.index_aus_bounded(total_aus),
        self.journal_alloc == old(self).journal_alloc,
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
                    require_end: old(self)@.seq_end(),
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
        let ghost old_bounds = status.au_page_bounds@;
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
        status.clean_watermark_au_page_bounds = Ghost(
            status.clean_watermark_au_page_bounds@.restrict(new_lsn_au_index_for_bounds.values()),
        );

        if old_clean < boundary_lsn {
            status.clean_watermark_lsn = boundary_lsn;
        }
        self.snapshot.boundary_lsn = boundary_lsn;
        self.snapshot.freshest_rec =
            if boundary_lsn == old_index_seq_end { None } else { old_freshest_rec };
        if boundary_lsn == old_index_seq_end {
            self.snapshot.first = 0;
        } else {
            let (first_addr, _) = status.lsn_addr_index.lookup_lsn_with_segment_end(boundary_lsn);
            self.snapshot.first = first_addr.au;
        }
        self.status = Some(status);

        proof {
            assert(pre_journal.status.unwrap().lsn_au_index == lsn_addr_index_to_au_index(old_index));
            discard_preserves_addr_bounds(old_index, old_bounds, boundary_lsn as nat);
            assert(self.status.unwrap().lsn_addr_index@
                == lsn_addr_index_discard_up_to(old_index, boundary_lsn as nat));
            assert(new_lsn_au_index_for_bounds
                == lsn_au_index_discard_up_to(lsn_addr_index_to_au_index(old_index), boundary_lsn as nat));
            assert forall |a: Address|
                #[trigger] self.status.unwrap().lsn_addr_index@.values().contains(a)
                implies self.status.unwrap().au_page_bounds@.contains_key(a.au)
                    && a.page <= self.status.unwrap().au_page_bounds@[a.au] by {
                assert(lsn_addr_index_discard_up_to(old_index, boundary_lsn as nat).values().contains(a));
            }
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
            assert(self@.status.unwrap().lsn_au_index =~= new_lsn_au_index) by {
                assert(self@.status.unwrap().lsn_au_index
                    == lsn_addr_index_to_au_index(self.status.unwrap().lsn_addr_index@));
                assert(self.status.unwrap().lsn_addr_index@
                    == lsn_addr_index_discard_up_to(old_index, boundary_lsn as nat));
                lsn_addr_index_to_au_index_discard(old_index, boundary_lsn as nat);
            }
            crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to_ensures(
                pre_journal.status.unwrap().lsn_au_index,
                boundary_lsn as nat,
            );
            assert(new_lsn_au_index <= pre_journal.status.unwrap().lsn_au_index);
            assert(self@.status.unwrap().lsn_au_index.values()
                <= pre_journal.status.unwrap().lsn_au_index.values()) by {
                assert forall |au: AU| #[trigger]
                    self@.status.unwrap().lsn_au_index.values().contains(au)
                    implies pre_journal.status.unwrap().lsn_au_index.values().contains(au) by {
                    let lsn = choose |lsn: LSN|
                        self@.status.unwrap().lsn_au_index.contains_key(lsn)
                            && self@.status.unwrap().lsn_au_index[lsn] == au;
                    assert(new_lsn_au_index.contains_key(lsn));
                    assert(pre_journal.status.unwrap().lsn_au_index.contains_key(lsn));
                    assert(pre_journal.status.unwrap().lsn_au_index[lsn] == au);
                }
            }
            assert(self.index_aus_bounded(total_aus));
            assert(self@.status.unwrap().au_page_bounds
                == pre_journal.status.unwrap().au_page_bounds.restrict(new_lsn_au_index.values()));
            assert(self@.status.unwrap().clean_watermark_au_page_bounds
                == pre_journal.status.unwrap().clean_watermark_au_page_bounds.restrict(
                    new_lsn_au_index.values(),
                ));
            assert(self@.status.unwrap().clean_watermark_lsn
                == if (boundary_lsn as nat) > pre_journal.clean_watermark() {
                    boundary_lsn as nat
                } else {
                    pre_journal.clean_watermark()
                });
            assert(self@.status.unwrap().unmarshalled_tail
                == pre_journal.status.unwrap().unmarshalled_tail.bounded_discard(
                    boundary_lsn as nat,
                ));
            reveal(CachedJournal::State::next_by);
            reveal(CachedJournal::State::next);
            assert(CachedJournal::State::discard_old(
                pre_journal,
                self@,
                lbl,
            )) by {
                reveal(CachedJournal::State::discard_old);
            }
            assert(CachedJournal::State::next_by(
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
        self.basic_wf(),
        self.wf(),
        self.index_ready(),
        cache.wf(),
        cache.valid_load_handles_preserved(*old(cache)),
        cache.valid_writeback_handles_preserved(*old(cache)),
        self.seq_start() == old(self).seq_start(),
        self.seq_end() == old(self).seq_end(),
        old(self).clean_watermark() <= self.clean_watermark(),
        self.clean_watermark() <= old(self).marshalled_seq_end(),
        self.marshalled_seq_end() == old(self).marshalled_seq_end(),
        old(self).clean_watermark() == self.clean_watermark() ==> self@ == old(self)@,
        self.journal_alloc == old(self).journal_alloc,
        self.journal_alloc.i() == old(self).journal_alloc.i(),
        self@.status.unwrap().lsn_au_index == old(self)@.status.unwrap().lsn_au_index,
        match out {
            BeginWritebackForTargetResult::Acquired{request, flushed_domain} => {
                &&& target_lsn as nat > old(self).clean_watermark()
                &&& old(self)@.status.unwrap().lsn_au_index.values().contains(request.addr@.au)
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
        let old_clean = self.status.as_ref().unwrap().clean_watermark_lsn;
        let ghost pre = self@;
        let ghost pre_index = self.status.unwrap().lsn_addr_index@;
        let ghost pre_cache = cache@;
        let ghost pre_cache_impl = *cache;
        let ghost pre_alloc_au = self.alloc_au();
        let ghost pre_journal_alloc = self.journal_alloc;
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
                assert(self.journal_alloc == old(self).journal_alloc);
                assert(self.journal_alloc.i() == old(self).journal_alloc.i());
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
                self@.status.unwrap().clean_watermark_au_page_bounds
                    == pre.status.unwrap().clean_watermark_au_page_bounds,
                self.journal_alloc == pre_journal_alloc,
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
                assert(index@ == pre_index);
                assert(pre_index.contains_key(clean_scan as nat));
                assert(pre_index[clean_scan as nat] == addr@);
                assert(pre_index.values().contains(addr@));
                lsn_addr_index_to_au_index_values_match(pre_index);
                to_aus_domain(pre_index.values());
                assert(to_aus(pre_index.values()).contains(addr@.au));
                assert(pre.status.unwrap().lsn_au_index == lsn_addr_index_to_au_index(pre_index));
                assert(pre.status.unwrap().lsn_au_index.values().contains(addr@.au));
            }
            let ghost cache_before = cache@;
            let ghost cache_before_impl = *cache;
            match cache.begin_writeback(&addr) {
                WritebackAcquireResult::Acquired{handle} => {
                    if clean_commit > old_clean {
                        let mut dummy: Option<IJournalStatus> = None;
                        core::mem::swap(&mut self.status, &mut dummy);
                        let old_status = dummy.unwrap();
                        let ghost flushed_domain_for_clean =
                            flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
                        let ghost clean_bounds = old_status.clean_watermark_au_page_bounds@
                            .union_prefer_right(
                                old_status.au_page_bounds@.restrict(to_aus(flushed_domain_for_clean)),
                            );
                        let status = IJournalStatus{
                            clean_watermark_lsn: clean_commit,
                            clean_watermark_au_page_bounds: Ghost(clean_bounds),
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
                            let ghost flushed_domain_for_clean =
                                flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
                            let ghost flushed_lsns =
                                Set::new(|lsn: LSN| old_clean as nat <= lsn < clean_commit as nat);
                            let ghost clean_lbl = CachedJournal::Label::ObserveCleanAUs{
                                aus: to_aus(flushed_domain_for_clean),
                            };
                            lsn_addr_index_to_au_index_restrict_values_match(pre_index, flushed_lsns);
                            assert(flushed_domain_for_clean == pre_index.restrict(flushed_lsns).values());
                            assert(pre.status.unwrap().lsn_au_index == lsn_addr_index_to_au_index(pre_index));
                            assert(clean_lbl->aus
                                =~= pre.status.unwrap().lsn_au_index.restrict(flushed_lsns).values());
                            assert(self@.status.unwrap().clean_watermark_au_page_bounds
                                == pre.status.unwrap().clean_watermark_au_page_bounds
                                    .union_prefer_right(
                                        pre.status.unwrap().au_page_bounds.restrict(clean_lbl->aus),
                                    ));
                            assert(CachedJournal::State::advance_watermark(
                                pre,
                                self@,
                                clean_lbl,
                                clean_commit as nat,
                            )) by {
                                reveal(CachedJournal::State::advance_watermark);
                            }
                            assert(CachedJournal::State::next_by(
                                pre,
                                self@,
                                clean_lbl,
                                CachedJournal::Step::advance_watermark(clean_commit as nat)
                            ));
                        } else {
                            assert(self@ == pre);
                        }
                        assert(self.journal_alloc == old(self).journal_alloc);
                        assert(self.journal_alloc.i() == old(self).journal_alloc.i());
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
                        assert(to_aus(set![addr@]) =~= set![addr@.au]) by {
                            assert forall |au: AU| #[trigger] to_aus(set![addr@]).contains(au)
                                implies set![addr@.au].contains(au) by {
                                to_aus_domain(set![addr@]);
                            }
                            assert forall |au: AU| #[trigger] set![addr@.au].contains(au)
                                implies to_aus(set![addr@]).contains(au) by {
                                assert(set![addr@].contains(addr@));
                                to_aus_domain(set![addr@]);
                            }
                        }
                        assert(Cache::State::next(
                            cache@,
                            cache@,
                            Cache::Label::EvictableCheck{aus: to_aus(set![addr@])},
                        ));
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
                                    to_aus(flushed_after).contains(a.au) && #[trigger] cache@.lookup_map.contains_key(a)
                                    implies {
                                        &&& cache@.entries[cache@.lookup_map[a]] is Filled
                                        &&& cache@.status_map[cache@.lookup_map[a]] is Clean
                                    } by {
                                    assert(flushed_after == range_after.values());
                                    if to_aus(flushed_before).contains(a.au) {
                                        assert(cache_evictable_prop(cache@, flushed_before));
                                    } else {
                                        let flushed_addr = choose |flushed_addr: Address|
                                            #[trigger] flushed_after.contains(flushed_addr)
                                            && flushed_addr.au == a.au;
                                        let l = choose |l: LSN| #![auto]
                                            range_after.contains_key(l) && range_after[l] == flushed_addr;
                                        if l < clean_commit as nat {
                                            assert(range_before.contains_key(l));
                                            assert(flushed_before.contains(flushed_addr));
                                            to_aus_domain(flushed_before);
                                            assert(to_aus(flushed_before).contains(a.au));
                                            assert(false);
                                        }
                                        assert(clean_commit as nat <= l < seg_end as nat);
                                        assert(range_seg.contains_key(l));
                                        assert(range_seg[l] == flushed_addr);
                                        assert(range_seg.values().contains(flushed_addr));
                                        assert(seg_values == range_seg.values());
                                        assert(seg_values.contains(flushed_addr));
                                        assert(flushed_addr == addr@);
                                        assert(a.au == addr@.au);
                                        assert(cache_evictable_prop(cache@, set![addr@]));
                                        to_aus_domain(set![addr@]);
                                        assert(to_aus(set![addr@]).contains(a.au));
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

        if clean_commit > old_clean {
            let mut dummy: Option<IJournalStatus> = None;
            core::mem::swap(&mut self.status, &mut dummy);
            let old_status = dummy.unwrap();
            let ghost flushed_domain_for_clean =
                flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
            let ghost clean_bounds = old_status.clean_watermark_au_page_bounds@
                .union_prefer_right(
                    old_status.au_page_bounds@.restrict(to_aus(flushed_domain_for_clean)),
                );
            let status = IJournalStatus{
                clean_watermark_lsn: clean_commit,
                clean_watermark_au_page_bounds: Ghost(clean_bounds),
                ..old_status
            };
            dummy = Some(status);
            core::mem::swap(&mut self.status, &mut dummy);
            proof {
                let ghost flushed_domain = flush_domain_from_index_range(pre_index, old_clean as nat, clean_commit as nat);
                let ghost flushed_lsns =
                    Set::new(|lsn: LSN| old_clean as nat <= lsn < clean_commit as nat);
                let ghost clean_lbl = CachedJournal::Label::ObserveCleanAUs{
                    aus: to_aus(flushed_domain),
                };
                lsn_addr_index_to_au_index_restrict_values_match(pre_index, flushed_lsns);
                assert(flushed_domain == pre_index.restrict(flushed_lsns).values());
                assert(pre.status.unwrap().lsn_au_index == lsn_addr_index_to_au_index(pre_index));
                assert(clean_lbl->aus
                    =~= pre.status.unwrap().lsn_au_index.restrict(flushed_lsns).values());
                assert(self@.status.unwrap().clean_watermark_au_page_bounds
                    == pre.status.unwrap().clean_watermark_au_page_bounds
                        .union_prefer_right(
                            pre.status.unwrap().au_page_bounds.restrict(clean_lbl->aus),
                        ));
                assert(CachedJournal::State::advance_watermark(
                    pre,
                    self@,
                    clean_lbl,
                    clean_commit as nat,
                )) by {
                    reveal(CachedJournal::State::advance_watermark);
                }
                assert(CachedJournal::State::next_by(
                    pre,
                    self@,
                    clean_lbl,
                    CachedJournal::Step::advance_watermark(clean_commit as nat)
                ));
            }
        } else {
            proof {
                assert(self@ == pre);
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
            assert(self.journal_alloc == old(self).journal_alloc);
            assert(self.journal_alloc.i() == old(self).journal_alloc.i());
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
