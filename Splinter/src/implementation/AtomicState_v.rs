// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::{multiset::*};

use crate::spec::KeyType_t::Key;
use crate::spec::Messages_t::Value;
use crate::spec::MapSpec_t::{ID, Input, MapSpec, Reply, Request, SyncReqId};
use crate::spec::AsyncDisk_t::{AU, Address, DiskRequest, DiskResponse, RawPage};
use crate::abstract_system::AbstractCrashAwareMap_v::Ephemeral;
use crate::spec::TotalKMMap_t::TotalKMMap;
use crate::implementation::DiskLayout_v::{DiskLayout, spec_superblock_addr};
use crate::implementation::StoreImpl_v::raw_page_to_store_kmmap;
use crate::implementation::SuperblockTypes_v::Superblock;
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedJournal_v::{CachedJournal, JournalSnapshot};
use crate::journal::LinkedJournal_v::{JournalRecord};
use crate::marshalling::IJournalRecordFormat_v::IJournalRecordFormat;
use crate::marshalling::Marshalling_v::Marshal;

use crate::abstract_system::AbstractMap_v::AbstractMap;
use crate::abstract_system::StampedMap_v::{LSN, StampedMap, empty};
use crate::abstract_system::MsgHistory_v::MsgHistory;

verus! {

pub enum RecoveryState {
    // Haven't done anything; don't know anything. Better not handle user IO.
    Begin,
    // We've sent the superblock read request; better not send any more! Still can't do user IO.
    AwaitingSuperblock,
    // now we can load the journal pages into the cache
    SuperblockAvailable,
    // journal index is built, time to update map with journal records
    JournalIndexComplete,
    // System can now operate
    RecoveryComplete,
}

// This is state we need in addition to the in-flight state hiding inside AbstractCrashAwareMap.
pub struct InflightInfo {
    pub frozen_store: StampedMap,
    pub store_ptr: Option<Address>,
    pub journal_version: LSN,
    pub req_id: ID,
}

#[verifier::ext_equal]
pub struct AtomicState {
    pub recovery_state: RecoveryState,
    
    pub cache: Cache::State,
    // bookkeeping structure to route disk responses back to cache
    pub outstanding_cache_reqs: Map<ID, Address>,

    // executable map state
    pub store: Ephemeral,
    // pointer to persistent store image on disk
    pub persistent_store_ptr: Option<Address>,

    // msg history seq start
    pub journal: CachedJournal::State,
    pub persistent_journal_seq_end: LSN,

    // tells us what we can bump persistent_version when the disk response comes back.
    pub in_flight: Option<InflightInfo>,

    // maps each syncreq id with a version
    pub sync_req_map: Map<SyncReqId, nat>, 
}

pub enum DiskEvent{
    // superblock read 
    InitiateRecovery{req_id: ID},
    SuperblockRecovery{req_id: ID, raw_page: RawPage},
    // superblock write
    ExecuteSyncBegin{req_id: ID, req: DiskRequest, frozen_journal: JournalSnapshot,
        frozen_store: StampedMap, store_ptr: Option<Address>,
        frozen_seq_end: LSN},
    ExecuteSyncEnd{discard_addrs: Set<Address>},
    // other I/Os
    CacheIOBegin{req_map: Map<ID, DiskRequest>},
    CacheIOEnd{resp_map: Map<ID, DiskResponse>},
}

pub enum InternalEvent{
    StoreInternal{},
    CacheInternal{},
    JournalMarshallStep{addr: Address, raw_page: RawPage},
    AckJournalFlush{flushed_domain: Set<Address>},
    LoadMap{reads: Map<Address, RawPage>},
    JournalRecovery{reads: Map<Address, RawPage>},
    MapRecovery{records: MsgHistory, reads: Map<Address, RawPage>, addr: Address},
    RecoveryComplete{},
}

// labels
pub enum ProgramEvent{
    NoOp{},
    Put{puts: MsgHistory},
    Query{end_lsn: LSN, key: Key, value: Value},
}

pub open spec fn valid_request_reply_pair(req: Request, reply: Reply) -> bool 
{
    &&& req.id == reply.id
    &&& req.input is QueryInput <==> reply.output is QueryOutput
    &&& req.input is PutInput <==> reply.output is PutOutput
    &&& req.input is NoopInput <==> reply.output is NoopOutput
}

pub open spec(checked) fn to_map_label(req: Request, reply: Reply) -> MapSpec::Label 
    recommends valid_request_reply_pair(req, reply)
{
    let input = req.input;
    let output = reply.output;
    match req.input {
        Input::QueryInput{..} => { MapSpec::Label::Query {input, output} },
        Input::PutInput{..} => { MapSpec::Label::Put {input, output} },
        Input::NoopInput{} => { MapSpec::Label::Noop {input, output} },
    }
}

pub open spec fn map_to_multiset<K,V>(m: Map<K,V>) -> Multiset<(K,V)>
{
    m.kv_pairs().to_multiset()
}

pub open spec fn raw_page_to_record(raw_page: RawPage) -> (out: JournalRecord)
{
    let fmt = IJournalRecordFormat::spec_new();
    if fmt.parsable(raw_page) {
        fmt.parse(raw_page).view()
    } else {
        arbitrary()
    }
}

pub open spec fn to_journal_records(reads: Map<Address, RawPage>) -> Map<Address, JournalRecord>
{
    Map::new(
        |addr| reads.contains_key(addr), 
        |addr| raw_page_to_record(reads[addr])
    )
}

pub open spec fn journal_marshall_labels(addr: Address, raw_page: RawPage) -> (CachedJournal::Label, Cache::Label)
{
    let writes = Map::<Address, RawPage>::empty().insert(addr, raw_page);
    (
        CachedJournal::Label::JournalMarshal{writes: to_journal_records(writes)},
        Cache::Label::Access{reads: Map::<Address, RawPage>::empty(), writes},
    )
}

pub open spec fn to_store_maps(reads: Map<Address, RawPage>) -> Map<Address, TotalKMMap>
{
    Map::new(
        |addr| reads.contains_key(addr),
        |addr| raw_page_to_store_kmmap(reads[addr])
    )
}

pub open spec fn journal_addrs(journal: CachedJournal::State) -> Set<Address>
{
    if journal.status is Some {
        journal.status.unwrap().lsn_addr_index.values()
    } else {
        set![]
    }
}

pub open spec fn store_ptr_disjoint_from_journal(store_ptr: Option<Address>, journal: CachedJournal::State) -> bool
{
    match store_ptr {
        None => true,
        Some(addr) => !journal_addrs(journal).contains(addr),
    }
}

impl AtomicState {
    pub open spec fn client_ready(self) -> bool
    {
        &&& self.recovery_state is RecoveryComplete
        &&& self.journal.status is Some
    }

    // Duck tape: directly accessing submodule state...
    pub open spec(checked) fn ephemeral_map(self) -> StampedMap
        recommends self.store is Known
    {
        self.store->Known_v.stamped_map
    }

    pub open spec fn store_in_flight(self) -> Option<StampedMap>
    {
        if self.in_flight is Some {
            Some(self.in_flight.unwrap().frozen_store)
        } else {
            None
        }
    }

    pub open spec fn store_addrs(self) -> Set<Address>
    {
        let persistent =
            if self.persistent_store_ptr is Some {
                set!{self.persistent_store_ptr.unwrap()}
            } else {
                set![]
            };
        let inflight =
            if self.in_flight is Some && self.in_flight.unwrap().store_ptr is Some {
                set!{self.in_flight.unwrap().store_ptr.unwrap()}
            } else {
                set![]
            };
        persistent + inflight
    }

    pub open spec fn wf(self) -> bool {
        &&& self.cache.inv()
        &&& self.outstanding_cache_reqs.is_injective() // at most 1 outstanding req per addr
        &&& !self.outstanding_cache_reqs.contains_value(spec_superblock_addr()) // sb ops do not go through the cache
        &&& self.outstanding_cache_reqs.values() <= self.cache.lookup_map.dom()

        &&& self.client_ready() ==> {
            &&& self.journal.wf()
            &&& self.store is Known
            &&& self.journal.seq_end() == self.ephemeral_map().seq_end
            &&& self.journal.snapshot.boundary_lsn <= self.journal.seq_start()
            &&& self.journal.seq_start() <= self.persistent_journal_seq_end
            &&& self.persistent_journal_seq_end <= self.journal.seq_end()
            &&& if let Some(ifl) = self.in_flight {
                &&& self.journal.snapshot.boundary_lsn <= ifl.frozen_store.seq_end
                &&& ifl.frozen_store.seq_end <= ifl.journal_version
                &&& ifl.journal_version <= self.journal.seq_end()
            } else { true }
        }
    }

    // this is process init, which should do filesystem recovery before operation
    pub open spec fn init(cache_slots: nat) -> Self
    {
        AtomicState{
            recovery_state: RecoveryState::Begin,
            cache: Cache::State::empty(cache_slots),
            outstanding_cache_reqs: Map::empty(),
            // initialized later on recovery
            journal: arbitrary(),
            store: Ephemeral::Unknown,
            persistent_store_ptr: None,
            persistent_journal_seq_end: arbitrary(),
            in_flight: None,
            sync_req_map: Map::empty(),
        }
    }

    pub open spec fn execute_noop(pre: Self, post: Self, req: Request, reply: Reply) -> bool
    {
        &&& post == pre
    }

    pub open spec fn execute_put(pre: Self, post: Self, req: Request, reply: Reply, records: MsgHistory) -> bool
    {
        &&& pre.store is Known
        &&& post.store is Known
        &&& AbstractMap::State::next(pre.store->Known_v, post.store->Known_v, AbstractMap::Label::PutLabel{puts: records})
        &&& CachedJournal::State::next(pre.journal, post.journal, CachedJournal::Label::Put{messages: records})
        &&& post == Self{
                journal: post.journal,
                store: post.store,
                ..pre
            }
    }

    pub open spec fn execute_query(pre: Self, post: Self, req: Request, reply: Reply, end_lsn: LSN, key: Key, value: Value) -> bool
    {
        &&& req.input is QueryInput
        &&& reply.output is QueryOutput
        &&& key == req.input.arrow_QueryInput_key()
        &&& value == reply.output.arrow_QueryOutput_value()
        &&& pre.store is Known
        &&& post.store is Known
        &&& AbstractMap::State::next(pre.store->Known_v, post.store->Known_v, AbstractMap::Label::QueryLabel{end_lsn, key, value})
        &&& post == Self{
                store: post.store,
                ..pre
            }
    }

    pub open spec fn execute_transition(pre: Self, post: Self, req: Request, reply: Reply, event: ProgramEvent) -> bool
    {
        &&& pre.client_ready()
        &&& valid_request_reply_pair(req, reply)
        &&& match req.input {
            Input::NoopInput{} => event is NoOp,
            Input::QueryInput{..} => event is Query,
            Input::PutInput{..} => event is Put,
        }
        &&& match event {
            ProgramEvent::NoOp{} => Self::execute_noop(pre, post, req, reply),
            ProgramEvent::Put{puts} => Self::execute_put(pre, post, req, reply, puts),
            ProgramEvent::Query{end_lsn, key, value} => Self::execute_query(pre, post, req, reply, end_lsn, key, value)
        }
        &&& post.wf()
    }

    pub open spec fn store_internal(pre: Self, post: Self) -> bool
    {
        &&& pre.client_ready()
        &&& pre.store is Known
        &&& post.store is Known
        &&& AbstractMap::State::next(pre.store->Known_v, post.store->Known_v, AbstractMap::Label::InternalLabel)
        &&& post == Self{
            store: post.store,
            ..pre
        }
    }

    pub open spec fn journal_marshall_step(pre: Self, post: Self, addr: Address, raw_page: RawPage) -> bool
    {
        let (journal_lbl, cache_lbl) = journal_marshall_labels(addr, raw_page);
        &&& pre.client_ready()
        &&& !pre.store_addrs().contains(addr)
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& post == Self{
            cache: post.cache,
            journal: post.journal,
            ..pre
        }
    }

    pub open spec fn accept_sync_request(pre: Self, post: Self, sync_req_id: SyncReqId) -> bool
    {
        &&& pre.client_ready()
        // &&& !pre.sync_req_map.contains_key(sync_req_id) // true by system invariant
        &&& post == Self{
            sync_req_map: pre.sync_req_map.insert(sync_req_id, pre.ephemeral_map().seq_end as nat),
            ..pre
        }
    }

    pub open spec fn deliver_sync_reply(pre: Self, post: Self, sync_req_id: SyncReqId) -> bool
    {
        &&& pre.client_ready()
        // The request with this id was once made and is still outstanding
        &&& pre.sync_req_map.contains_key(sync_req_id)
        // The request has been satisfied by a disk sync that got completed
        &&& pre.sync_req_map[sync_req_id] <= pre.persistent_journal_seq_end
        &&& post == Self{
            sync_req_map: pre.sync_req_map.remove(sync_req_id),
            ..pre
        }
    }

    pub open spec fn initiate_recovery(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>, req_id: ID) -> bool
    {
        // Haven't started operating yet
        &&& pre.recovery_state is Begin
        // NOTE: ignores id for now cause we don't use it yet
        &&& reqs == Multiset::empty().insert((req_id, DiskRequest::ReadReq{from: spec_superblock_addr()}))
        &&& resps.is_empty()
        &&& post == Self{ recovery_state: RecoveryState::AwaitingSuperblock, ..pre }
    }

    pub open spec fn superblock_recovery(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>, req_id: ID, raw_page: RawPage) -> bool
    {
        &&& pre.recovery_state is AwaitingSuperblock // can prove this by invariant
        &&& reqs.is_empty()
        &&& resps == Multiset::empty().insert((req_id, DiskResponse::ReadResp{data: raw_page}))
        // &&& valid_checksum(raw_page) 
        &&& {
            let superblock = DiskLayout::spec_new().spec_parse(raw_page);
            &&& post == Self{
                recovery_state: RecoveryState::SuperblockAvailable,
                journal: CachedJournal::State{
                    snapshot: superblock.journal,
                    status: None,
                },
                store: post.store,
                persistent_store_ptr: superblock.store_ptr,
                persistent_journal_seq_end: arbitrary(), // do not know yet
                in_flight: None,
                sync_req_map: Map::empty(),
                ..pre
            }
        }
    }

    pub open spec fn journal_recovery(pre: Self, post: Self, reads: Map<Address, RawPage>) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};
        let journal_lbl = CachedJournal::Label::LoadIndex{reads: to_journal_records(reads)};

        &&& pre.recovery_state is SuperblockAvailable
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)
        &&& post == Self{
            recovery_state: RecoveryState::JournalIndexComplete,
            cache: post.cache,
            journal: post.journal,
            ..pre
        }
    }

    pub open spec fn load_map(pre: Self, post: Self, reads: Map<Address, RawPage>) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
        let boundary_lsn = pre.journal.snapshot.boundary_lsn;

        &&& (pre.recovery_state is SuperblockAvailable || pre.recovery_state is JournalIndexComplete)
        &&& pre.store is Unknown
        &&& if pre.persistent_store_ptr is None {
            &&& reads == Map::<Address, RawPage>::empty()
            &&& post.cache == pre.cache
            &&& post.store is Known
            &&& post.store->Known_v.stamped_map.value == TotalKMMap::empty()
            &&& post.store->Known_v.stamped_map.seq_end == boundary_lsn
        } else {
            let addr = pre.persistent_store_ptr.unwrap();
            &&& reads.contains_key(addr)
            &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
            &&& post.store is Known
            &&& post.store->Known_v.stamped_map.value == to_store_maps(reads)[addr]
            &&& post.store->Known_v.stamped_map.seq_end == boundary_lsn
        }
        &&& post == Self{
            cache: post.cache,
            store: post.store,
            ..pre
        }
    }

    // update map to the journal
    pub open spec fn map_recovery(pre: Self, post: Self, records: MsgHistory, reads: Map<Address, RawPage>, addr: Address) -> bool
    {
        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};

        &&& pre.recovery_state is JournalIndexComplete
        &&& pre.store is Known
        &&& post.store is Known
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& reads.contains_key(addr)
        &&& {
            let journal_reads = to_journal_records(reads);
            let journal_records = journal_reads[addr].message_seq.maybe_discard_old(pre.journal.snapshot.boundary_lsn);
            let map_records = journal_reads[addr].message_seq.maybe_discard_old(pre.store->Known_v.stamped_map.seq_end);
            let journal_lbl = CachedJournal::Label::ReadForRecovery{messages: journal_records, reads: journal_reads};
            &&& records == map_records
            &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)
        }
        &&& AbstractMap::State::next(pre.store->Known_v, post.store->Known_v, AbstractMap::Label::PutLabel{puts: records})

        &&& post == Self{
            cache: post.cache,
            journal: post.journal,
            store: post.store,
            ..pre
        }
    }

    pub open spec fn recovery_complete(pre: Self, post: Self) -> bool
    {
        let end_lsn = pre.ephemeral_map().seq_end;
        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn};
        
        &&& pre.recovery_state is JournalIndexComplete
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)
        &&& post == Self {
            recovery_state: RecoveryState::RecoveryComplete,
            persistent_journal_seq_end: end_lsn,
            ..pre
        }
    }

    pub open spec fn cache_internal(pre: Self, post: Self) -> bool
    {
        &&& Cache::State::next(pre.cache, post.cache, Cache::Label::Internal{})
        &&& post == Self {
            cache: post.cache,
            ..pre
        }
    }

    pub open spec fn acknowledge_flushed_journal_pages(
        pre: Self,
        post: Self,
        flushed_domain: Set<Address>,
    ) -> bool
    {
        let cache_lbl = Cache::Label::EvictableCheck{addrs: flushed_domain};
        let journal_lbl = CachedJournal::Label::JournalFlush{flushed_domain};

        &&& pre.client_ready()
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)
        &&& post == Self{
            cache: post.cache,
            journal: post.journal,
            ..pre
        }
    }

    pub open spec fn cache_io_begin(pre: Self, post: Self, req_map: Map<ID, DiskRequest>, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        let updated_outstanding_cache_reqs = Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
        let new_outstanding_cache_reqs = pre.outstanding_cache_reqs.union_prefer_right(updated_outstanding_cache_reqs);

        &&& map_to_multiset(req_map) == reqs
        &&& resps.is_empty()
        // TODO: any domain restriction can be part of the invariant and not an enabling condition
        // &&& req_map.dom().disjoint(pre.outstanding_cache_reqs.dom())
        &&& Cache::State::next(pre.cache, post.cache, Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()})
        &&& post == Self {
            cache: post.cache,
            outstanding_cache_reqs: new_outstanding_cache_reqs,
            ..pre
        }
    }

    pub open spec fn cache_io_end(pre: Self, post: Self, resp_map: Map<ID, DiskResponse>, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        let new_outstanding_cache_reqs = pre.outstanding_cache_reqs.remove_keys(resp_map.dom());
        let finished_cache_reqs = pre.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
        let cache_resps = Map::new(|addr| finished_cache_reqs.contains_key(addr), |addr| resp_map[finished_cache_reqs[addr]]);

        &&& map_to_multiset(resp_map) == resps
        &&& reqs.is_empty()

        &&& Cache::State::next(pre.cache, post.cache, Cache::Label::DiskOps{requests: set![], responses: cache_resps})
        &&& post == Self {
            cache: post.cache,
            outstanding_cache_reqs: new_outstanding_cache_reqs,
            ..pre
        }
    }

    // superblock sync
    pub open spec fn execute_sync_begin(pre: Self, post: Self, 
        req_id: ID, req: DiskRequest, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>,
        frozen_store: StampedMap, store_ptr: Option<Address>,
        frozen: JournalSnapshot, frozen_seq_end: LSN) -> bool
    {
        let journal_lbl = CachedJournal::Label::FreezeForCommit{frozen, frozen_seq_end};

        let sb = Superblock{
            store_ptr,
            journal: frozen,
        };

        // superblock writes
        let inflight_info = InflightInfo{
            frozen_store,
            store_ptr,
            journal_version: frozen_seq_end,
            req_id
        };

        &&& pre.client_ready()
        &&& pre.in_flight is None
        &&& pre.store is Known
        &&& post.store == pre.store
        &&& post.in_flight is Some

        // CachedJournal::freeze_for_commit is going to point at some frozen freshest_rec, and
        // needs to verify that the highest lsn recorded in that freshest_rec matches
        // frozen_seq_end. You might think "hey, just have an index that remembers what the last
        // lsn is in the last marshalled page", but we might want to reach back some depth into the
        // journal (to defer writing dirty journal pages in the case where we're updating an
        // ancient map and we haven't been asked to sync for a week). You might think "hey, we
        // *have* the lsn_addr_index, just query that for the high end of the range!" But the
        // ultimate system will have an au_addr_index, not a page-granularity index, and we want to
        // be able to push a single journal page at a time (in the case where we're syncing
        // frequently and we don't want to burn an AU on a single journal record).
        // So, the journal needs to read this page from the cache.
        // &&& Cache::State::next(pre.cache, post.cache, cache_lbl1)
        // // checks that frozen journal has been flushed
        // &&& Cache::State::next(pre.cache, post.cache, cache_lbl2)
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)

        &&& req is WriteReq
        &&& req->to == spec_superblock_addr()
        &&& DiskLayout::spec_new().spec_parse(req->data) == sb
        &&& reqs == Multiset::singleton((req_id, req))
        &&& resps.is_empty()
        &&& post == Self{
            store: post.store,
            journal: post.journal,
            in_flight: Some(inflight_info),
            .. pre}
    }

    pub open spec fn execute_sync_end(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>,
        discard_addrs: Set<Address>) -> bool
    {
        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn: pre.in_flight.unwrap().frozen_store.seq_end,
            require_end: post.ephemeral_map().seq_end, // requires journal to still line up with ephemeral map, might not be needed
            discard_addrs,
        };
        let cache_lbl = Cache::Label::EvictableCheck{addrs: discard_addrs};

        &&& pre.client_ready()
        &&& pre.in_flight is Some 
        &&& reqs.is_empty()
        &&& resps == Multiset::singleton((pre.in_flight.unwrap().req_id, DiskResponse::WriteResp{}))

        &&& pre.store is Known
        &&& post.store == pre.store
        // journal truncates if necessary
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)
        // cache checks that discarded pages are now evictable
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)

        &&& post == Self{
            store: post.store,
            journal: post.journal,
            cache: post.cache,
            persistent_store_ptr: pre.in_flight.unwrap().store_ptr,
            persistent_journal_seq_end: pre.in_flight.unwrap().journal_version,
            in_flight: None,
            ..pre
        }
    }

    pub open spec fn disk_transition(pre: Self, post: Self, disk_event: DiskEvent, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        match disk_event {
            DiskEvent::InitiateRecovery{req_id} => Self::initiate_recovery(pre, post, reqs, resps, req_id),
            DiskEvent::SuperblockRecovery{req_id, raw_page} => Self::superblock_recovery(pre, post, reqs, resps, req_id, raw_page),
            DiskEvent::ExecuteSyncBegin{req_id, req, frozen_journal, frozen_store, store_ptr, frozen_seq_end}
                => Self::execute_sync_begin(pre, post, req_id, req, reqs, resps, frozen_store, store_ptr, frozen_journal, frozen_seq_end),
            DiskEvent::ExecuteSyncEnd{discard_addrs} => Self::execute_sync_end(pre, post, reqs, resps, discard_addrs),
            DiskEvent::CacheIOBegin{req_map} => Self::cache_io_begin(pre, post, req_map, reqs, resps),
            DiskEvent::CacheIOEnd{resp_map} => Self::cache_io_end(pre, post, resp_map, reqs, resps),
        }
    }

    pub open spec fn internal_transitions(pre: Self, post: Self, internal_event: InternalEvent) -> bool
    {
        match internal_event {
            InternalEvent::StoreInternal{} => Self::store_internal(pre, post),
            InternalEvent::CacheInternal{} => Self::cache_internal(pre, post),
            InternalEvent::JournalMarshallStep{addr, raw_page} =>
                Self::journal_marshall_step(pre, post, addr, raw_page),
            InternalEvent::AckJournalFlush{flushed_domain} =>
                Self::acknowledge_flushed_journal_pages(pre, post, flushed_domain),
            InternalEvent::LoadMap{reads} => Self::load_map(pre, post, reads),
            InternalEvent::JournalRecovery{reads} => Self::journal_recovery(pre, post, reads),
            InternalEvent::MapRecovery{records, reads, addr} => Self::map_recovery(pre, post, records, reads, addr),
            InternalEvent::RecoveryComplete{} => Self::recovery_complete(pre, post),
        }
    }

    pub open spec(checked) fn in_flight_sb(self) -> Superblock
    recommends
        self.wf(),
        self.client_ready(),
        self.in_flight is Some,
        self.in_flight.unwrap().journal_version != self.in_flight.unwrap().frozen_store.seq_end
        ==> ({
            let ifl_journal_version = self.in_flight.unwrap().journal_version;
            let index = self.journal.status.unwrap().lsn_addr_index;
            &&& ifl_journal_version > 0 
            &&& index.contains_key((ifl_journal_version - 1) as nat)
        }),
    {
        let inf = self.in_flight.unwrap();
        let index = self.journal.status.unwrap().lsn_addr_index;
        let freshest_rec =
            if inf.journal_version == inf.frozen_store.seq_end { None }
            else { Some(index[(inf.journal_version-1) as nat]) };

        Superblock{
            store_ptr: inf.store_ptr,
            journal: JournalSnapshot{boundary_lsn: inf.frozen_store.seq_end, freshest_rec},
        }
    }

    pub open spec(checked) fn persistent_sb(self) -> Superblock
    recommends
        self.wf(),
        self.client_ready(),
        self.persistent_journal_seq_end != self.journal.snapshot.boundary_lsn
        ==>
        ({
            let index = self.journal.status.unwrap().lsn_addr_index;
            &&& self.persistent_journal_seq_end > 0 
            &&& index.contains_key((self.persistent_journal_seq_end - 1) as nat)
        }),
    {
        let index = self.journal.status.unwrap().lsn_addr_index;
        let freshest_rec =
            if self.persistent_journal_seq_end == self.journal.snapshot.boundary_lsn { None }
            else { Some(index[(self.persistent_journal_seq_end-1) as nat]) };

        Superblock{
            store_ptr: self.persistent_store_ptr,
            journal: JournalSnapshot{boundary_lsn: self.journal.snapshot.boundary_lsn, freshest_rec},
        }
    }
}

}//verus!
