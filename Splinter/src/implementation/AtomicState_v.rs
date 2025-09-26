// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::{multiset::*};

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::abstract_system::AbstractCrashAwareMap_v::*;
use crate::implementation::DiskLayout_v::*;
use crate::implementation::SuperblockTypes_v::*;
use crate::implementation::Cache_v::*;
use crate::implementation::CachedJournal_v::*;
use crate::journal::LinkedJournal_v::{JournalRecord};

use crate::abstract_system::AbstractJournal_v::*;
use crate::abstract_system::AbstractMap_v::*;
use crate::abstract_system::StampedMap_v::*;
use crate::abstract_system::MsgHistory_v::*;

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

pub struct InflightInfo {
    pub journal_version: LSN,
    pub req_id: ID,
}

#[verifier::ext_equal]
pub struct AtomicState {
    pub recovery_state: RecoveryState,

    // msg history seq start
    // pub journal: AbstractJournal::State, // ephemeral
    pub journal: CachedJournal::State,
    pub cache: Cache::State,

    // crash aware map
    pub store: AbstractCrashAwareMap::State, // covers ephemeral, in_flight map, plus a persistent map

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
    ExecuteSyncBegin{req_id: ID, req: DiskRequest, frozen_journal: JournalSnapShot, 
        frozen_seq_end: LSN, frozen_domain: Set<Address>, reads: Map<Address, RawPage>},
    ExecuteSyncEnd{discard_addrs: Set<Address>},
    // other I/Os
    CacheIOBegin{req_map: Map<ID, DiskRequest>},
    CacheIOEnd{resp_map: Map<ID, DiskResponse>},
    // CacheReadBegin{req_map: Map<ID, addr: Address>},
    // CacheReadEnd{resp_map: Map<ID, raw_page: RawPage>},
    // CacheWriteBegin{req_map: Map<ID, info: (Address, RawPage)>},
    // CacheWriteEnd{resp_map: Set<ID>},
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

// TODO: not sure where 
pub closed spec fn raw_page_to_record(raw_page: RawPage) -> (out: JournalRecord)
{
    arbitrary()
}

pub open spec fn to_journal_reads(reads: Map<Address, RawPage>) -> Map<Address, JournalRecord>
{
    Map::new(
        |addr| reads.contains_key(addr), 
        |addr| raw_page_to_record(reads[addr])
    )
}

impl AtomicState {
    pub open spec fn client_ready(self) -> bool
    {
        self.recovery_state is RecoveryComplete
    }

    // Duck tape: directly accessing submodule state...
    pub open spec(checked) fn ephemeral_map(self) -> StampedMap
        recommends self.store.ephemeral is Known
    {
        self.store.ephemeral->v.stamped_map
    }

    pub open spec(checked) fn in_flight_map(self) -> StampedMap
        recommends self.store.in_flight is Some
    {
        self.store.in_flight.unwrap()
    }

    pub open spec fn persistent_map(self) -> StampedMap
    {
        self.store.persistent
    }

    pub open spec fn wf(self) -> bool {
        &&& self.client_ready() ==> {
            &&& self.journal.wf()
            // persistent map lines up with ephemeral journal
            &&& self.journal.seq_end() == self.persistent_map().seq_end
            // ephemeral map = persistent map + ephemeral journal
            // TODO(move into inv)
            // &&& self.ephemeral_map() == self.journal.journal.apply_to_stamped_map(self.persistent_map())
            &&& self.store.in_flight is Some <==> self.in_flight is Some

            &&& if let Some(ifl) = self.in_flight {
                &&& self.persistent_map().seq_end <= self.in_flight_map().seq_end
                // TODO(move into inv)
                // &&& self.ephemeral_map() == self.journal.journal
                //         .discard_old(self.in_flight_map().seq_end)
                //         .apply_to_stamped_map(self.in_flight_map())
                } else { true }
        }
    }

    // this is process init, which should do filesystem recovery before operation
    pub open spec fn init(cache_slots: nat) -> Self
    {
        AtomicState{
            recovery_state: RecoveryState::Begin,
            journal: arbitrary(),
            cache: Cache::State::empty(cache_slots),
            store: arbitrary(), 
            persistent_journal_seq_end: arbitrary(),
            in_flight: arbitrary(),
            sync_req_map: arbitrary(),
        }
    }

    pub open spec fn execute_noop(pre: Self, post: Self, req: Request, reply: Reply) -> bool
    {
        &&& post == pre
    }

    pub open spec fn execute_put(pre: Self, post: Self, req: Request, reply: Reply, records: MsgHistory) -> bool
    {
        &&& AbstractCrashAwareMap::State::next(pre.store, post.store, AbstractCrashAwareMap::Label::PutRecordsLabel{records})
        &&& CachedJournal::State::next(pre.journal, post.journal, CachedJournal::Label::Put{messages: records})
        &&& post == Self{
                journal: post.journal,
                store: post.store,
                ..pre
            }
    }

    pub open spec fn execute_query(pre: Self, post: Self, req: Request, reply: Reply, end_lsn: LSN, key: Key, value: Value) -> bool
    {
        &&& AbstractCrashAwareMap::State::next(pre.store, post.store, AbstractCrashAwareMap::Label::QueryLabel{end_lsn, key, value})
        &&& post == Self{
                store: post.store,
                ..pre
            }
    }

    pub open spec fn execute_transition(pre: Self, post: Self, req: Request, reply: Reply, event: ProgramEvent) -> bool
    {
        &&& pre.client_ready()
        &&& valid_request_reply_pair(req, reply)
        &&& match event {
            ProgramEvent::NoOp{} => Self::execute_noop(pre, post, req, reply),
            ProgramEvent::Put{puts} => Self::execute_put(pre, post, req, reply, puts),
            ProgramEvent::Query{end_lsn, key, value} => Self::execute_query(pre, post, req, reply, end_lsn, key, value)
        }
        &&& post.wf()
    }

    pub open spec fn store_internal(pre: Self, post: Self) -> bool
    {
        &&& AbstractCrashAwareMap::State::next(pre.store, post.store, AbstractCrashAwareMap::Label::InternalLabel{})
        &&& post == Self{
            store: post.store,
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
        &&& pre.sync_req_map[sync_req_id] <= pre.persistent_map().seq_end
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
                // duck tape
                store: AbstractCrashAwareMap::State{
                    persistent: superblock.store,
                    ephemeral: Ephemeral::Known{v: AbstractMap::State{stamped_map: superblock.store}},
                    in_flight: None,
                },
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
        let journal_lbl = CachedJournal::Label::LoadIndex{reads: to_journal_reads(reads)};

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

    // update map to the journal
    pub open spec fn map_recovery(pre: Self, post: Self, records: MsgHistory, reads: Map<Address, RawPage>) -> bool
    {
        let map_lbl = AbstractCrashAwareMap::Label::PutRecordsLabel{records};
        let journal_lbl = CachedJournal::Label::ReadForRecovery{messages: records, reads: to_journal_reads(reads)};
        let cache_lbl = Cache::Label::Access{reads: reads, writes: Map::empty()};

        &&& pre.recovery_state is JournalIndexComplete
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)
        &&& AbstractCrashAwareMap::State::next(pre.store, post.store, map_lbl)

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
        let journal_lbl = CachedJournal::Label::QueryEndLsn{end_lsn: end_lsn};
        
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

    pub open spec fn cache_io_begin(pre: Self, post: Self, req_map: Map<ID, DiskRequest>, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        &&& Cache::State::next(pre.cache, post.cache, Cache::Label::DiskOps{requests: req_map, responses: Map::empty()})
        &&& map_to_multiset(req_map) == reqs
        &&& resps.is_empty()
        &&& post == Self {
            cache: post.cache,
            ..pre
        }
    }

    pub open spec fn cache_io_end(pre: Self, post: Self, resp_map: Map<ID, DiskResponse>, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        &&& Cache::State::next(pre.cache, post.cache, Cache::Label::DiskOps{requests: Map::empty(), responses: resp_map})
        &&& map_to_multiset(resp_map) == resps
        &&& reqs.is_empty()
        &&& post == Self {
            cache: post.cache,
            ..pre
        }
    }

    // superblock sync
    pub open spec fn execute_sync_begin(pre: Self, post: Self, 
        req_id: ID, req: DiskRequest, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>, 
        frozen_journal: JournalSnapShot, frozen_seq_end: LSN, frozen_domain: Set<Address>, reads: Map<Address, RawPage>) -> bool
    {
        let map_lbl = AbstractCrashAwareMap::Label::CommitStartLabel{new_boundary_lsn: frozen_journal.boundary_lsn};
        let cache_lbl1 = Cache::Label::Access{reads: reads, writes: Map::empty()};
        let cache_lbl2 = Cache::Label::EvictableCheck{addrs: frozen_domain};
        let journal_lbl = CachedJournal::Label::FreezeForCommit{frozen: frozen_journal, frozen_seq_end, frozen_domain, reads: to_journal_reads(reads)};

        let sb = Superblock{
            store: pre.in_flight_map(),
            journal: frozen_journal,
        };

        // superblock writes
        let inflight_info = InflightInfo{
            journal_version: frozen_seq_end,
            req_id
        };

        &&& pre.client_ready()
        &&& pre.in_flight is None

        // checks that map has been frozen
        &&& AbstractCrashAwareMap::State::next(pre.store, post.store, map_lbl)

        // checks that frozen journal has been flushed
        &&&  Cache::State::next(pre.cache, post.cache, cache_lbl1)
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl2)
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)

        &&& req is WriteReq
        &&& req->to == spec_superblock_addr()
        &&& DiskLayout::spec_new().spec_parse(req->data) == sb
        &&& reqs == Multiset::singleton((req_id, req))
        &&& resps.is_empty()
        &&& post == Self{ 
            store: post.store,
            cache: post.cache,
            journal: post.journal,
            in_flight: Some(inflight_info), 
            .. pre}
    }

    pub open spec fn execute_sync_end(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>,
        discard_addrs: Set<Address>) -> bool
    {
        let map_lbl = AbstractCrashAwareMap::Label::CommitCompleteLabel{};
        let journal_lbl = CachedJournal::Label::DiscardOld{
            start_lsn: post.persistent_map().seq_end,
            require_end: post.ephemeral_map().seq_end, // requires journal to still line up with ephemeral map, might not be needed
            discard_addrs,
        };
        let cache_lbl = Cache::Label::EvictableCheck{addrs: discard_addrs};

        &&& pre.client_ready()
        &&& pre.in_flight is Some 
        &&& reqs.is_empty()
        &&& resps == Multiset::singleton((pre.in_flight.unwrap().req_id, DiskResponse::WriteResp{}))

        // map state shifts from persistent to in flight
        &&& AbstractCrashAwareMap::State::next(pre.store, post.store, map_lbl)
        // journal truncates if necessary
        &&& CachedJournal::State::next(pre.journal, post.journal, journal_lbl)
        // cache checks that discarded pages are now evictable
        &&& Cache::State::next(pre.cache, post.cache, cache_lbl)

        &&& post == Self{
            store: post.store,
            journal: post.journal,
            cache: post.cache,
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
            DiskEvent::ExecuteSyncBegin{req_id, req, frozen_journal, frozen_seq_end, frozen_domain, reads} 
                => Self::execute_sync_begin(pre, post, req_id, req, reqs, resps, frozen_journal, frozen_seq_end, frozen_domain, reads),
            DiskEvent::ExecuteSyncEnd{discard_addrs} => Self::execute_sync_end(pre, post, reqs, resps, discard_addrs),
            DiskEvent::CacheIOBegin{req_map} => Self::cache_io_begin(pre, post, req_map, reqs, resps),
            DiskEvent::CacheIOEnd{resp_map} => Self::cache_io_end(pre, post, resp_map, reqs, resps),
        }
    }

    // NOTE: silly internal op for now
    pub open spec fn internal_transitions(pre: Self, post: Self) -> bool
    {
        &&& pre == post 
        &&& pre.client_ready()
    }

    // pub open spec(checked) fn in_flight_sb(self) -> Superblock
    // recommends
    //     self.wf(),
    //     self.client_ready(),
    //     self.in_flight is Some,
    // {
    //     let inf = self.in_flight.unwrap();
    //     Superblock{
    //         store: inf.new_persistent_map,
    //         journal: self.journal.journal.discard_old(inf.new_persistent_map.seq_end).discard_recent(inf.journal_version),
    //     }
    // }

    // pub open spec(checked) fn persistent_sb(self) -> Superblock
    // recommends
    //     self.wf(),
    //     self.client_ready(),
    // {
    //     Superblock{
    //         store: self.persistent_map,
    //         journal: self.journal.journal.discard_recent(self.persistent_journal_seq_end),
    //     }
    // }
}

}//verus!
