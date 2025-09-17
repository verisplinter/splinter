// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
use vstd::{prelude::*};
use vstd::{multiset::*};

use crate::spec::KeyType_t::*;
use crate::spec::Messages_t::*;
use crate::spec::MapSpec_t::*;
use crate::spec::FloatingSeq_t::*;
use crate::spec::AsyncDisk_t::*;
use crate::implementation::DiskLayout_v::*;
use crate::implementation::SuperblockTypes_v::*;
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
    // System can now operate
    RecoveryComplete,
}

pub struct InflightInfo {
    pub new_persistent_map: StampedMap,
    pub journal_version: LSN,
    pub req_id: ID,
}

impl InflightInfo {
    pub open spec fn wf(self) -> bool
    {
        self.new_persistent_map.seq_end <= self.journal_version
    }

    pub open spec fn map_version(self) -> LSN
    {
        self.new_persistent_map.seq_end
    }
}

#[verifier::ext_equal]
pub struct AtomicState {
    pub recovery_state: RecoveryState,

    pub journal: AbstractJournal::State, // ephemeral
    pub map: AbstractMap::State, // ephemeral

    // The view of the disk's map that we learn (ghostily) on recovery.
    pub persistent_map: StampedMap,
    pub persistent_journal_seq_end: LSN,

    // pub journal: CachedJournal::State,
    // pub cache: Cache::State,

    // tells us what we can bump persistent_version when the disk response comes back.
    pub in_flight: Option<InflightInfo>,

    // maps each syncreq id with a version
    pub sync_req_map: Map<SyncReqId, nat>, 
}

pub enum DiskEvent{
    InitiateRecovery{req_id: ID},
    CompleteRecovery{req_id: ID, raw_page: RawPage},
    ExecuteSyncBegin{req_id: ID, req: DiskRequest, sync_map: bool},
    ExecuteSyncEnd{},
}

// labels
pub enum ProgramEvent{
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

impl AtomicState {
    pub open spec fn client_ready(self) -> bool
    {
        self.recovery_state is RecoveryComplete
    }

    pub open spec fn persistent_map_version(self) -> LSN
    {
        self.persistent_map.seq_end
    }

    pub open spec fn wf(self) -> bool {
        &&& self.client_ready() ==> {
            &&& self.journal.wf()
            // persistent map lines up with ephemeral journal
            &&& self.journal.journal.seq_start == self.persistent_map.seq_end
            // ephemeral map = persistent map + ephemeral journal
            &&& self.map.stamped_map == self.journal.journal.apply_to_stamped_map(self.persistent_map)
            &&& if let Some(ifl) = self.in_flight {
                &&& ifl.wf()
                &&& self.persistent_map_version() <= ifl.map_version()
                &&& self.map.stamped_map == self.journal.journal
                        .discard_old(ifl.map_version())
                        .apply_to_stamped_map(ifl.new_persistent_map)
            } else { true }
        }
    }

    // this is process init, which should do filesystem recovery before operation
    pub open spec fn init() -> Self
    {
        AtomicState{
            recovery_state: RecoveryState::Begin,
            journal: arbitrary(),
            map: arbitrary(),
            persistent_map: arbitrary(),
            persistent_journal_seq_end: arbitrary(),
            in_flight: arbitrary(),
            sync_req_map: arbitrary(),
        }
    }

    pub open spec fn execute_put(pre: Self, post: Self, req: Request, reply: Reply, puts: MsgHistory) -> bool
    {
        &&& AbstractMap::State::next(pre.map, post.map, AbstractMap::Label::PutLabel{puts})
        &&& AbstractJournal::State::next(pre.journal, post.journal, AbstractJournal::Label::PutLabel{messages: puts})
    }   

    pub open spec fn execute_query(pre: Self, post: Self, req: Request, reply: Reply, end_lsn: LSN, key: Key, value: Value) -> bool
    {
        &&& AbstractMap::State::next(pre.map, post.map, AbstractMap::Label::QueryLabel{end_lsn, key, value})
    }   

    pub open spec fn execute_transition(pre: Self, post: Self, req: Request, reply: Reply, event: ProgramEvent) -> bool
    {
        &&& pre.client_ready()
        &&& valid_request_reply_pair(req, reply)
        &&& match event {
            ProgramEvent::Put{puts} => Self::execute_put(pre, post, req, reply, puts),
            ProgramEvent::Query{end_lsn, key, value} => Self::execute_query(pre, post, req, reply, end_lsn, key, value)
        }
        &&& post.wf()
        &&& post == Self{
                journal: post.journal,
                map: post.map,
                ..pre
            }
    }

    pub open spec fn accept_sync_request(pre: Self, post: Self, sync_req_id: SyncReqId) -> bool
    {
        &&& pre.client_ready()
        // &&& !pre.sync_req_map.contains_key(sync_req_id) // true by system invariant
        &&& post == Self{
            sync_req_map: pre.sync_req_map.insert(sync_req_id, pre.map.stamped_map.seq_end as nat),
            ..pre
        }
    }

    pub open spec fn deliver_sync_reply(pre: Self, post: Self, sync_req_id: SyncReqId) -> bool
    {
        &&& pre.client_ready()
        // The request with this id was once made and is still outstanding
        &&& pre.sync_req_map.contains_key(sync_req_id)
        // The request has been satisfied by a disk sync that got completed
        &&& pre.sync_req_map[sync_req_id] <= pre.persistent_map.seq_end
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

    pub open spec fn complete_recovery(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>, req_id: ID, raw_page: RawPage) -> bool
    {
        &&& pre.recovery_state is AwaitingSuperblock // can prove this by invariant
        &&& reqs.is_empty()
        &&& resps == Multiset::empty().insert((req_id, DiskResponse::ReadResp{data: raw_page}))
        // &&& valid_checksum(raw_page)
        &&& {
            let superblock = DiskLayout::spec_new().spec_parse(raw_page);
            post == Self{
                recovery_state: RecoveryState::RecoveryComplete,
                persistent_map: superblock.store,
                persistent_journal_seq_end: superblock.journal.seq_end,
                journal: AbstractJournal::State{ journal: superblock.journal },
                map: AbstractMap::State{ stamped_map: superblock.journal.apply_to_stamped_map(superblock.store) },
                in_flight: None,
                sync_req_map: Map::empty(),
            }
        }
    }

    pub open spec fn execute_sync_begin(pre: Self, post: Self, req_id: ID, req: DiskRequest, sync_map: bool, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        let sb = pre.sync_sb(sync_map);
        let inflight_info = InflightInfo{
            new_persistent_map: sb.store,
            journal_version: pre.journal.journal.seq_end,
            req_id
        };

        &&& pre.client_ready()
        &&& pre.in_flight is None

        &&& req is WriteReq
        &&& req->to == spec_superblock_addr()
        &&& DiskLayout::spec_new().spec_parse(req->data) == sb
        &&& reqs == Multiset::singleton((req_id, req))

        &&& resps.is_empty()

        &&& post == Self{ in_flight: Some(inflight_info), .. pre }
    }

    pub open spec fn execute_sync_end(pre: Self, post: Self, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        &&& pre.client_ready()
        &&& pre.in_flight is Some 
        &&& reqs.is_empty()
        &&& resps == Multiset::singleton((pre.in_flight.unwrap().req_id, DiskResponse::WriteResp{}))

        &&& {
            let new_persistent_map = pre.in_flight.unwrap().new_persistent_map;
            &&& post == Self{
                recovery_state: RecoveryState::RecoveryComplete,
                persistent_map: new_persistent_map,
                journal: AbstractJournal::State{ journal: pre.journal.journal.discard_old(new_persistent_map.seq_end) },
                in_flight: None,
                ..pre
            }
        }
    }

    pub open spec fn disk_transition(pre: Self, post: Self, disk_event: DiskEvent, reqs: Multiset<(ID, DiskRequest)>, resps: Multiset<(ID, DiskResponse)>) -> bool
    {
        match disk_event {
            DiskEvent::InitiateRecovery{req_id} => Self::initiate_recovery(pre, post, reqs, resps, req_id),
            DiskEvent::CompleteRecovery{req_id, raw_page} => Self::complete_recovery(pre, post, reqs, resps, req_id, raw_page),
            DiskEvent::ExecuteSyncBegin{req_id, req, sync_map} => Self::execute_sync_begin(pre, post, req_id, req, sync_map, reqs, resps),
            DiskEvent::ExecuteSyncEnd{} => Self::execute_sync_end(pre, post, reqs, resps),
        }
    }

    // TODO delete dead code
//     pub closed spec fn disk_transition_system_assumptions(disk_event: DiskEvent) -> bool
//     {
//         match disk_event {
//             DiskEvent::CompleteRecovery{req_id, raw_page} => {
//                 // remember that superblock invariant survives disk
//                 let superblock = DiskLayout::spec_new().spec_parse(raw_page);
//                 superblock.store.appv.invariant()
//             },
//             _ => { true },
//         }
//     }

    // NOTE: silly internal op for now
    pub open spec fn internal_transitions(pre: Self, post: Self) -> bool
    {
        &&& pre == post 
        &&& pre.client_ready()
    }

    // Just the ephemeral map
    pub open spec fn mapspec(self) -> MapSpec::State {
        MapSpec::State{ kmmap: self.map.stamped_map.value }
    }

    pub open spec(checked) fn sync_sb(self, sync_map: bool) -> Superblock
    recommends
        self.client_ready(),
    {
        if sync_map {
            Superblock{
                store: self.map.stamped_map,
                journal: MsgHistory::empty_history_at(self.map.stamped_map.seq_end),
            }
        } else {
            Superblock{
                store: self.persistent_map,
                journal: self.journal.journal,
            }
        }
    }

    pub open spec(checked) fn in_flight_sb(self) -> Superblock
    recommends
        self.wf(),
        self.client_ready(),
        self.in_flight is Some,
    {
        let inf = self.in_flight.unwrap();
        Superblock{
            store: inf.new_persistent_map,
            journal: self.journal.journal.discard_old(inf.new_persistent_map.seq_end).discard_recent(inf.journal_version),
        }
    }

    pub open spec(checked) fn persistent_sb(self) -> Superblock
    recommends
        self.wf(),
        self.client_ready(),
    {
        Superblock{
            store: self.persistent_map,
            journal: self.journal.journal.discard_recent(self.persistent_journal_seq_end),
        }
    }
}

}//verus!
