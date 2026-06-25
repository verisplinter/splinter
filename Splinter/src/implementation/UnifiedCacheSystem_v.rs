// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// State-machine refactor for the staged AnotherAtomicState model.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::multiset::*;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::AllocationBranch_v::Summary;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, marshal_abstract_superblock, superblock_matches,
};
use crate::implementation::AllocationBranchStack_v::normalize_value;
use crate::implementation::AllocationBranchStackRefinement_v::append_puts;
use crate::implementation::AnotherAtomicState_v::{
    AtomicBranchImage, AtomicBranchState, AtomicInflightInfo, AtomicJournalState,
    query_receipts_read_addrs, to_branch_nodes, valid_request_reply_pair,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranch_v::LoadedPathReceipt;
use crate::implementation::CachingDiskBranch_v::sealed_summary_aus_between;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::MultisetMapRelation_v::multiset_to_map;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{ID, Reply, Request, SyncReqId};
use crate::spec::Messages_t::{Message, Value};

verus! {

pub open spec fn singleton_key_seq(key: Key) -> Seq<Key>
{
    seq![key]
}

pub open spec fn singleton_message_seq(msg: Message) -> Seq<Message>
{
    seq![msg]
}


state_machine!{ UnifiedCacheSystem {
    fields {
        pub recovery_state: RecoveryState,
        pub cache: Cache::State,
        pub outstanding_cache_reqs: Map<ID, Address>,
        pub free_aus: Set<AU>,
        pub journal: AtomicJournalState::State,
        pub branch: AtomicBranchState::State,
        pub persistent_image: Option<AbstractSuperblockImage>,
        pub in_flight: Option<AtomicInflightInfo>,
        pub sync_req_map: Map<SyncReqId, LSN>,
    }

    pub enum Label {
        Execute{ req: Request, reply: Reply },
        AcceptSyncRequest{ sync_req_id: SyncReqId },
        DeliverSyncReply{ sync_req_id: SyncReqId },
        Disk,
        Internal,
    }

    init!{ initialize(cache_slots: nat, free_aus: Set<AU>) {
        require free_aus.disjoint(Self::reserved_aus());

        init recovery_state = RecoveryState::Begin;
        init cache = Cache::State::empty(cache_slots);
        init outstanding_cache_reqs = Map::empty();
        init free_aus = free_aus;
        init journal = AtomicJournalState::State::empty();
        init branch = AtomicBranchState::State::empty();
        init persistent_image = None;
        init in_flight = None;
        init sync_req_map = Map::empty();
    }}

    transition!{ execute_noop(lbl: Label) {
        require let Label::Execute{req, reply} = lbl;
        require valid_request_reply_pair(req, reply);
        require req.input is NoopInput;
        require reply.output is NoopOutput;
    }}

    transition!{ execute_put(
        lbl: Label,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_branch: AtomicBranchState::State,
    ) {
        require let Label::Execute{req, reply} = lbl;
        require valid_request_reply_pair(req, reply);
        require pre.client_ready();
        require req.input is PutInput;
        require reply.output is PutOutput;
        let key = req.input.arrow_PutInput_key();
        let value = req.input.arrow_PutInput_value();
        let msg = Message::Define{value};
        let keyed_message = KeyedMessage{key, message: msg};
        let records = MsgHistory::singleton_at(pre.branch.seq_end(), keyed_message);
        let keys = singleton_key_seq(key);
        let msgs = singleton_message_seq(msg);
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = AtomicBranchState::Label::Append{
            keys,
            msgs,
            receipt,
            init_root,
            read_nodes,
            write_nodes,
        };

        require if pre.branch.active_branch.root is Some {
            reads.dom() == receipt.needed_addrs()
        } else {
            reads.dom() == Set::<Address>::empty()
        };
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::Put{messages: records},
        );
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);

        update cache = new_cache;
        update journal = new_journal;
        update branch = new_branch;
    }}

    transition!{ execute_query(
        lbl: Label,
        new_cache: Cache::State,
        msg: Message,
        receipts: Seq<LoadedPathReceipt>,
        reads: Map<Address, RawPage>,
    ) {
        require let Label::Execute{req, reply} = lbl;
        require valid_request_reply_pair(req, reply);
        require pre.client_ready();
        require req.input is QueryInput;
        require reply.output is QueryOutput;
        let key = req.input.arrow_QueryInput_key();
        let value = reply.output.arrow_QueryOutput_value();
        let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
        let read_nodes = to_branch_nodes(reads);
        let branch_lbl = AtomicBranchState::Label::Query{key, msg, receipts, read_nodes};

        require reads.dom() == query_receipts_read_addrs(receipts, receipts.len() as nat);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicBranchState::State::next(pre.branch, pre.branch, branch_lbl);
        require normalize_value(msg) == value;

        update cache = new_cache;
    }}

    transition!{ accept_sync_request(lbl: Label) {
        require let Label::AcceptSyncRequest{sync_req_id} = lbl;
        require pre.client_ready();
        require !pre.sync_req_map.contains_key(sync_req_id);

        update sync_req_map = pre.sync_req_map.insert(sync_req_id, pre.branch.seq_end());
    }}

    transition!{ deliver_sync_reply(lbl: Label) {
        require let Label::DeliverSyncReply{sync_req_id} = lbl;
        require pre.client_ready();
        require pre.sync_req_map.contains_key(sync_req_id);
        require pre.sync_req_map[sync_req_id] <= pre.journal.persistent_seq_end;

        update sync_req_map = pre.sync_req_map.remove(sync_req_id);
    }}

    transition!{ initiate_recovery(
        lbl: Label,
        req_id: ID,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        require pre.recovery_state is Begin;
        require reqs == Multiset::empty().insert((
            req_id,
            DiskRequest::ReadReq{from: spec_superblock_addr()},
        ));
        require resps.is_empty();

        update recovery_state = RecoveryState::AwaitingSuperblock;
    }}

    transition!{ superblock_recovery(
        lbl: Label,
        req_id: ID,
        raw_page: RawPage,
        image: AbstractSuperblockImage,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let branch_image = AtomicBranchImage{
            sealed_roots: image.branch_roots,
            seq_end: image.branch_seq_end,
        };
        require pre.recovery_state is AwaitingSuperblock;
        require superblock_matches(raw_page, image);
        require AtomicBranchState::State::initialize(
            new_branch,
            branch_image,
            image.branch_roots.len() as nat,
        );
        require AtomicJournalState::State::initialize(
            new_journal,
            image.journal_snapshot,
            image.journal_seq_end,
        );
        require reqs.is_empty();
        require resps == Multiset::empty().insert((
            req_id,
            DiskResponse::ReadResp{data: raw_page},
        ));

        update recovery_state = RecoveryState::SuperblockAvailable;
        update journal = new_journal;
        update branch = new_branch;
        update persistent_image = Some(image);
        update in_flight = None;
        update sync_req_map = Map::empty();
    }}

    transition!{ execute_sync_begin(
        lbl: Label,
        req_id: ID,
        image: AbstractSuperblockImage,
        journal_reads: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let inflight = AtomicInflightInfo{
            req_id,
            boundary_lsn: image.branch_seq_end,
        };
        let cache_lbl = Cache::Label::Access{reads: journal_reads, writes: Map::empty()};
        let journal_lbl = AtomicJournalState::Label::CommitStart{
            snapshot: image.journal_snapshot,
            seq_end: image.journal_seq_end,
            reads: to_journal_records(journal_reads),
        };
        let branch_lbl = AtomicBranchState::Label::CommitStart{
            branch_image: AtomicBranchImage{
                sealed_roots: image.branch_roots,
                seq_end: image.branch_seq_end,
            },
        };

        require pre.client_ready();
        require pre.in_flight is None;
        require pre.sync_image_metadata_valid(image);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicJournalState::State::next(pre.journal, new_journal, journal_lbl);
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);
        require reqs.is_empty();
        require resps.is_empty();

        update cache = new_cache;
        update journal = new_journal;
        update branch = new_branch;
        update in_flight = Some(inflight);
    }}

    transition!{ execute_sync_prepared(
        lbl: Label,
        req: DiskRequest,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let image = pre.atomic_inflight_superblock_i();
        require pre.client_ready();
        require pre.in_flight is Some;
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::CommitPrepared,
        );
        require AtomicBranchState::State::next(
            pre.branch,
            new_branch,
            AtomicBranchState::Label::CommitPrepared,
        );
        require req is WriteReq;
        require req->to == spec_superblock_addr();
        require req->data == marshal_abstract_superblock(image);
        require superblock_matches(req->data, image);
        require reqs == Multiset::singleton((pre.in_flight.unwrap().req_id, req));
        require resps.is_empty();

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition!{ execute_sync_end(
        lbl: Label,
        journal_discarded_aus: Set<AU>,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let image = pre.atomic_inflight_superblock_i();
        let branch_lbl = AtomicBranchState::Label::CommitComplete;
        let journal_lbl = AtomicJournalState::Label::CommitComplete{
            require_end: pre.journal.journal.seq_end(),
            discarded_aus: journal_discarded_aus,
        };

        require pre.client_ready();
        require pre.in_flight is Some;
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);
        require AtomicJournalState::State::next(pre.journal, new_journal, journal_lbl);
        require reqs.is_empty();
        require resps == Multiset::singleton((
            pre.in_flight.unwrap().req_id,
            DiskResponse::WriteResp{},
        ));

        update free_aus = pre.free_aus + journal_discarded_aus;
        update journal = new_journal;
        update branch = new_branch;
        update persistent_image = Some(image);
        update in_flight = None;
    }}

    transition!{ cache_io_begin(
        lbl: Label,
        req_map: Map<ID, DiskRequest>,
        new_cache: Cache::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let updated = Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
        let new_outstanding = pre.outstanding_cache_reqs.union_prefer_right(updated);

        require !(pre.recovery_state is Begin);
        require !(pre.recovery_state is AwaitingSuperblock);
        require updated.is_injective();
        require !updated.contains_value(spec_superblock_addr());
        require multiset_to_map(reqs) == req_map;
        require resps.is_empty();
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
        );

        update cache = new_cache;
        update outstanding_cache_reqs = new_outstanding;
    }}

    transition!{ cache_io_end(
        lbl: Label,
        resp_map: Map<ID, DiskResponse>,
        new_cache: Cache::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let new_outstanding = pre.outstanding_cache_reqs.remove_keys(resp_map.dom());
        let finished = pre.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
        let cache_resps = Map::new(
            |addr| finished.contains_key(addr),
            |addr| resp_map[finished[addr]],
        );

        require !(pre.recovery_state is Begin);
        require !(pre.recovery_state is AwaitingSuperblock);
        require reqs.is_empty();
        require multiset_to_map(resps) == resp_map;
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps},
        );

        update cache = new_cache;
        update outstanding_cache_reqs = new_outstanding;
    }}

    transition!{ cache_internal(lbl: Label, new_cache: Cache::State) {
        require lbl is Internal;
        require Cache::State::next(pre.cache, new_cache, Cache::Label::Internal{});

        update cache = new_cache;
    }}

    transition!{ journal_load_index(
        lbl: Label,
        cache_reads: Map<Address, RawPage>,
        journal_reads: Map<Address, RawPage>,
        discovered_aus: Set<AU>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
    ) {
        require lbl is Internal;
        let cache_lbl = Cache::Label::Access{reads: cache_reads, writes: Map::empty()};
        let journal_lbl = AtomicJournalState::Label::LoadIndex{
            reads: to_journal_records(journal_reads),
            discovered_aus,
        };

        require pre.recovery_state is SuperblockAvailable;
        require journal_reads <= cache_reads;
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicJournalState::State::next(pre.journal, new_journal, journal_lbl);

        update cache = new_cache;
        update free_aus = pre.free_aus - discovered_aus;
        update journal = new_journal;
    }}

    transition!{ read_for_recovery(
        lbl: Label,
        addr: Address,
        keys: Seq<Key>,
        msgs: Seq<Message>,
        receipt: LoadedPathReceipt,
        init_root: Option<Address>,
        journal_reads: Map<Address, RawPage>,
        branch_reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchState::State,
    ) {
        require lbl is Internal;
        let reads = journal_reads.union_prefer_right(branch_reads);
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(branch_reads);
        let write_nodes = to_branch_nodes(writes);

        require pre.recovery_state is MetadataLoadComplete;
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require journal_reads <= reads;
        require branch_reads <= reads;
        require journal_reads.contains_key(addr);
        require pre.branch.seq_end() + keys.len() <= pre.journal.journal.seq_end();

        let full_msgs = to_journal_records(journal_reads)[addr].message_seq;
        let journal_records = full_msgs.maybe_discard_old(
            pre.journal.journal.snapshot.boundary_lsn);
        let branch_records = full_msgs.maybe_discard_old(
            pre.journal.journal.seq_start());

        let journal_lbl = AtomicJournalState::Label::ReadForRecovery{
            messages: journal_records,
            reads: to_journal_records(journal_reads),
        };
        let branch_lbl = AtomicBranchState::Label::Append{
            keys,
            msgs,
            receipt,
            init_root,
            read_nodes,
            write_nodes,
        };

        require branch_records == append_puts(pre.branch.seq_end(), keys, msgs);
        require AtomicJournalState::State::next(pre.journal, new_journal, journal_lbl);
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);

        update cache = new_cache;
        update journal = new_journal;
        update branch = new_branch;
    }}

    transition!{ journal_marshall(
        lbl: Label,
        addr: Address,
        raw_page: RawPage,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
    ) {
        require lbl is Internal;
        let writes = Map::<Address, RawPage>::empty().insert(addr, raw_page);
        let journal_lbl = AtomicJournalState::Label::JournalMarshal{
            addr,
            writes: to_journal_records(writes),
        };
        let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes};

        require pre.client_ready();
        require AtomicJournalState::State::next(pre.journal, new_journal, journal_lbl);
        require Cache::State::next(pre.cache, new_cache, cache_lbl);

        update cache = new_cache;
        update journal = new_journal;
    }}

    transition!{ observe_clean_journal_aus(
        lbl: Label,
        aus: Set<AU>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
    ) {
        require lbl is Internal;
        let cache_lbl = Cache::Label::EvictableCheck{aus};
        let journal_lbl = AtomicJournalState::Label::ObserveCleanAUs{aus};

        require pre.client_ready();
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicJournalState::State::next(pre.journal, new_journal, journal_lbl);

        update cache = new_cache;
        update journal = new_journal;
    }}

    transition!{ journal_fill_aus(
        lbl: Label,
        aus: Set<AU>,
        new_journal: AtomicJournalState::State,
    ) {
        require lbl is Internal;
        require pre.client_ready();
        require aus <= pre.free_aus;
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::FillAUs{aus},
        );

        update free_aus = pre.free_aus - aus;
        update journal = new_journal;
    }}

    transition!{ branch_load_metadata(
        lbl: Label,
        root: Address,
        reads: Map<Address, RawPage>,
        discovered_aus: Set<AU>,
        new_cache: Cache::State,
        new_branch: AtomicBranchState::State,
    ) {
        require lbl is Internal;
        let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
        let read_nodes = to_branch_nodes(reads);
        let branch_lbl = AtomicBranchState::Label::LoadMetadata{root, discovered_aus, read_nodes};

        require pre.recovery_state is SuperblockAvailable;
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);

        update cache = new_cache;
        update free_aus = pre.free_aus - discovered_aus;
        update branch = new_branch;
    }}

    transition!{ metadata_load_complete(lbl: Label) {
        require lbl is Internal;
        require pre.recovery_state is SuperblockAvailable;
        require pre.journal_metadata_loaded();
        require pre.branch_metadata_loaded();
        require pre.branch.mini_allocator == MiniAllocator::empty();

        update recovery_state = RecoveryState::MetadataLoadComplete;
    }}

    transition!{ branch_fill_aus(
        lbl: Label,
        aus: Set<AU>,
        new_branch: AtomicBranchState::State,
    ) {
        require lbl is Internal;
        require pre.client_ready();
        require aus <= pre.free_aus;
        require AtomicBranchState::State::next(
            pre.branch,
            new_branch,
            AtomicBranchState::Label::FillAUs{aus},
        );

        update free_aus = pre.free_aus - aus;
        update branch = new_branch;
    }}

    transition!{ branch_grow(
        lbl: Label,
        new_root_addr: Address,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_branch: AtomicBranchState::State,
    ) {
        require lbl is Internal;
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = AtomicBranchState::Label::Grow{
            new_root_addr,
            read_nodes,
            write_nodes,
        };

        require pre.client_ready();
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);

        update cache = new_cache;
        update branch = new_branch;
    }}

    transition!{ branch_split(
        lbl: Label,
        new_child_addr: Address,
        receipt: LoadedPathReceipt,
        split_arg: SplitArg,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_branch: AtomicBranchState::State,
    ) {
        require lbl is Internal;
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = AtomicBranchState::Label::Split{
            new_child_addr,
            receipt,
            split_arg,
            read_nodes,
            write_nodes,
        };

        require pre.client_ready();
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);

        update cache = new_cache;
        update branch = new_branch;
    }}

    transition!{ branch_seal(
        lbl: Label,
        aux_ptr: Pointer,
        summary: Summary,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_branch: AtomicBranchState::State,
    ) {
        require lbl is Internal;
        let cache_lbl = Cache::Label::Access{reads, writes};
        let read_nodes = to_branch_nodes(reads);
        let write_nodes = to_branch_nodes(writes);
        let branch_lbl = AtomicBranchState::Label::Seal{
            aux_ptr,
            summary,
            read_nodes,
            write_nodes,
        };

        require pre.client_ready();
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);

        update cache = new_cache;
        update branch = new_branch;
    }}

    transition!{ observe_persisted_branch_roots(
        lbl: Label,
        target_count: nat,
        aus: Set<AU>,
        new_cache: Cache::State,
        new_branch: AtomicBranchState::State,
    ) {
        require lbl is Internal;
        let cache_lbl = Cache::Label::EvictableCheck{aus};
        let branch_lbl = AtomicBranchState::Label::ObservePersistedRoots{target_count};

        require pre.client_ready();
        require aus == sealed_summary_aus_between(
            pre.branch.image.sealed_roots,
            pre.branch.branch_summary,
            pre.branch.persisted_root_count,
            target_count,
        );
        require Cache::State::next(pre.cache, new_cache, cache_lbl);
        require AtomicBranchState::State::next(pre.branch, new_branch, branch_lbl);

        update cache = new_cache;
        update branch = new_branch;
    }}

    transition!{ recovery_complete(lbl: Label) {
        require lbl is Internal;
        let end_lsn = pre.branch.seq_end();
        let journal_lbl = AtomicJournalState::Label::QueryEndLsn{end_lsn};

        require pre.recovery_state is MetadataLoadComplete;
        require AtomicJournalState::State::next(pre.journal, pre.journal, journal_lbl);

        update recovery_state = RecoveryState::RecoveryComplete;
    }}

    pub open spec fn reserved_aus() -> Set<AU>
    {
        set![spec_superblock_addr().au]
    }

    pub open spec fn journal_metadata_loaded(self) -> bool
    {
        self.journal.ready()
    }

    pub open spec fn branch_metadata_loaded(self) -> bool
    {
        self.branch.metadata_loaded()
    }

    pub open spec fn client_ready(self) -> bool
    {
        self.recovery_state is RecoveryComplete
    }

    pub open spec fn atomic_inflight_superblock_i(self) -> AbstractSuperblockImage
    {
        let journal_image = self.journal.in_flight.unwrap();
        let branch_image = self.branch.in_flight.unwrap();
        AbstractSuperblockImage{
            journal_snapshot: journal_image.snapshot,
            journal_seq_end: journal_image.seq_end,
            branch_roots: branch_image.sealed_roots,
            branch_seq_end: self.in_flight.unwrap().boundary_lsn,
        }
    }

    pub open spec fn sync_image_metadata_valid(self, image: AbstractSuperblockImage) -> bool
    {
        let root_count = image.branch_roots.len() as nat;
        &&& image.wf()
        &&& self.journal.persistent_seq_end <= image.journal_seq_end
        &&& image.journal_seq_end <= self.journal.journal.seq_end()
        &&& image.branch_seq_end <= self.branch.seq_end()
        &&& root_count <= self.branch.persisted_root_count
        &&& root_count <= self.branch.image.sealed_roots.len()
        &&& self.branch.image.sealed_roots.take(root_count as int) == image.branch_roots
    }
}}

} // verus!
