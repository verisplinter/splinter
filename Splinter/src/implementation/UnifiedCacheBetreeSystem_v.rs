// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Unified shared-cache system with a directly embedded CachedBranchBetree.
// This module is kept parallel to UnifiedCacheSystem while its refinement and
// executable implementation are migrated from the prototype branch stack.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::multiset::*;

use verus_state_machines_macros::state_machine;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::betree::LinkedBetree_v::{PathAddrs, SplitAddrs, TwoAddrs};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::disk::GenericDisk_v::{AU, Address, Pointer};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, superblock_matches,
};
use crate::implementation::AtomicBranchBetreeState_v::{
    AtomicBranchBetreeState, AtomicBranchBetreeControl,
};
use crate::implementation::AtomicJournalState_v::AtomicJournalState;
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachedBranchBetree_v::{
    CachedBranchBetree, FrozenBranchBetree, LoadedBetreePath,
    LoadedBetreeQueryReceipt,
};
use crate::implementation::CachedBulkBranch_v::CachedBulkBranch;
use crate::implementation::CachingDiskBranchBetree_v::{
    BranchBuildEvent, PageAccess,
};
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::{
    BetreeMetadataRecoveryCore, BetreeMetadataRecoveryLabel,
    CachingDiskBranchBetreeMetadata, FrozenCachingDiskBranchBetree,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::MultisetMapRelation_v::multiset_to_map;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{ID, Reply, Request, SyncReqId};
use crate::spec::Messages_t::{Message, Value};

verus! {

pub open spec fn betree_metadata_from_superblock(
    image: AbstractSuperblockImage,
) -> CachingDiskBranchBetreeMetadata {
    CachingDiskBranchBetreeMetadata {
        root: image.betree_root,
        seq_end: image.journal_snapshot.boundary_lsn,
    }
}

pub open spec fn betree_superblock_image_wf(
    image: AbstractSuperblockImage,
) -> bool {
    image.wf()
}

pub enum AtomicBetreeSyncPhase {
    None,
    Preparing {
        image: AbstractSuperblockImage,
        journal_ready: bool,
        branch_ready: bool,
    },
    SuperblockWriteIssued {
        req_id: ID,
        image: AbstractSuperblockImage,
    },
}

impl AtomicBetreeSyncPhase {
    pub open spec fn image(self) -> Option<AbstractSuperblockImage> {
        match self {
            AtomicBetreeSyncPhase::None => None,
            AtomicBetreeSyncPhase::Preparing{image, ..}
            | AtomicBetreeSyncPhase::SuperblockWriteIssued{
                image, ..
            } => Some(image),
        }
    }

    pub open spec fn req_id(self) -> Option<ID> {
        match self {
            AtomicBetreeSyncPhase::SuperblockWriteIssued{
                req_id, ..
            } =>
                Some(req_id),
            _ => None,
        }
    }

    pub open spec fn journal_ready(self) -> bool {
        match self {
            AtomicBetreeSyncPhase::Preparing{
                journal_ready, ..
            } => journal_ready,
            AtomicBetreeSyncPhase::SuperblockWriteIssued{..} => true,
            AtomicBetreeSyncPhase::None => false,
        }
    }

    pub open spec fn branch_ready(self) -> bool {
        match self {
            AtomicBetreeSyncPhase::Preparing{
                branch_ready, ..
            } => branch_ready,
            AtomicBetreeSyncPhase::SuperblockWriteIssued{..} => true,
            AtomicBetreeSyncPhase::None => false,
        }
    }
}

state_machine! { UnifiedCacheBetreeSystem {
    fields {
        pub recovery_state: RecoveryState,
        pub cache: Cache::State,
        pub outstanding_cache_reqs: Map<ID, Address>,
        pub free_aus: Set<AU>,
        pub journal: AtomicJournalState::State,
        pub branch: AtomicBranchBetreeState::State,
        pub persistent_image: Option<AbstractSuperblockImage>,
        pub sync_phase: AtomicBetreeSyncPhase,
        pub sync_req_map: Map<SyncReqId, LSN>,
    }

    pub enum Label {
        Execute{req: Request, reply: Reply},
        AcceptSyncRequest{sync_req_id: SyncReqId},
        DeliverSyncReply{sync_req_id: SyncReqId},
        Disk,
        Internal,
    }

    init! { initialize(cache_slots: nat, free_aus: Set<AU>) {
        require free_aus.disjoint(Self::reserved_aus());

        init recovery_state = RecoveryState::Begin;
        init cache = Cache::State::empty(cache_slots);
        init outstanding_cache_reqs = Map::empty();
        init free_aus = free_aus;
        init journal = AtomicJournalState::State::empty();
        init branch = AtomicBranchBetreeState::State::empty();
        init persistent_image = None;
        init sync_phase = AtomicBetreeSyncPhase::None;
        init sync_req_map = Map::empty();
    }}

    transition! { execute_noop(lbl: Label) {
        require let Label::Execute{req, reply} = lbl;
        require Self::valid_request_reply_pair(req, reply);
        require req.input is NoopInput;
        require reply.output is NoopOutput;
    }}

    transition! { execute_put(
        lbl: Label,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchBetreeState::State,
    ) {
        require let Label::Execute{req, reply} = lbl;
        require Self::valid_request_reply_pair(req, reply);
        require pre.client_ready();
        require req.input is PutInput;
        require reply.output is PutOutput;

        let key = req.input.arrow_PutInput_key();
        let value = req.input.arrow_PutInput_value();
        let records = MsgHistory::singleton_at(
            pre.branch.betree.memtable.seq_end,
            KeyedMessage {
                key,
                message: Message::Define{value},
            },
        );

        // NOTE: we no longer perform cache access here because our memtable will 
        // look like a direct array storing messages, meaning we are not building
        // any disk backed data structure right now
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::Put{messages: records},
        );
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            new_branch,
            AtomicBranchBetreeState::Label::Put{puts: records},
        );

        update journal = new_journal;
        update branch = new_branch;
    }}

    transition! { execute_query(
        lbl: Label,
        new_cache: Cache::State,
        access: PageAccess,
    ) {
        require let Label::Execute{req, reply} = lbl;
        require Self::valid_request_reply_pair(req, reply);
        require pre.client_ready();
        require req.input is QueryInput;
        require reply.output is QueryOutput;
        let key = req.input.arrow_QueryInput_key();
        let value = reply.output.arrow_QueryOutput_value();

        require access.wf();
        require access.read_only();
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{
                reads: access.reads(),
                writes: access.writes(),
            },
        );
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            pre.branch,
            AtomicBranchBetreeState::Label::Query {
                end_lsn: pre.branch.betree.memtable.seq_end,
                key,
                value,
                access,
            },
        );

        update cache = new_cache;
    }}

    transition! { accept_sync_request(lbl: Label) {
        require let Label::AcceptSyncRequest{sync_req_id} = lbl;
        require pre.client_ready();
        require !pre.sync_req_map.contains_key(sync_req_id);

        update sync_req_map = pre.sync_req_map.insert(
            sync_req_id,
            pre.branch.betree.memtable.seq_end,
        );
    }}

    transition! { deliver_sync_reply(lbl: Label) {
        require let Label::DeliverSyncReply{sync_req_id} = lbl;
        require pre.client_ready();
        require pre.sync_req_map.contains_key(sync_req_id);
        require pre.sync_req_map[sync_req_id]
            <= pre.journal.persistent_seq_end;

        update sync_req_map = pre.sync_req_map.remove(sync_req_id);
    }}

    transition! { initiate_recovery(
        lbl: Label,
        req_id: ID,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        require pre.recovery_state is Begin;
        require reqs == Multiset::singleton((
            req_id,
            DiskRequest::ReadReq{from: spec_superblock_addr()},
        ));
        require resps.is_empty();

        update recovery_state = RecoveryState::AwaitingSuperblock;
    }}

    transition! { superblock_recovery(
        lbl: Label,
        req_id: ID,
        raw_page: RawPage,
        image: AbstractSuperblockImage,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchBetreeState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let metadata = betree_metadata_from_superblock(image);
        require pre.recovery_state is AwaitingSuperblock;
        require superblock_matches(raw_page, image);
        require AtomicJournalState::State::init_by(
            new_journal,
            AtomicJournalState::Config::initialize(
                image.journal_snapshot,
                image.journal_seq_end,
            ),
        );
        require AtomicBranchBetreeState::State::init_by(
            new_branch,
            AtomicBranchBetreeState::Config::initialize(metadata),
        );
        require reqs.is_empty();
        require resps == Multiset::singleton((
            req_id,
            DiskResponse::ReadResp{data: raw_page},
        ));

        update recovery_state = RecoveryState::SuperblockAvailable;
        update journal = new_journal;
        update branch = new_branch;
        update persistent_image = Some(image);
        update sync_phase = AtomicBetreeSyncPhase::None;
        update sync_req_map = Map::empty();
    }}

    transition! { branch_internal(
        lbl: Label,
        new_branch: AtomicBranchBetreeState::State,
    ) {
        require lbl is Internal;
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            new_branch,
            AtomicBranchBetreeState::Label::Internal,
        );

        update branch = new_branch;
    }}

    transition! { branch_internal_access(
        lbl: Label,
        branch_lbl: AtomicBranchBetreeState::Label,
        access: PageAccess,
        new_cache: Cache::State,
        new_branch: AtomicBranchBetreeState::State,
    ) {
        require lbl is Internal;
        require branch_lbl.internal_access() == Some(access);
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            new_branch,
            branch_lbl,
        );
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{
                reads: access.reads(),
                writes: access.writes(),
            },
        );

        update cache = new_cache;
        update branch = new_branch;
    }}

    transition! { branch_recovery_complete(
        lbl: Label,
        discovered_aus: Set<AU>,
        new_branch: AtomicBranchBetreeState::State,
    ) {
        require lbl is Internal;
        require pre.recovery_state is SuperblockAvailable;
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            new_branch,
            AtomicBranchBetreeState::Label::RecoveryComplete{
                discovered_aus,
            },
        );

        update free_aus = pre.free_aus - discovered_aus;
        update branch = new_branch;
    }}

    transition! { cache_io_begin(
        lbl: Label,
        req_map: Map<ID, DiskRequest>,
        new_cache: Cache::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let updated = Map::new(
            |id| req_map.contains_key(id),
            |id| req_map[id].addr(),
        );

        require !(pre.recovery_state is Begin);
        require !(pre.recovery_state is AwaitingSuperblock);
        require updated.is_injective();
        require !updated.contains_value(spec_superblock_addr());
        require multiset_to_map(reqs) == req_map;
        require resps.is_empty();
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::DiskOps{
                requests: req_map.values(),
                responses: Map::empty(),
            },
        );

        update cache = new_cache;
        update outstanding_cache_reqs =
            pre.outstanding_cache_reqs.union_prefer_right(updated);
    }}

    transition! { cache_io_end(
        lbl: Label,
        resp_map: Map<ID, DiskResponse>,
        new_cache: Cache::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let finished = pre.outstanding_cache_reqs
            .restrict(resp_map.dom()).invert();
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
            Cache::Label::DiskOps{
                requests: Set::empty(),
                responses: cache_resps,
            },
        );

        update cache = new_cache;
        update outstanding_cache_reqs =
            pre.outstanding_cache_reqs.remove_keys(resp_map.dom());
    }}

    transition! { cache_internal(
        lbl: Label,
        new_cache: Cache::State,
    ) {
        require lbl is Internal;
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Internal{},
        );

        update cache = new_cache;
    }}

    transition! { journal_load_index(
        lbl: Label,
        cache_reads: Map<Address, RawPage>,
        journal_reads: Map<Address, RawPage>,
        discovered_aus: Set<AU>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
    ) {
        require lbl is Internal;
        require pre.recovery_state is SuperblockAvailable;
        require journal_reads <= cache_reads;
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{
                reads: cache_reads,
                writes: Map::empty(),
            },
        );
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::LoadIndex{
                reads: to_journal_records(journal_reads),
                discovered_aus,
            },
        );

        update cache = new_cache;
        update free_aus = pre.free_aus - discovered_aus;
        update journal = new_journal;
    }}

    transition! { metadata_load_complete(lbl: Label) {
        require lbl is Internal;
        require pre.recovery_state is SuperblockAvailable;
        require pre.journal.ready();
        require pre.branch.control.metadata_loaded;

        update recovery_state = RecoveryState::MetadataLoadComplete;
    }}

    transition! { read_for_recovery(
        lbl: Label,
        addr: Address,
        journal_reads: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
        new_branch: AtomicBranchBetreeState::State,
    ) {
        require lbl is Internal;
        require pre.recovery_state is MetadataLoadComplete;
        require journal_reads.contains_key(addr);
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{
                reads: journal_reads,
                writes: Map::empty(),
            },
        );
        let full_msgs =
            to_journal_records(journal_reads)[addr].message_seq;
        let journal_records = full_msgs.maybe_discard_old(
            pre.journal.journal.snapshot.boundary_lsn,
        );
        let branch_records = full_msgs.maybe_discard_old(
            pre.branch.betree.memtable.seq_end,
        );
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::ReadForRecovery{
                messages: journal_records,
                reads: to_journal_records(journal_reads),
            },
        );
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            new_branch,
            AtomicBranchBetreeState::Label::Put{puts: branch_records},
        );

        update cache = new_cache;
        update journal = new_journal;
        update branch = new_branch;
    }}

    transition! { recovery_complete(lbl: Label) {
        require lbl is Internal;
        require pre.recovery_state is MetadataLoadComplete;
        require AtomicJournalState::State::next(
            pre.journal,
            pre.journal,
            AtomicJournalState::Label::QueryEndLsn{
                end_lsn: pre.branch.betree.memtable.seq_end,
            },
        );

        update recovery_state = RecoveryState::RecoveryComplete;
    }}

    transition! { journal_internal_access(
        lbl: Label,
        journal_lbl: AtomicJournalState::Label,
        reads: Map<Address, RawPage>,
        writes: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
    ) {
        require lbl is Internal;
        require pre.client_ready();
        require AtomicJournalState::State::internal_access_next(
            pre.journal,
            new_journal,
            journal_lbl,
            reads,
            writes,
        );
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{
                reads,
                writes,
            },
        );

        update cache = new_cache;
        update journal = new_journal;
    }}

    transition! { observe_clean_journal_aus(
        lbl: Label,
        aus: Set<AU>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
    ) {
        require lbl is Internal;
        require pre.client_ready();
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::EvictableCheck{aus},
        );
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::ObserveCleanAUs{aus},
        );

        update cache = new_cache;
        update journal = new_journal;
    }}

    transition! { journal_fill_aus(
        lbl: Label,
        aus: Set<AU>,
        new_journal: AtomicJournalState::State,
    ) {
        require lbl is Internal;
        require pre.allocation_metadata_loaded();
        require aus <= pre.free_aus;
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::FillAUs{aus},
        );

        update free_aus = pre.free_aus - aus;
        update journal = new_journal;
    }}

    transition! { branch_internal_alloc_access(
        lbl: Label,
        allocs: Set<AU>,
        deallocs: Set<AU>,
        access: PageAccess,
        new_cache: Cache::State,
        new_branch: AtomicBranchBetreeState::State,
    ) {
        require lbl is Internal;
        require pre.client_ready();
        require allocs <= pre.free_aus;
        require allocs.disjoint(
            pre.branch.control.protected_aus(),
        );
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            new_branch,
            AtomicBranchBetreeState::Label::InternalAllocAccess{
                allocs,
                deallocs,
                access,
            },
        );
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{
                reads: access.reads(),
                writes: access.writes(),
            },
        );

        update cache = new_cache;
        update free_aus =
            (pre.free_aus - allocs)
                + pre.branch.control.reclaimable(deallocs);
        update branch = new_branch;
    }}

    transition! { execute_journal_sync_begin(
        lbl: Label,
        image: AbstractSuperblockImage,
        journal_reads: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        require pre.client_ready();
        require pre.sync_phase is None;
        require pre.journal_sync_image_metadata_valid(image);
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{
                reads: journal_reads,
                writes: Map::empty(),
            },
        );
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::CommitStart{
                snapshot: image.journal_snapshot,
                seq_end: image.journal_seq_end,
                reads: to_journal_records(journal_reads),
            },
        );
        require reqs.is_empty();
        require resps.is_empty();

        update cache = new_cache;
        update journal = new_journal;
        update sync_phase =
            AtomicBetreeSyncPhase::Preparing{
                image,
                journal_ready: false,
                branch_ready: true,
            };
    }}

    transition! { execute_sync_journal_prepare(
        lbl: Label,
    ) {
        require lbl is Internal;
        require let AtomicBetreeSyncPhase::Preparing{
            image,
            journal_ready,
            branch_ready,
        } = pre.sync_phase;
        require pre.client_ready();
        require !journal_ready;
        require AtomicJournalState::State::next(
            pre.journal,
            pre.journal,
            AtomicJournalState::Label::CommitPrepared,
        );

        update sync_phase =
            AtomicBetreeSyncPhase::Preparing{
                image,
                journal_ready: true,
                branch_ready,
            };
    }}

    transition! { execute_sync_branch_prepare(
        lbl: Label,
        new_cache: Cache::State,
    ) {
        require lbl is Internal;
        require let AtomicBetreeSyncPhase::Preparing{
            image,
            journal_ready,
            branch_ready,
        } = pre.sync_phase;
        require pre.client_ready();
        require !branch_ready;
        require pre.branch.control.frozen is Some;
        let frozen = pre.branch.control.frozen.unwrap();
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::EvictableCheck{aus: frozen.aus},
        );
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            pre.branch,
            AtomicBranchBetreeState::Label::CommitPrepared,
        );

        update cache = new_cache;
        update sync_phase =
            AtomicBetreeSyncPhase::Preparing{
                image,
                journal_ready,
                branch_ready: true,
            };
    }}

    transition! { execute_sync_superblock_write(
        lbl: Label,
        req_id: ID,
        req: DiskRequest,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        require let AtomicBetreeSyncPhase::Preparing{
            image,
            journal_ready,
            branch_ready,
        } = pre.sync_phase;
        require pre.client_ready();
        require journal_ready;
        require branch_ready;
        require req is WriteReq;
        require req->to == spec_superblock_addr();
        require superblock_matches(req->data, image);
        require reqs == Multiset::singleton((req_id, req));
        require resps.is_empty();

        update sync_phase =
            AtomicBetreeSyncPhase::SuperblockWriteIssued{
                req_id,
                image,
            };
    }}

    transition! { execute_journal_sync_end(
        lbl: Label,
        journal_discarded_aus: Set<AU>,
        new_journal: AtomicJournalState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        require let AtomicBetreeSyncPhase::SuperblockWriteIssued{
            req_id,
            image,
        } = pre.sync_phase;
        require pre.client_ready();
        require pre.branch.control.frozen is None;
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::CommitComplete{
                require_end: pre.journal.journal.seq_end(),
                discarded_aus: journal_discarded_aus,
            },
        );
        require reqs.is_empty();
        require resps == Multiset::singleton((
            req_id,
            DiskResponse::WriteResp{},
        ));

        update free_aus =
            pre.free_aus + journal_discarded_aus;
        update journal = new_journal;
        update persistent_image = Some(image);
        update sync_phase = AtomicBetreeSyncPhase::None;
    }}

    transition! { execute_store_sync_begin(
        lbl: Label,
        image: AbstractSuperblockImage,
        journal_reads: Map<Address, RawPage>,
        new_cache: Cache::State,
        new_journal: AtomicJournalState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        let metadata = betree_metadata_from_superblock(image);
        let frozen_image = FrozenBranchBetree{
            root: metadata.root,
            seq_end: metadata.seq_end,
        };
        require pre.client_ready();
        require pre.sync_phase is None;
        require pre.store_sync_image_metadata_valid(image);
        require Cache::State::next(
            pre.cache,
            new_cache,
            Cache::Label::Access{
                reads: journal_reads,
                writes: Map::empty(),
            },
        );
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::CommitStart{
                snapshot: image.journal_snapshot,
                seq_end: image.journal_seq_end,
                reads: to_journal_records(journal_reads),
            },
        );
        require reqs.is_empty();
        require resps.is_empty();

        let new_atomic_branch = AtomicBranchBetreeState::State {
            control: AtomicBranchBetreeControl {
                frozen: Some(FrozenCachingDiskBranchBetree {
                    metadata,
                    aus: pre.branch.betree.durable_aus(),
                }),
                ..pre.branch.control
            },
            ..pre.branch
        };
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            new_atomic_branch,
            AtomicBranchBetreeState::Label::CommitStart {
                image: frozen_image,
            },
        );

        update cache = new_cache;
        update journal = new_journal;
        update branch = new_atomic_branch;
        update sync_phase =
            AtomicBetreeSyncPhase::Preparing{
                image,
                journal_ready: false,
                branch_ready: false,
            };
    }}

    transition! { execute_store_sync_end(
        lbl: Label,
        journal_discarded_aus: Set<AU>,
        new_journal: AtomicJournalState::State,
        reqs: Multiset<(ID, DiskRequest)>,
        resps: Multiset<(ID, DiskResponse)>,
    ) {
        require lbl is Disk;
        require let AtomicBetreeSyncPhase::SuperblockWriteIssued{
            req_id,
            image,
        } = pre.sync_phase;
        require pre.client_ready();
        require pre.branch.control.frozen is Some;
        let frozen = pre.branch.control.frozen.unwrap();
        let branch_discarded_aus =
            pre.branch.control.persistent_aus
                - frozen.aus
                - pre.branch.betree.owned_aus();
        require AtomicJournalState::State::next(
            pre.journal,
            new_journal,
            AtomicJournalState::Label::CommitComplete{
                require_end: pre.journal.journal.seq_end(),
                discarded_aus: journal_discarded_aus,
            },
        );
        require reqs.is_empty();
        require resps == Multiset::singleton((
            req_id,
            DiskResponse::WriteResp{},
        ));

        let new_atomic_branch = AtomicBranchBetreeState::State {
            control: AtomicBranchBetreeControl {
                metadata: frozen.metadata,
                persistent_aus: frozen.aus,
                frozen: None,
                ..pre.branch.control
            },
            ..pre.branch
        };
        require AtomicBranchBetreeState::State::next(
            pre.branch,
            new_atomic_branch,
            AtomicBranchBetreeState::Label::CommitComplete,
        );

        update free_aus =
            pre.free_aus
                + journal_discarded_aus
                + branch_discarded_aus;
        update journal = new_journal;
        update branch = new_atomic_branch;
        update persistent_image = Some(image);
        update sync_phase = AtomicBetreeSyncPhase::None;
    }}

    pub open spec fn valid_request_reply_pair(
        req: Request,
        reply: Reply,
    ) -> bool {
        &&& req.id == reply.id
        &&& req.input is QueryInput <==> reply.output is QueryOutput
        &&& req.input is PutInput <==> reply.output is PutOutput
        &&& req.input is NoopInput <==> reply.output is NoopOutput
    }

    pub open spec fn reserved_aus() -> Set<AU> {
        set![spec_superblock_addr().au]
    }

    pub open spec fn branch_metadata_loaded(self) -> bool {
        self.branch.control.metadata_loaded
    }

    pub open spec fn allocation_metadata_loaded(self) -> bool {
        &&& self.journal.ready()
        &&& self.branch_metadata_loaded()
        &&& (self.recovery_state is MetadataLoadComplete
            || self.recovery_state is RecoveryComplete)
    }

    pub open spec fn client_ready(self) -> bool {
        self.recovery_state is RecoveryComplete
    }

    pub open spec fn journal_sync_image_metadata_valid(
        self,
        image: AbstractSuperblockImage,
    ) -> bool {
        &&& betree_superblock_image_wf(image)
        &&& betree_metadata_from_superblock(image)
            == self.branch.control.metadata
        &&& self.journal.persistent_seq_end
            <= image.journal_seq_end
        &&& image.journal_seq_end
            <= self.journal.journal.seq_end()
    }

    pub open spec fn store_sync_image_metadata_valid(
        self,
        image: AbstractSuperblockImage,
    ) -> bool {
        let metadata = betree_metadata_from_superblock(image);
        &&& betree_superblock_image_wf(image)
        &&& metadata.root == self.branch.betree.root
        &&& metadata.seq_end == self.branch.betree.memtable.seq_end
        &&& self.journal.persistent_seq_end
            <= image.journal_seq_end
        &&& image.journal_seq_end
            <= self.journal.journal.seq_end()
    }
}}

} // verus!
