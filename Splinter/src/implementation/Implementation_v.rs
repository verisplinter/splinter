// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// Executable coordinator for UnifiedCacheBetreeSystem.

#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]

use vstd::prelude::*;
use vstd::{assert_maps_equal, assert_seqs_equal, assert_sets_equal};
use vstd::hash_map::HashMapWithView;
use vstd::modes::tracked_swap;
use vstd::multiset::Multiset;
use vstd::tokens::InstanceId;
use vstd::pervasive::unreached;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::allocation_layer::BranchTypes_v::Summary;
use crate::allocation_layer::AllocationBranchBetree_v::read_ref_aus;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU, page_count, to_aus};
use crate::implementation::AbstractSuperblock_v::{
    abstract_superblock_raw_wf, superblock_matches,
};
use crate::implementation::BranchProofUtils_v::append_puts;
use crate::implementation::AtomicBranchBetreeState_v::{
    AtomicBranchBetreeState, recovery_page_access,
};
use crate::implementation::AtomicJournalState_v::{
    AtomicJournalImage, AtomicJournalState,
};
use crate::implementation::AuLikesImpl_v::{iau_seq_set, unique_iau_seq};
use crate::implementation::AuPoolImpl_v::{
    iau_vec_set, AuAllocation, AuPoolImpl, AuRun,
};
use crate::implementation::BetreePageImpl_v::betree_addr_for_au;
use crate::implementation::BetreePathImpl_v::
    query_valid_implies_path_prefix_valid;
use crate::implementation::BetreeMaintenanceImpl_v::{
    cached_betree_root_wf, compaction_destination_addrs,
};
use crate::implementation::BetreeSplitWriteImpl_v::iaddr_views;
use crate::implementation::BetreeQueryImpl_v::cached_betree_query_valid;
use crate::implementation::BranchBetreeImpl_v::{
    BetreeMetadataImpl, BranchBetreeAbortResult,
    BranchBetreeBuildResult, BranchBetreeBulkSealResult,
    BranchBetreeBulkStartResult, BranchBetreeCommitCompleteResult,
    BranchBetreeCommitResult, BranchBetreeControlResult,
    BranchBetreeExistingFlushResult, BranchBetreeFlushResult,
    BranchBetreeImpl, BranchBetreePutResult, BranchBetreeQueryResult,
    BranchBetreeRecoveryStepResult, BranchBetreeWipResult,
    BranchBetreeCompactAbortResult, BranchBetreeCompactBeginResult,
    BranchBetreeCompactCompleteResult, BranchBetreeCompactStreamResult,
    compact_stream_entries, compactor_views,
};
use crate::implementation::BranchBetreeOwnershipImpl_v::append_unique_aus;
use crate::implementation::BranchBulkBuilderImpl_v::BranchBulkPhase;
use crate::implementation::BulkBranchImpl_v::BulkBuilderImpl;
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachingDiskBranchBetree_v::{
    BranchBuildEvent, PageAccess,
};
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::CachedBranchBetree_v::{
    CachedBranchBetree,
};
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::CompactionCandidateQueueImpl_v::{
    CompactionCandidate, CompactionCandidateQueue, CompactionEnqueueResult,
};
use crate::implementation::CompactionPickerImpl_v::{
    CompactionPickerImpl, CompactionPickerStepResult,
};
use crate::implementation::DiskLayout_v::{
    DiskLayout, spec_superblock_addr, superblock_addr,
};
use crate::implementation::FracCacheImpl_v::{
    cache_load_label, AuSetWritebackResult, FracCacheImpl, MutHandle,
    WritebackHandle, CACHE_SIZE_RECS, PAGE_SIZE_BYTES,
};
use crate::implementation::JournalImpl_v::{
    cache_agrees_with_raw_disk_on_domain, journal_disk_load_index_inv,
    BeginWritebackForTargetResult, CleanForCommitResult, FrozenJournal,
    IJournalSnapshot, JournalImpl, MarshalReserveResult,
    PrepareFreezeReadsResult,
    UnifiedRecoverIndexResult, UnifiedRecoverMapResult,
};
use crate::implementation::IBranchNode_v::iopt_addr;
use crate::implementation::JournalTypes_v::{
    journal_marshall_labels, to_journal_records,
};
use crate::implementation::MemtableImpl_v::MemtableImpl;
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::implementation::MultisetMapRelation_v::{
    multiset_map_singleton, multiset_map_singleton_ensures,
    multiset_to_map, singleton_map_values,
};
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::implementation::SyncRequestBufferImpl_v::SyncRequestBufferImpl;
use crate::implementation::StreamingBranchBuilderImpl_v::{
    StreamingBranchPhase, StreamingFinishInputResult,
    StreamingFinishLevelResult,
};
use crate::implementation::UnifiedCacheBetreeProgramModel_v::
    UnifiedCacheBetreeProgramModel;
use crate::implementation::UnifiedCacheBetreeSystem_v::{
    AtomicBetreeSyncPhase, UnifiedCacheBetreeSystem,
};
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::ImplDisk_t::{
    IAddress, IAU, IPage, IDiskGeometry, IDiskRequest, IDiskResponse,
};
use crate::implementation::SuperblockTypes_v::{
    ISuperblock, ISuperblockGeometry, ISuperblockJournalImage,
    ISuperblockPayload,
};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{ID, SyncReqId};
use crate::spec::Messages_t::{Message, Value};
use crate::trusted::ClientAPI_t::{
    ClientAPI, DiskResponseRecord, UserRequestRecord,
};
use crate::trusted::KVStoreTrait_t::{
    KVStoreTrait,
};
use crate::trusted::KVStoreTokenized_t::KVStoreTokenized;
use crate::trusted::ProgramModelTrait_t::{
    ProgramDiskInfo, ProgramLabel, ProgramModelTrait, ProgramUserOp,
};
use crate::trusted::ReqReply_t::{Input, Output, Reply, Request};
use crate::implementation::UnifiedCacheBetreeRefinementProof_v::
    UnifiedCacheBetreeRefinementProof;

verus! {

pub const BETREE_OWNERSHIP_BUCKET_COUNT: u32 = 64;
pub const BETREE_MEMTABLE_BUCKET_COUNT: u32 = 256;
pub const STORE_SYNC_INTERVAL: u64 = 3;
pub const BETREE_BRANCH_FREE_AU_THRESHOLD: IAU = 5;
pub const DEFAULT_PHYSICAL_AUS: IAU = 100;
pub const IMPLEMENTATION_PAGES_PER_AU: IPage = 7;
pub const COMPACTION_CANDIDATE_CAPACITY: usize = 16;
pub const TEST_NON_ROOT_COMPACTION_PICKER: bool = false;

pub type ModelShard =
    KVStoreTokenized::model<UnifiedCacheBetreeProgramModel>;
pub type DiskRespShard =
    KVStoreTokenized::disk_responses_multiset<UnifiedCacheBetreeProgramModel>;
pub type RequestShard =
    KVStoreTokenized::requests<UnifiedCacheBetreeProgramModel>;

#[derive(Debug, Copy, Clone)]
pub enum RecoveryPhase {
    FetchingSuperblock,
    LoadingJournal,
    LoadingBranch,
    ReplayingJournal,
    ReadyForUserOperation,
}

#[derive(Clone, Copy, Debug)]
pub enum CacheReadPurpose {
    JournalIndex,
    BranchMetadata,
    ClientQuery,
    SyncJournalRoot,
    MemtableFlushRoot,
    CompactionDiscovery,
    CompactionExecute,
}

#[derive(Debug, Copy, Clone)]
pub enum CompactionWorkPhase {
    Begin,
    OutputCreation,
    InitializeCursors,
    Scanning,
    FinishingInput,
    FinishingLevels,
    Sealing,
    Completing,
    AbortCompactor,
    AbortBranch,
}

#[derive(Debug, Copy, Clone)]
pub struct CompactionWorkItem {
    pub candidate: CompactionCandidate,
    pub phase: CompactionWorkPhase,
    pub input_idx: Option<usize>,
    pub output_idx: Option<usize>,
}

pub enum PendingClientOp {
    Put {
        req: Request,
        req_shard: Tracked<RequestShard>,
        key: Key,
        value: Value,
    },
    Query {
        req: Request,
        req_shard: Tracked<RequestShard>,
        key: Key,
    },
}

pub enum BetreeSyncPhaseImpl {
    None,
    Preparing {
        image: crate::implementation::SuperblockTypes_v::ISuperblock,
        journal_ready: bool,
        branch_ready: bool,
    },
    SuperblockWriteIssued {
        image: crate::implementation::SuperblockTypes_v::ISuperblock,
        req_id: ID,
    },
}

#[derive(Debug, Copy, Clone)]
pub enum StoreFlushPhaseImpl {
    None,
    Pending,
    Building { idx: usize, seq_end: u64 },
    Sealed { idx: usize, seq_end: u64 },
    Ready { seq_end: u64 },
}

enum StoreRootFlushAttempt {
    Flushed {
        prepared_cache: Ghost<Cache::State>,
        access: Ghost<PageAccess>,
        allocs: Ghost<Set<AU>>,
        deallocs: Ghost<Set<AU>>,
        reclaimed: Vec<IAU>,
    },
    NeedCacheLoad { addr: IAddress, handle: MutHandle },
    CacheFull,
    Blocked,
    InvalidPage,
}

#[derive(Debug, Copy, Clone)]
pub enum ReadyClientStepResult {
    Progress,
    Idle,
    ExitRequested,
}

#[derive(Debug, Copy, Clone)]
pub enum ReadyBackgroundStepResult {
    Progress,
    Idle,
}

pub enum OutstandingReqInfo {
    CacheRead {
        addr: IAddress,
        load_handle: MutHandle,
        purpose: CacheReadPurpose,
    },
    CacheWrite {
        addr: IAddress,
        write_handle: WritebackHandle,
    },
    SuperblockWrite,
}

pub struct Implementation {
    pub disk_au_count: IAU,
    pub disk_page_count: IPage,
    pub recovery_phase: RecoveryPhase,
    pub cache: FracCacheImpl,
    pub journal: JournalImpl,
    pub branch: BranchBetreeImpl,
    pub au_pool: AuPoolImpl,
    pub persistent_journal_seq_end: u64,
    pub sync_requests: SyncRequestBufferImpl,
    pub sync_counter: u64,
    pub sync_phase: BetreeSyncPhaseImpl,
    pub store_flush_phase: StoreFlushPhaseImpl,
    pub compaction_candidates: CompactionCandidateQueue,
    pub compaction_picker: CompactionPickerImpl,
    pub compaction_work: Option<CompactionWorkItem>,
    pub outstanding_requests: HashMapWithView<ID, OutstandingReqInfo>,
    pub pending_client_op: Option<PendingClientOp>,
    pub model: Tracked<ModelShard>,
    pub instance: Tracked<
        KVStoreTokenized::Instance<UnifiedCacheBetreeProgramModel>,
    >,
}

impl Implementation {
    pub closed spec fn state(&self) -> UnifiedCacheBetreeSystem::State {
        self.model@.value().state
    }

    pub closed spec fn instance_id(&self) -> InstanceId {
        self.instance@.id()
    }

    pub closed spec fn outstanding_requests_wf(&self) -> bool {
        forall |id: ID|
            #[trigger] self.outstanding_requests@.contains_key(id)
            ==> match self.outstanding_requests@[id] {
                OutstandingReqInfo::CacheRead {
                    addr,
                    load_handle,
                    ..
                } => {
                    &&& self.cache.entry_fetched(&addr)
                    &&& self.cache.valid_load_handle(&addr, load_handle)
                },
                OutstandingReqInfo::CacheWrite {
                    addr,
                    write_handle,
                } => {
                    &&& self.cache.entry_fetched(&addr)
                    &&& self.cache.valid_writeback_handle(
                        &addr,
                        write_handle,
                    )
                },
                OutstandingReqInfo::SuperblockWrite => true,
            }
    }

    pub closed spec fn outstanding_cache_reqs_match_model(&self) -> bool {
        &&& forall |id: ID|
            #[trigger] self.state().outstanding_cache_reqs.contains_key(id)
            ==> {
                &&& self.outstanding_requests@.contains_key(id)
                &&& match self.outstanding_requests@[id] {
                    OutstandingReqInfo::CacheRead { addr, .. } => {
                        self.state().outstanding_cache_reqs[id] == addr@
                    },
                    OutstandingReqInfo::CacheWrite { addr, .. } => {
                        self.state().outstanding_cache_reqs[id] == addr@
                    },
                    OutstandingReqInfo::SuperblockWrite => false,
                }
            }
        &&& forall |id: ID|
            #[trigger] self.outstanding_requests@.contains_key(id)
            ==> {
                &&& match self.outstanding_requests@[id] {
                    OutstandingReqInfo::CacheRead { addr, .. } => {
                        &&& self.state().outstanding_cache_reqs
                            .contains_key(id)
                        &&& self.state().outstanding_cache_reqs[id] == addr@
                    },
                    OutstandingReqInfo::CacheWrite { addr, .. } => {
                        &&& self.state().outstanding_cache_reqs
                            .contains_key(id)
                        &&& self.state().outstanding_cache_reqs[id] == addr@
                    },
                    OutstandingReqInfo::SuperblockWrite => {
                        !self.state().outstanding_cache_reqs.contains_key(id)
                    },
                }
            }
    }

    pub closed spec fn outstanding_requests_single_flight(&self) -> bool {
        forall |left: ID, right: ID| {
            &&& #[trigger] self.outstanding_requests@.contains_key(left)
            &&& #[trigger] self.outstanding_requests@.contains_key(right)
        } ==> left == right
    }

    pub closed spec fn pending_client_op_wf(&self) -> bool {
        match self.pending_client_op {
            None => true,
            Some(PendingClientOp::Put {
                req,
                req_shard,
                key,
                value,
            }) => {
                &&& req.input == Input::PutInput { key, value }
                &&& req_shard@.instance_id() == self.instance_id()
                &&& req_shard@.element() == req
            },
            Some(PendingClientOp::Query {
                req,
                req_shard,
                key,
            }) => {
                &&& req.input == Input::QueryInput { key }
                &&& req_shard@.instance_id() == self.instance_id()
                &&& req_shard@.element() == req
            },
        }
    }

    pub closed spec fn sync_wf(&self) -> bool {
        let ids = self.sync_requests.all_ids();
        &&& self.sync_requests.ids_unique()
        &&& ids.to_set() =~= self.state().sync_req_map.dom()
        &&& forall |id: ID|
            #[trigger] self.outstanding_requests@.contains_key(id)
                && self.outstanding_requests@[id] is SuperblockWrite
            ==> match &self.sync_phase {
                BetreeSyncPhaseImpl::SuperblockWriteIssued {
                    req_id,
                    ..
                } => *req_id == id,
                _ => false,
            }
        &&& (!(self.recovery_phase is ReadyForUserOperation) ==> {
            &&& ids.len() == 0
            &&& self.sync_phase is None
        })
        &&& forall |i: int|
            0 <= i < self.sync_requests.buffered_reqs@.len()
            ==> #[trigger] self.state().sync_req_map[
                self.sync_requests.buffered_reqs@[i]
            ] <= self.state().branch.betree.memtable.seq_end
        &&& forall |i: int|
            0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
            ==> #[trigger] self.state().sync_req_map[
                self.sync_requests.journal_cleaning_reqs@[i]
            ] <= self.sync_requests.sync_target_lsn as nat
        &&& self.sync_requests.journal_cleaning_reqs@.len() > 0 ==>
            self.state().journal.persistent_seq_end
                <= self.sync_requests.sync_target_lsn as nat
        &&& match &self.sync_phase {
            BetreeSyncPhaseImpl::None => {
                &&& self.state().sync_phase is None
                &&& self.state().journal.in_flight is None
                &&& self.state().branch.control.frozen is None
                &&& forall |i: int|
                    0 <= i < self.sync_requests.superblocking_reqs@.len()
                    ==> #[trigger] self.state().sync_req_map[
                        self.sync_requests.superblocking_reqs@[i]
                    ] <= self.state().journal.persistent_seq_end
            },
            BetreeSyncPhaseImpl::Preparing {
                image,
                journal_ready,
                branch_ready,
            } => {
                &&& self.state().sync_phase
                    == AtomicBetreeSyncPhase::Preparing {
                        image: image@@,
                        journal_ready: *journal_ready,
                        branch_ready: *branch_ready,
                    }
                &&& self.sync_requests.journal_cleaning_reqs@.len() > 0
                &&& self.sync_requests.superblocking_reqs@.len() == 0
                &&& self.sync_requests.sync_target_lsn as nat
                    <= image@@.journal_seq_end
                &&& image@.wf()
                &&& image.geometry.pages_per_au == self.disk_page_count
                &&& image.geometry.formatted_au_count == self.disk_au_count
                &&& self.state().journal.in_flight
                    == Some(AtomicJournalImage {
                        snapshot: image@@.journal_snapshot,
                        seq_end: image@@.journal_seq_end,
                    })
                &&& (self.state().branch.control.frozen is None ==> {
                    &&& *branch_ready
                    &&& image.payload.journal.snapshot.boundary_lsn as nat
                        == self.journal.seq_start()
                })
                &&& (self.state().branch.control.frozen is Some ==> {
                    &&& self.branch_owned_aus_bounded()
                    &&& self.branch.control.frozen_metadata is Some
                    &&& self.branch.control.frozen_metadata.unwrap().root
                        == image.payload.branch
                    &&& self.branch.ownership.frozen_aus()
                        == self.branch.ownership.current_durable_aus()
                    &&& self.branch.wip_branches@.len() == 0
                    &&& image.payload.journal.snapshot.freshest_rec is None
                    &&& image.payload.journal.snapshot.boundary_lsn
                        == image.payload.journal.seq_end
                    &&& self.journal.seq_start()
                        <= image.payload.journal.seq_end as nat
                        <= self.journal.marshalled_seq_end()
                })
            },
            BetreeSyncPhaseImpl::SuperblockWriteIssued { image, req_id } => {
                &&& self.state().sync_phase
                    == AtomicBetreeSyncPhase::SuperblockWriteIssued {
                        req_id: *req_id,
                        image: image@@,
                    }
                &&& self.sync_requests.journal_cleaning_reqs@.len() == 0
                &&& self.sync_requests.superblocking_reqs@.len() > 0
                &&& image@.wf()
                &&& image.geometry.pages_per_au == self.disk_page_count
                &&& image.geometry.formatted_au_count == self.disk_au_count
                &&& self.outstanding_requests@.contains_key(*req_id)
                &&& self.outstanding_requests@[*req_id]
                    is SuperblockWrite
                &&& self.state().journal.in_flight
                    == Some(AtomicJournalImage {
                        snapshot: image@@.journal_snapshot,
                        seq_end: image@@.journal_seq_end,
                    })
                &&& (self.state().branch.control.frozen is None ==> {
                    image.payload.journal.snapshot.boundary_lsn as nat
                        == self.journal.seq_start()
                })
                &&& (self.state().branch.control.frozen is Some ==> {
                    &&& self.branch_owned_aus_bounded()
                    &&& self.branch.control.frozen_metadata is Some
                    &&& self.branch.control.frozen_metadata.unwrap().root
                        == image.payload.branch
                    &&& self.branch.ownership.frozen_aus()
                        == self.branch.ownership.current_durable_aus()
                    &&& self.branch.wip_branches@.len() == 0
                    &&& image.payload.journal.snapshot.freshest_rec is None
                    &&& image.payload.journal.snapshot.boundary_lsn
                        == image.payload.journal.seq_end
                    &&& self.journal.seq_start()
                        <= image.payload.journal.seq_end as nat
                        <= self.journal.marshalled_seq_end()
                })
                &&& forall |i: int|
                    0 <= i < self.sync_requests.superblocking_reqs@.len()
                    ==> #[trigger] self.state().sync_req_map[
                        self.sync_requests.superblocking_reqs@[i]
                    ] <= image@@.journal_seq_end
            },
        }
    }

    pub closed spec fn store_flush_wf(&self) -> bool {
        &&& self.sync_counter < STORE_SYNC_INTERVAL
        &&& (!(self.recovery_phase is ReadyForUserOperation) ==> {
            &&& self.sync_counter == 0
            &&& self.store_flush_phase is None
        })
        &&& match self.store_flush_phase {
            StoreFlushPhaseImpl::None => true,
            StoreFlushPhaseImpl::Pending => {
                &&& self.sync_phase is None
                &&& self.sync_requests.journal_cleaning_reqs@.len() > 0
                &&& self.sync_requests.superblocking_reqs@.len() == 0
                &&& self.sync_requests.sync_target_lsn as nat
                    <= self.state().branch.betree.memtable.seq_end
            },
            StoreFlushPhaseImpl::Building { idx, seq_end } => {
                &&& self.sync_phase is None
                &&& self.sync_requests.journal_cleaning_reqs@.len() > 0
                &&& self.sync_requests.superblocking_reqs@.len() == 0
                &&& self.sync_requests.sync_target_lsn <= seq_end
                &&& idx < self.branch.wip_branches@.len()
                &&& self.branch.wip_branches@.len() == 1
                &&& self.branch.wip_branches@[idx as int]
                    .has_memtable_builder()
                &&& !self.branch.wip_branches@[idx as int].sealed
                &&& self.branch.wip_branches@[idx as int]
                    .mini_allocator.bounded(self.disk_au_count)
                &&& self.branch.wip_branches@[idx as int]
                    .mini_allocator.i().all_aus().disjoint(
                        self.branch.control_i().protected_aus(),
                    )
                &&& self.branch.wip_branches@[idx as int]
                    .mini_allocator.i().all_aus().disjoint(
                        self.branch.ownership.betree.all_aus()
                            + self.branch.ownership.branches
                                .all_summary_aus(),
                    )
                &&& self.branch.wip_branches@[idx as int]
                    .mini_allocator.i().all_aus().disjoint(
                        self.journal.owned_aus(),
                    )
                &&& self.cache@.inv()
                &&& self.branch.wip_branches@[idx as int]
                    .cache_inv(self.cache@)
                &&& self.branch.memtable.seq_end == seq_end
                &&& !self.branch.memtable@.is_empty()
            },
            StoreFlushPhaseImpl::Sealed { idx, seq_end } => {
                &&& self.sync_phase is None
                &&& self.sync_requests.journal_cleaning_reqs@.len() > 0
                &&& self.sync_requests.superblocking_reqs@.len() == 0
                &&& self.sync_requests.sync_target_lsn <= seq_end
                &&& idx < self.branch.wip_branches@.len()
                &&& self.branch.wip_branches@.len() == 1
                &&& self.branch.wip_branches@[idx as int]
                    .bulk_builder is None
                &&& self.branch.wip_branches@[idx as int].sealed
                &&& self.branch.wip_branches@[idx as int]
                    .sealed_branch@ is Some
                &&& self.branch.wip_branches@[idx as int]
                    .sealed_branch@.unwrap().i().i().map
                    == self.branch.memtable@.buffer.map
                &&& self.branch.wip_branches@[idx as int]
                    .mini_allocator.bounded(self.disk_au_count)
                &&& self.branch.wip_branches@[idx as int]
                    .mini_allocator.i().all_aus().disjoint(
                        self.branch.control_i().protected_aus(),
                    )
                &&& self.branch.wip_branches@[idx as int]
                    .mini_allocator.i().all_aus().disjoint(
                        self.branch.ownership.betree.all_aus()
                            + self.branch.ownership.branches
                                .all_summary_aus(),
                    )
                &&& self.branch.wip_branches@[idx as int]
                    .mini_allocator.i().all_aus().disjoint(
                        self.journal.owned_aus(),
                    )
                &&& self.cache@.inv()
                &&& self.branch.wip_branches@[idx as int]
                    .cache_inv(self.cache@)
                &&& self.branch.memtable.seq_end == seq_end
                &&& !self.branch.memtable@.is_empty()
            },
            StoreFlushPhaseImpl::Ready { seq_end } => {
                &&& self.sync_phase is None
                &&& self.sync_requests.journal_cleaning_reqs@.len() > 0
                &&& self.sync_requests.superblocking_reqs@.len() == 0
                &&& self.sync_requests.sync_target_lsn <= seq_end
                &&& self.branch.wip_branches@.len() == 0
                &&& self.branch.memtable.seq_end == seq_end
                &&& self.branch.memtable@.is_empty()
            },
        }
    }

    pub closed spec fn branch_owned_aus_bounded(&self) -> bool {
        forall |au: AU| #[trigger]
            (self.branch.ownership.betree.all_aus()
                + self.branch.ownership.branches.all_summary_aus())
                .contains(au)
            ==> 0 < au && au < self.disk_au_count as nat
    }

    pub closed spec fn phase_alignment(&self) -> bool {
        match self.recovery_phase {
            RecoveryPhase::FetchingSuperblock => {
                &&& (self.state().recovery_state is Begin
                    || self.state().recovery_state is AwaitingSuperblock)
                &&& !self.branch.control.installed
                &&& self.branch@
                    == AtomicBranchBetreeState::State::empty()
            },
            RecoveryPhase::LoadingJournal => {
                &&& self.state().recovery_state is SuperblockAvailable
                &&& !self.journal.index_ready()
                &&& self.journal.journal_alloc.i()
                    == MiniAllocator::empty()
                &&& self.journal.snapshot_geometry_bounded(
                    self.disk_au_count,
                )
                &&& self.branch.control.installed
                &&& !self.branch.control.loading
                &&& !self.branch.control.metadata_loaded
                &&& self.branch.control.frozen_metadata is None
                &&& self.branch.wip_branches@.len() == 0
            },
            RecoveryPhase::LoadingBranch => {
                &&& self.state().recovery_state is SuperblockAvailable
                &&& self.journal.wf()
                &&& self.journal.index_ready()
                &&& self.journal.no_unmarshalled_entries()
                &&& self.journal.index_aus_bounded(self.disk_au_count)
                &&& self.branch.control.installed
                &&& self.branch.control.frozen_metadata is None
                &&& self.branch.wip_branches@.len() == 0
            },
            RecoveryPhase::ReplayingJournal => {
                &&& self.state().recovery_state is MetadataLoadComplete
                &&& self.journal.wf()
                &&& self.journal.index_ready()
                &&& self.journal.no_unmarshalled_entries()
                &&& self.journal.index_aus_bounded(self.disk_au_count)
                &&& self.branch.control.metadata_loaded
                &&& self.branch.wip_branches@.len() == 0
            },
            RecoveryPhase::ReadyForUserOperation => {
                &&& self.state().recovery_state is RecoveryComplete
                &&& self.journal.wf()
                &&& self.journal.index_ready()
                &&& self.journal.index_aus_bounded(self.disk_au_count)
                &&& self.branch.control.metadata_loaded
                &&& self.state().journal.journal.seq_end()
                    == self.state().branch.betree.memtable.seq_end
            },
        }
    }

    pub closed spec fn common_inv(&self) -> bool {
        &&& self.model@.instance_id() == self.instance@.id()
        &&& 1 < self.disk_au_count as nat
        &&& self.disk_page_count as nat == page_count()
        &&& 0 < self.disk_page_count as nat
        &&& self.cache.wf()
        &&& self.journal.basic_wf()
        &&& self.journal.journal_alloc.bounded(self.disk_au_count)
        &&& MiniAllocatorImpl::allocators_unique(
            self.journal.journal_alloc.allocators@,
        )
        &&& self.journal.allocator_index_aligned()
        &&& self.au_pool@.disjoint(self.journal.owned_aus())
        &&& self.branch.wf()
        &&& self.compaction_executor_wf()
        &&& self.compaction_candidates.wf()
        &&& self.compaction_candidates.capacity
            == COMPACTION_CANDIDATE_CAPACITY
        &&& forall |i: int|
            0 <= i < self.compaction_candidates.entries@.len()
            ==> (#[trigger] self.compaction_candidates.entries@[i]).fuel
                == CACHE_SIZE_RECS
        &&& self.compaction_picker.wf()
        &&& self.branch_owned_aus_bounded()
        &&& self.branch.control.metadata.root is Some ==>
            self.branch.control.metadata.root.unwrap()@.au
                < self.disk_au_count as nat
        &&& self.au_pool.canonical_wf(self.disk_au_count)
        &&& self.state().journal.journal == self.journal@
        &&& self.state().journal.mini_allocator
            == self.journal.journal_alloc.i()
        &&& self.state().journal.persistent_seq_end
            == self.persistent_journal_seq_end as nat
        &&& self.state().branch == self.branch@
        &&& self.state().free_aus =~= self.au_pool@
        &&& self.outstanding_requests_wf()
        &&& self.outstanding_cache_reqs_match_model()
        &&& self.outstanding_requests_single_flight()
        &&& self.pending_client_op_wf()
        &&& self.sync_wf()
        &&& self.store_flush_wf()
        &&& !(self.recovery_phase is ReadyForUserOperation)
            ==> self.pending_client_op is None
        &&& forall |id: ID|
            #[trigger] self.outstanding_requests@.contains_key(id)
            ==> {
            &&& !(self.state().recovery_state is Begin)
            &&& !(self.state().recovery_state is AwaitingSuperblock)
        }
        &&& self.phase_alignment()
    }

    pub open spec fn same_non_cache_io_state(
        pre: &Implementation,
        post: &Implementation,
    ) -> bool {
        &&& post.disk_au_count == pre.disk_au_count
        &&& post.disk_page_count == pre.disk_page_count
        &&& post.recovery_phase == pre.recovery_phase
        &&& post.journal == pre.journal
        &&& post.branch == pre.branch
        &&& post.au_pool == pre.au_pool
        &&& post.persistent_journal_seq_end
            == pre.persistent_journal_seq_end
        &&& post.sync_requests == pre.sync_requests
        &&& post.sync_counter == pre.sync_counter
        &&& post.sync_phase == pre.sync_phase
        &&& post.store_flush_phase == pre.store_flush_phase
        &&& post.compaction_picker == pre.compaction_picker
        &&& post.pending_client_op == pre.pending_client_op
        &&& post.instance@ == pre.instance@
        &&& post.state().recovery_state == pre.state().recovery_state
        &&& post.state().free_aus =~= pre.state().free_aus
        &&& post.state().journal == pre.state().journal
        &&& post.state().branch == pre.state().branch
        &&& post.state().persistent_image == pre.state().persistent_image
        &&& post.state().sync_phase == pre.state().sync_phase
        &&& post.state().sync_req_map == pre.state().sync_req_map
    }

    pub open spec fn same_journal_sync_stable_state(
        pre: &Implementation,
        post: &Implementation,
    ) -> bool {
        &&& post.disk_au_count == pre.disk_au_count
        &&& post.disk_page_count == pre.disk_page_count
        &&& post.recovery_phase == pre.recovery_phase
        &&& post.cache == pre.cache
        &&& post.branch == pre.branch
        &&& post.au_pool == pre.au_pool
        &&& post.sync_requests == pre.sync_requests
        &&& post.sync_counter == pre.sync_counter
        &&& post.store_flush_phase == pre.store_flush_phase
        &&& post.compaction_candidates == pre.compaction_candidates
        &&& post.compaction_picker == pre.compaction_picker
        &&& post.compaction_work == pre.compaction_work
        &&& post.pending_client_op == pre.pending_client_op
        &&& post.instance@ == pre.instance@
        &&& post.state().recovery_state == pre.state().recovery_state
        &&& post.state().cache == pre.state().cache
        &&& post.state().free_aus =~= pre.state().free_aus
        &&& post.state().branch == pre.state().branch
        &&& post.state().sync_req_map == pre.state().sync_req_map
    }

    pub closed spec fn compaction_executor_wf(&self) -> bool {
        match self.compaction_work {
            None => {
                &&& self.branch.compactors@.len() == 0
                &&& (self.recovery_phase is ReadyForUserOperation
                        && (self.store_flush_phase is None
                            || self.store_flush_phase is Pending
                            || self.store_flush_phase is Ready)
                    ==> self.branch.wip_branches@.len() == 0)
            },
            Some(work) => {
                &&& work.candidate.wf()
                &&& work.candidate.fuel == CACHE_SIZE_RECS
                &&& self.recovery_phase is ReadyForUserOperation
                &&& self.sync_phase is None
                &&& self.store_flush_phase is None
                &&& read_ref_aus(compactor_views(
                    self.branch.compactors@,
                )) <= self.branch.branch_likes@.dom()
                &&& (work.phase is Begin || self.branch.root is Some)
                &&& (work.output_idx == Some(0usize) ==> {
                    &&& self.branch.wip_branches@.len() == 1
                    &&& self.branch.wip_branches@[0]
                        .mini_allocator.bounded(self.disk_au_count)
                    &&& self.branch.wip_branches@[0]
                        .mini_allocator.i().all_aus().disjoint(
                            self.branch.control_i().protected_aus(),
                        )
                    &&& self.branch.wip_branches@[0]
                        .mini_allocator.i().all_aus().disjoint(
                            self.branch.ownership.betree.all_aus()
                                + self.branch.ownership.branches
                                    .all_summary_aus(),
                        )
                    &&& self.branch.wip_branches@[0]
                        .mini_allocator.i().all_aus().disjoint(
                            self.journal.owned_aus(),
                        )
                    &&& self.branch.wip_branches@[0]
                        .cache_inv(self.cache@)
                })
                &&& match work.phase {
                    CompactionWorkPhase::Begin => {
                        &&& work.input_idx is None
                        &&& work.output_idx is None
                        &&& self.branch.compactors@.len() == 0
                        &&& self.branch.wip_branches@.len() == 0
                    },
                    CompactionWorkPhase::OutputCreation => {
                        &&& work.input_idx == Some(0usize)
                        &&& work.output_idx is None
                        &&& self.branch.compactors@.len() == 1
                        &&& self.branch.compactors@[0].merge is None
                        &&& self.branch.wip_branches@.len() == 0
                    },
                    CompactionWorkPhase::InitializeCursors => {
                        &&& work.input_idx == Some(0usize)
                        &&& work.output_idx == Some(0usize)
                        &&& self.branch.compactors@.len() == 1
                        &&& self.branch.compactors@[0].merge is None
                        &&& self.branch.wip_branches@.len() == 1
                        &&& self.branch.wip_branches@[0]
                            .has_streaming_builder()
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().phase is Reading
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().source_entries@.len() == 0
                    },
                    CompactionWorkPhase::Scanning => {
                        &&& work.input_idx == Some(0usize)
                        &&& work.output_idx == Some(0usize)
                        &&& self.branch.compactors@.len() == 1
                        &&& self.branch.compactors@[0].merge is Some
                        &&& !self.branch.compactors@[0].merge_done
                        &&& self.branch.compactors@[0]
                            .cache_inv(self.cache@)
                        &&& self.branch.wip_branches@.len() == 1
                        &&& self.branch.wip_branches@[0]
                            .has_streaming_builder()
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().phase is Reading
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().source_entries@
                            == compact_stream_entries(
                                self.branch.compactors@[0]
                                    .merge->0.output@,
                            )
                    },
                    CompactionWorkPhase::FinishingInput => {
                        &&& work.input_idx == Some(0usize)
                        &&& work.output_idx == Some(0usize)
                        &&& self.branch.compactors@.len() == 1
                        &&& self.branch.compactors@[0].merge_done
                        &&& self.branch.wip_branches@.len() == 1
                        &&& self.branch.wip_branches@[0]
                            .has_streaming_builder()
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().phase is Reading
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().source_entries@
                            == compact_stream_entries(
                                self.branch.compactors@[0]
                                    .merge->0.output@,
                            )
                    },
                    CompactionWorkPhase::FinishingLevels => {
                        &&& work.input_idx == Some(0usize)
                        &&& work.output_idx == Some(0usize)
                        &&& self.branch.compactors@.len() == 1
                        &&& self.branch.compactors@[0].merge_done
                        &&& self.branch.wip_branches@.len() == 1
                        &&& self.branch.wip_branches@[0]
                            .has_streaming_builder()
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().phase is Finishing
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().source_entries@
                            == compact_stream_entries(
                                self.branch.compactors@[0]
                                    .merge->0.output@,
                            )
                    },
                    CompactionWorkPhase::Sealing => {
                        &&& work.input_idx == Some(0usize)
                        &&& work.output_idx == Some(0usize)
                        &&& self.branch.compactors@.len() == 1
                        &&& self.branch.compactors@[0].merge_done
                        &&& self.branch.wip_branches@.len() == 1
                        &&& self.branch.wip_branches@[0]
                            .has_streaming_builder()
                        &&& (self.branch.wip_branches@[0]
                            .streaming_builder().phase is ReadyLeafRoot
                            || self.branch.wip_branches@[0]
                                .streaming_builder().phase is ReadyIndexRoot)
                        &&& self.branch.wip_branches@[0]
                            .streaming_builder().source_entries@
                            == compact_stream_entries(
                                self.branch.compactors@[0]
                                    .merge->0.output@,
                            )
                    },
                    CompactionWorkPhase::Completing => {
                        &&& work.input_idx == Some(0usize)
                        &&& work.output_idx == Some(0usize)
                        &&& self.branch.compactors@.len() == 1
                        &&& self.branch.compactors@[0].merge_done
                        &&& self.branch.wip_branches@.len() == 1
                        &&& self.branch.wip_branches@[0].sealed
                        &&& self.branch.wip_branches@[0]
                            .sealed_branch@ is Some
                        &&& self.branch.wip_branches@[0].sealed_source@
                            == Some(crate::implementation::MemtableImpl_v::
                                MemtableBucket::entries_map(
                                compact_stream_entries(
                                    self.branch.compactors@[0]
                                        .merge->0.output@,
                                ),
                            ))
                    },
                    CompactionWorkPhase::AbortCompactor => {
                        &&& work.input_idx == Some(0usize)
                        &&& self.branch.compactors@.len() == 1
                        &&& (work.output_idx is None
                            || work.output_idx == Some(0usize))
                        &&& (work.output_idx is None
                            ==> self.branch.wip_branches@.len() == 0)
                        &&& (work.output_idx == Some(0usize)
                            ==> self.branch.wip_branches@.len() == 1)
                    },
                    CompactionWorkPhase::AbortBranch => {
                        &&& work.input_idx is None
                        &&& work.output_idx == Some(0usize)
                        &&& self.branch.compactors@.len() == 0
                        &&& self.branch.wip_branches@.len() == 1
                    },
                }
            },
        }
    }

    pub closed spec fn inv(&self) -> bool {
        &&& self.common_inv()
        &&& self.state().cache == self.cache@
    }

    pub closed spec fn cache_read_io_lag_inv(&self) -> bool {
        &&& self.common_inv()
        &&& self.outstanding_requests@
            == Map::<ID, OutstandingReqInfo>::empty()
        &&& self.state().outstanding_cache_reqs
            == Map::<ID, Address>::empty()
    }

    pub closed spec fn wf_init(&self) -> bool {
        &&& self.inv()
        &&& self.recovery_phase is FetchingSuperblock
        &&& self.state().recovery_state is Begin
        &&& self.outstanding_requests@
            == Map::<ID, OutstandingReqInfo>::empty()
    }

    pub closed spec fn inv_api(
        &self,
        api: &ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> bool {
        &&& self.inv()
        &&& self.instance_id() == api.instance_id()
    }

    pub fn new(geometry: IDiskGeometry) -> (out: Self)
        requires
            1 < geometry.physical_au_count as nat,
            geometry.pages_per_au as nat == page_count(),
            0 < geometry.pages_per_au as nat,
        ensures out.wf_init(),
    {
        let cache = FracCacheImpl::new();
        let journal = JournalImpl::new(IJournalSnapshot::new_empty(0), 0);
        let branch = BranchBetreeImpl::new(
            BETREE_OWNERSHIP_BUCKET_COUNT,
            BETREE_MEMTABLE_BUCKET_COUNT,
        );
        let au_pool = AuPoolImpl::new(geometry.physical_au_count);
        let ghost free_aus = au_pool@;
        let ghost initial_state = UnifiedCacheBetreeSystem::State {
            recovery_state: RecoveryState::Begin,
            cache: cache@,
            outstanding_cache_reqs: Map::<ID, Address>::empty(),
            free_aus,
            journal: AtomicJournalState::State::empty(),
            branch: AtomicBranchBetreeState::State::empty(),
            persistent_image: None,
            sync_phase: AtomicBetreeSyncPhase::None,
            sync_req_map: Map::<SyncReqId, nat>::empty(),
        };

        proof {
            assert(free_aus.disjoint(
                UnifiedCacheBetreeSystem::State::reserved_aus(),
            )) by {
                assert(spec_superblock_addr().au == 0);
                assert(UnifiedCacheBetreeSystem::State::reserved_aus()
                    =~= set![0nat]) by {

                }
                assert(!free_aus.contains(0));
            }
            assert(UnifiedCacheBetreeSystem::State::initialize(
                initial_state,
                cache.total_slots() as nat,
                free_aus,
            )) by {
                assert(initial_state.cache
                    == Cache::State::empty(cache.total_slots() as nat));
            }
            assert(UnifiedCacheBetreeSystem::State::init_by(
                initial_state,
                UnifiedCacheBetreeSystem::Config::initialize(
                    cache.total_slots() as nat,
                    free_aus,
                ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::init_by);
            }
            assert(UnifiedCacheBetreeSystem::State::init(initial_state)) by {
                reveal(UnifiedCacheBetreeSystem::State::init);
            }
        }

        let tracked (
            Tracked(instance),
            Tracked(model),
            Tracked(requests),
            Tracked(replies),
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize(
            UnifiedCacheBetreeProgramModel { state: initial_state },
        );

        let out = Self {
            disk_au_count: geometry.physical_au_count,
            disk_page_count: geometry.pages_per_au,
            recovery_phase: RecoveryPhase::FetchingSuperblock,
            cache,
            journal,
            branch,
            au_pool,
            persistent_journal_seq_end: 0,
            sync_requests: SyncRequestBufferImpl::new_empty(),
            sync_counter: 0,
            sync_phase: BetreeSyncPhaseImpl::None,
            store_flush_phase: StoreFlushPhaseImpl::None,
            compaction_candidates: CompactionCandidateQueue::new(
                COMPACTION_CANDIDATE_CAPACITY,
            ),
            compaction_picker: CompactionPickerImpl::new(
                TEST_NON_ROOT_COMPACTION_PICKER,
            ),
            compaction_work: None,
            outstanding_requests: HashMapWithView::new(),
            pending_client_op: None,
            model: Tracked(model),
            instance: Tracked(instance),
        };
        proof {
            out.journal.view_ensures();
            assert(!out.journal.index_ready());
            assert(out.state().journal.journal == out.journal@);
            assert(out.state().journal.mini_allocator
                == out.journal.journal_alloc.i());
            assert(out.phase_alignment());
            assert(out.outstanding_requests_wf());
            assert(out.outstanding_cache_reqs_match_model());
            assert(out.outstanding_requests_single_flight());
            assert(out.branch.wip_branches@.len() == 0);
            assert(out.common_inv()) by {
                reveal(Implementation::common_inv);
            }
            assert(out.inv());
        }
        out
    }

    pub fn recover_begin(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is FetchingSuperblock,
            old(self).state().recovery_state is Begin,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase is FetchingSuperblock,
            self.state().recovery_state is AwaitingSuperblock,
    {
        api.log("unified-cache Betree recovery begins");
        let ghost pre_state = self.model@.value();
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        let req_id_perm = Tracked(api.send_disk_request_predict_id());
        let disk_req = IDiskRequest::ReadReq { from: superblock_addr() };
        let ghost disk_request_tuples =
            multiset_map_singleton(req_id_perm@, disk_req@);
        let ghost disk_response_tuples = Multiset::empty();
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                recovery_state: RecoveryState::AwaitingSuperblock,
                ..pre_state.state
            },
        };

        proof {
            multiset_map_singleton_ensures(req_id_perm@, disk_req@);
            assert(disk_req@
                == DiskRequest::ReadReq { from: spec_superblock_addr() });
            assert(disk_request_tuples == Multiset::singleton((
                req_id_perm@,
                DiskRequest::ReadReq {
                    from: spec_superblock_addr(),
                },
            )));
            assert(UnifiedCacheBetreeSystem::State::initiate_recovery(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                req_id_perm@,
                disk_request_tuples,
                disk_response_tuples,
            ));
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                UnifiedCacheBetreeSystem::Step::initiate_recovery(
                    req_id_perm@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            let info = ProgramDiskInfo {
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheBetreeProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheBetreeSystem::Step::initiate_recovery(
                    req_id_perm@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
                info,
            ));
            UnifiedCacheBetreeProgramModel::lift_disk_step(
                pre_state,
                post_state,
                info,
            );
        }

        let tracked empty_disk_responses =
            DiskRespShard::empty(self.instance_id());
        let tracked new_disk_req_token =
            self.instance.borrow().disk_transitions(
                KVStoreTokenized::Label::DiskOp {
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                empty_disk_responses,
            );
        self.model = Tracked(model);
        let _id = api.send_disk_request(
            disk_req,
            req_id_perm,
            Tracked(new_disk_req_token),
        );

        proof {
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty());
            assert(self.state().outstanding_cache_reqs
                == Map::<ID, Address>::empty());
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
            assert(self.phase_alignment());
            assert(self.common_inv());
            assert(self.inv());
        }
    }

    fn issue_acquired_cache_read_io(
        &mut self,
        addr: IAddress,
        load_handle: MutHandle,
        purpose: CacheReadPurpose,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (started: bool)
        requires
            old(self).instance_id() == old(api).instance_id(),
            old(self).cache_read_io_lag_inv(),
            !(old(self).state().recovery_state is Begin),
            !(old(self).state().recovery_state is AwaitingSuperblock),
            addr@ != spec_superblock_addr(),
            old(self).cache.entry_fetched(&addr),
            old(self).cache.valid_load_handle(&addr, load_handle),
            Cache::State::next(
                old(self).state().cache,
                old(self).cache@,
                cache_load_label(&addr),
            ),
        ensures
            started,
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.sync_phase == old(self).sync_phase,
            self.store_flush_phase == old(self).store_flush_phase,
            self.sync_requests.buffered_reqs@
                == old(self).sync_requests.buffered_reqs@,
            self.sync_requests.journal_cleaning_reqs@
                == old(self).sync_requests.journal_cleaning_reqs@,
            self.sync_requests.superblocking_reqs@
                == old(self).sync_requests.superblocking_reqs@,
            self.sync_requests.sync_target_lsn
                == old(self).sync_requests.sync_target_lsn,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_outstanding = self.outstanding_requests@;
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        let req_id_perm = Tracked(api.send_disk_request_predict_id());
        let disk_req = IDiskRequest::ReadReq { from: addr };
        let ghost req_map = map![req_id_perm@ => disk_req@];
        let ghost updated = map![req_id_perm@ => addr@];
        let ghost disk_request_tuples =
            multiset_map_singleton(req_id_perm@, disk_req@);
        let ghost disk_response_tuples = Multiset::empty();
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                cache: self.cache@,
                outstanding_cache_reqs: pre_state.state
                    .outstanding_cache_reqs
                    .union_prefer_right(updated),
                ..pre_state.state
            },
        };

        proof {
            multiset_map_singleton_ensures(req_id_perm@, disk_req@);
            assert(multiset_to_map(disk_request_tuples) == req_map);
            Self::singleton_updated_addr_map(
                req_id_perm@,
                disk_req@,
                addr@,
            );
            assert(updated.is_injective());
            assert(!updated.contains_value(spec_superblock_addr()));
            singleton_map_values(req_id_perm@, disk_req@);
            assert(Cache::Label::DiskOps {
                requests: req_map.values(),
                responses: Map::empty(),
            } == cache_load_label(&addr));
            assert(UnifiedCacheBetreeSystem::State::cache_io_begin(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                req_map,
                self.cache@,
                disk_request_tuples,
                disk_response_tuples,
            ));
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                UnifiedCacheBetreeSystem::Step::cache_io_begin(
                    req_map,
                    self.cache@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            let info = ProgramDiskInfo {
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheBetreeProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheBetreeSystem::Step::cache_io_begin(
                    req_map,
                    self.cache@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
                info,
            ));
            UnifiedCacheBetreeProgramModel::lift_disk_step(
                pre_state,
                post_state,
                info,
            );
        }

        let tracked empty_disk_responses =
            DiskRespShard::empty(self.instance_id());
        let tracked new_disk_req_token =
            self.instance.borrow().disk_transitions(
                KVStoreTokenized::Label::DiskOp {
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                empty_disk_responses,
            );
        self.model = Tracked(model);
        let id = api.send_disk_request(
            disk_req,
            req_id_perm,
            Tracked(new_disk_req_token),
        );
        self.outstanding_requests.insert(
            id,
            OutstandingReqInfo::CacheRead {
                addr,
                load_handle,
                purpose,
            },
        );

        proof {
            assert(pre_outstanding
                == Map::<ID, OutstandingReqInfo>::empty());
            assert(self.outstanding_requests@.dom() =~= set![id]);
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
            assert(self.state().cache == self.cache@);
            assert(self.phase_alignment());
            assert(self.common_inv());
            assert(self.inv());
        }
        true
    }

    fn issue_acquired_cache_write_io(
        &mut self,
        addr: IAddress,
        write_handle: WritebackHandle,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (started: bool)
        requires
            old(self).instance_id() == old(api).instance_id(),
            old(self).cache_read_io_lag_inv(),
            !(old(self).state().recovery_state is Begin),
            !(old(self).state().recovery_state is AwaitingSuperblock),
            addr@ != spec_superblock_addr(),
            old(self).cache.entry_fetched(&addr),
            old(self).cache.valid_writeback_handle(&addr, write_handle),
            Cache::State::next(
                old(self).state().cache,
                old(self).cache@,
                Cache::Label::DiskOps {
                    requests: set![DiskRequest::WriteReq {
                        to: addr@,
                        data: write_handle.rec@,
                    }],
                    responses: Map::empty(),
                },
            ),
        ensures
            started,
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.sync_phase == old(self).sync_phase,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_outstanding = self.outstanding_requests@;
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        let req_id_perm = Tracked(api.send_disk_request_predict_id());
        let write_data = write_handle.rec.clone();
        let disk_req = IDiskRequest::WriteReq {
            to: addr,
            data: write_data,
        };
        let ghost req_map = map![req_id_perm@ => disk_req@];
        let ghost updated = map![req_id_perm@ => addr@];
        let ghost disk_request_tuples =
            multiset_map_singleton(req_id_perm@, disk_req@);
        let ghost disk_response_tuples = Multiset::empty();
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                cache: self.cache@,
                outstanding_cache_reqs: pre_state.state
                    .outstanding_cache_reqs.union_prefer_right(updated),
                ..pre_state.state
            },
        };

        proof {
            multiset_map_singleton_ensures(req_id_perm@, disk_req@);
            assert(multiset_to_map(disk_request_tuples) == req_map);
            Self::singleton_updated_addr_map(
                req_id_perm@,
                disk_req@,
                addr@,
            );
            assert(updated.is_injective());
            assert(!updated.contains_value(spec_superblock_addr()));
            singleton_map_values(req_id_perm@, disk_req@);
            assert(req_map.values() == set![DiskRequest::WriteReq {
                to: addr@,
                data: write_handle.rec@,
            }]);
            assert(UnifiedCacheBetreeSystem::State::cache_io_begin(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                req_map,
                self.cache@,
                disk_request_tuples,
                disk_response_tuples,
            ));
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                UnifiedCacheBetreeSystem::Step::cache_io_begin(
                    req_map,
                    self.cache@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            let info = ProgramDiskInfo {
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheBetreeProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheBetreeSystem::Step::cache_io_begin(
                    req_map,
                    self.cache@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
                info,
            ));
            UnifiedCacheBetreeProgramModel::lift_disk_step(
                pre_state,
                post_state,
                info,
            );
        }

        let tracked empty_disk_responses =
            DiskRespShard::empty(self.instance_id());
        let tracked new_disk_req_token = self.instance.borrow()
            .disk_transitions(
                KVStoreTokenized::Label::DiskOp {
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                empty_disk_responses,
            );
        self.model = Tracked(model);
        proof {
            FracCacheImpl::valid_writeback_handle_has_inv(
                &self.cache,
                &addr,
                write_handle,
            );
        }
        let id = api.send_disk_request(
            disk_req,
            req_id_perm,
            Tracked(new_disk_req_token),
        );
        self.outstanding_requests.insert(
            id,
            OutstandingReqInfo::CacheWrite { addr, write_handle },
        );

        proof {
            assert(pre_outstanding
                == Map::<ID, OutstandingReqInfo>::empty());
            assert(self.outstanding_requests@.dom() =~= set![id]);
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
            assert(self.state().cache == self.cache@);
            assert(self.phase_alignment());
            assert(self.common_inv());
            assert(self.inv());
        }
        true
    }

    fn complete_store_sync_response(
        &mut self,
        id: ID,
        token: Tracked<DiskRespShard>,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).outstanding_requests@.contains_key(id),
            old(self).outstanding_requests@[id] is SuperblockWrite,
            old(self).sync_phase is SuperblockWriteIssued,
            old(self).sync_phase->req_id == id,
            old(self).branch.control.frozen_metadata is Some,
            token@.instance_id() == old(self).instance_id(),
            token@.multiset()
                == multiset_map_singleton(
                    id,
                    DiskResponse::WriteResp {},
                ),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let ghost response = DiskResponse::WriteResp {};
        proof {
            self.sync_write_response_certificate(id, token);
        }
        let req_info = self.outstanding_requests.remove(&id);
        match req_info {
            Some(OutstandingReqInfo::SuperblockWrite) => {},
            _ => unreached(),
        }
        let mut phase = BetreeSyncPhaseImpl::None;
        core::mem::swap(&mut self.sync_phase, &mut phase);
        let (image, req_id) = match phase {
            BetreeSyncPhaseImpl::SuperblockWriteIssued {
                image,
                req_id,
            } => (image, req_id),
            _ => unreached(),
        };
        let boundary = image.payload.journal.snapshot.boundary_lsn;
        let persistent_seq_end = image.payload.journal.seq_end;
        let ghost abstract_image = image@@;
        let ghost pre_state = self.model@.value();
        let ghost pre_journal = self.journal@;
        let ghost pre_branch = self.branch@;
        let ghost pre_pool = self.au_pool@;
        if self.branch.control.frozen_metadata.is_some() {
            proof {
                self.journal.view_seq_end_ensures();
                assert(pre_journal.seq_end()
                    == self.journal.seq_end());
            }
            let journal_discarded_vec =
                self.journal.discard_for_store_commit(
                    boundary,
                    self.disk_au_count,
                );
            let ghost journal_discarded_aus =
                iau_vec_set(journal_discarded_vec@);
            let ghost discarded_journal = self.journal@;
            proof {
                let kept = crate::allocation_layer::
                    AllocationJournal_v::
                    lsn_au_index_discard_up_to(
                        pre_journal.status.unwrap()
                            .lsn_au_index,
                        boundary as nat,
                    );
                assert(journal_discarded_aus
                    =~= pre_journal.status.unwrap()
                        .lsn_au_index.values() - kept.values());
                assert(CachedJournal::State::next(
                    pre_journal,
                    discarded_journal,
                    CachedJournal::Label::DiscardOld {
                        start_lsn: boundary as nat,
                        require_end: pre_journal.seq_end(),
                        deallocs: journal_discarded_aus,
                    },
                ));
            }
            let branch_reclaimed = match self.branch.commit_complete() {
                BranchBetreeCommitCompleteResult::Applied {
                    reclaimed,
                } => reclaimed,
                BranchBetreeCommitCompleteResult::Noop => {
                    proof { assert(false); }
                    unreached()
                },
            };
            let ghost branch_discarded_aus =
                iau_seq_set(branch_reclaimed@);
            proof {
                assert(iau_vec_set(branch_reclaimed@)
                    =~= branch_discarded_aus) by {
                    assert forall |au: AU|
                        #[trigger] iau_vec_set(
                            branch_reclaimed@,
                        ).contains(au)
                            <==> branch_discarded_aus
                                .contains(au) by {}
                }
                assert(journal_discarded_aus
                    <= pre_journal.status.unwrap()
                        .lsn_au_index.values());
                assert(branch_discarded_aus
                    <= old(self).branch.ownership
                        .persistent_aus());
                assert(pre_pool.disjoint(
                    journal_discarded_aus,
                )) by {
                    assert(pre_state.state.journal.loaded_index_aus()
                        == pre_journal.status.unwrap()
                            .lsn_au_index.values());
                    assert(pre_state.state.journal.loaded_index_aus()
                        <= pre_state.state.journal.owned_aus());
                    assert(pre_pool.disjoint(
                        pre_state.state.journal.owned_aus(),
                    ));
                }
                assert(pre_pool.disjoint(
                    branch_discarded_aus,
                )) by {
                    assert(old(self).branch.control_i()
                        .persistent_aus
                        == old(self).branch.ownership
                            .persistent_aus());
                    assert(pre_pool.disjoint(
                        old(self).branch.control_i()
                            .persistent_aus,
                    ));
                }
                assert(journal_discarded_aus.disjoint(
                    branch_discarded_aus,
                )) by {
                    assert(pre_state.state.journal.loaded_index_aus()
                        == pre_journal.status.unwrap()
                            .lsn_au_index.values());
                    assert(pre_state.state.journal.loaded_index_aus()
                        <= pre_state.state.journal.owned_aus());
                    assert(old(self).branch.control_i()
                        .persistent_aus
                        == old(self).branch.ownership
                            .persistent_aus());
                    assert(pre_state.state.journal.owned_aus()
                        .disjoint(old(self).branch.control_i()
                            .persistent_aus));
                }
                assert forall |i: int|
                    0 <= i < journal_discarded_vec@.len()
                    implies {
                        &&& 0 < #[trigger]
                            (journal_discarded_vec@[i] as nat)
                        &&& (journal_discarded_vec@[i] as nat)
                            < self.disk_au_count as nat
                    } by {
                    let au = journal_discarded_vec@[i] as nat;
                    assert(journal_discarded_aus.contains(au));
                    assert(pre_journal.status.unwrap()
                        .lsn_au_index.values().contains(au));
                    assert(old(self).journal.index_aus_bounded(
                        self.disk_au_count,
                    ));
                    assert(au < self.disk_au_count as nat);
                    assert(pre_state.state.journal.loaded_index_aus()
                        .contains(au));
                    assert(pre_state.state.journal.owned_aus()
                        .contains(au));
                    assert(!pre_state.state.journal.owned_aus()
                        .contains(spec_superblock_addr().au));

                    assert(!pre_state.state.journal.owned_aus()
                        .contains(0));
                    assert(au != 0);
                }
                assert forall |i: int|
                    0 <= i < branch_reclaimed@.len()
                    implies {
                        &&& 0 < #[trigger]
                            (branch_reclaimed@[i] as nat)
                        &&& (branch_reclaimed@[i] as nat)
                            < self.disk_au_count as nat
                    } by {
                    let au = branch_reclaimed@[i] as nat;
                    assert(branch_discarded_aus.contains(au));
                    assert(old(self).branch.ownership
                        .persistent_aus().contains(au));
                    assert((old(self).branch.ownership.betree
                        .all_aus()
                        + old(self).branch.ownership.branches
                            .all_summary_aus()).contains(au));
                    assert(old(self).branch_owned_aus_bounded());
                }
            }
            self.au_pool.free_aus(
                self.disk_au_count,
                &journal_discarded_vec,
            );
            proof {
                assert(self.au_pool@
                    =~= pre_pool + journal_discarded_aus);
                assert(self.au_pool@.disjoint(
                    branch_discarded_aus,
                ));
            }
            self.au_pool.free_aus(
                self.disk_au_count,
                &branch_reclaimed,
            );

            let ghost new_journal = AtomicJournalState::State {
                journal: self.journal@,
                persistent_seq_end: abstract_image.journal_seq_end,
                mini_allocator: self.journal.journal_alloc.i(),
                in_flight: None,
            };
            let ghost post_state = UnifiedCacheBetreeProgramModel {
                state: UnifiedCacheBetreeSystem::State {
                    journal: new_journal,
                    branch: self.branch@,
                    free_aus: self.au_pool@,
                    persistent_image: Some(abstract_image),
                    sync_phase: AtomicBetreeSyncPhase::None,
                    ..pre_state.state
                },
            };
            let ghost disk_request_tuples = Multiset::empty();
            let ghost disk_response_tuples =
                multiset_map_singleton(id, response);
            let tracked mut model =
                KVStoreTokenized::model::arbitrary();
            proof {
                tracked_swap(self.model.borrow_mut(), &mut model);
                assert(req_id == id) by {
                    assert(old(self).outstanding_requests@
                        .contains_key(req_id));
                    assert(old(self).outstanding_requests@
                        .contains_key(id));
                    assert(old(self)
                        .outstanding_requests_single_flight());
                }
                assert(pre_state.state.sync_phase
                    == AtomicBetreeSyncPhase::SuperblockWriteIssued {
                        req_id: id,
                        image: abstract_image,
                    });
                assert(pre_state.state.journal.journal
                    == pre_journal);
                assert(pre_state.state.branch == pre_branch);
                assert(pre_state.state.free_aus =~= pre_pool);
                assert(self.journal@ == discarded_journal);
                assert(boundary as nat
                    == abstract_image.journal_snapshot
                        .boundary_lsn);
                assert(pre_state.state.journal.journal.seq_end()
                    == pre_journal.seq_end());
                assert(CachedJournal::State::next(
                    pre_journal,
                    self.journal@,
                    CachedJournal::Label::DiscardOld {
                        start_lsn: abstract_image
                            .journal_snapshot.boundary_lsn,
                        require_end: pre_state.state.journal
                            .journal.seq_end(),
                        deallocs: journal_discarded_aus,
                    },
                ));
                assert(AtomicJournalState::State::commit_complete(
                    pre_state.state.journal,
                    new_journal,
                    AtomicJournalState::Label::CommitComplete {
                        require_end: pre_state.state.journal
                            .journal.seq_end(),
                        discarded_aus: journal_discarded_aus,
                    },
                    self.journal@,
                )) by {

                }
                assert(AtomicJournalState::State::next(
                    pre_state.state.journal,
                    new_journal,
                    AtomicJournalState::Label::CommitComplete {
                        require_end: pre_state.state.journal
                            .journal.seq_end(),
                        discarded_aus: journal_discarded_aus,
                    },
                )) by {
                    reveal(AtomicJournalState::State::next);
                    assert(AtomicJournalState::State::next_by(
                        pre_state.state.journal,
                        new_journal,
                        AtomicJournalState::Label::CommitComplete {
                            require_end: pre_state.state.journal
                                .journal.seq_end(),
                            discarded_aus: journal_discarded_aus,
                        },
                        AtomicJournalState::Step::commit_complete(
                            self.journal@,
                        ),
                    )) by {
                        reveal(AtomicJournalState::State::next_by);
                    }
                }
                assert(AtomicBranchBetreeState::State::next(
                    pre_state.state.branch,
                    self.branch@,
                    AtomicBranchBetreeState::Label::CommitComplete,
                ));
                assert(branch_discarded_aus
                    == pre_branch.control.persistent_aus
                        - pre_branch.control.frozen.unwrap().aus
                        - pre_branch.betree.owned_aus());
                assert(self.au_pool@
                    =~= pre_pool + journal_discarded_aus
                        + branch_discarded_aus);
                multiset_map_singleton_ensures(id, response);
                assert(response == DiskResponse::WriteResp {});
                assert(disk_response_tuples
                    == Multiset::singleton((
                        id,
                        DiskResponse::WriteResp {},
                    ))) by {
                    assert(disk_response_tuples
                        == Multiset::empty().insert((id, response)));
                }
                assert(UnifiedCacheBetreeSystem::State::
                    execute_store_sync_end(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Disk,
                        journal_discarded_aus,
                        new_journal,
                        disk_request_tuples,
                        disk_response_tuples,
                    ));
                assert(UnifiedCacheBetreeSystem::State::next_by(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Disk,
                    UnifiedCacheBetreeSystem::Step::
                        execute_store_sync_end(
                            journal_discarded_aus,
                            new_journal,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                )) by {
                    reveal(UnifiedCacheBetreeSystem::State::next_by);
                }
                let info = ProgramDiskInfo {
                    reqs: disk_request_tuples,
                    resps: disk_response_tuples,
                };
                assert(UnifiedCacheBetreeProgramModel::
                    disk_step_matches_info(
                        pre_state.state,
                        UnifiedCacheBetreeSystem::Step::
                            execute_store_sync_end(
                                journal_discarded_aus,
                                new_journal,
                                disk_request_tuples,
                                disk_response_tuples,
                            ),
                        info,
                    ));
                UnifiedCacheBetreeProgramModel::lift_disk_step(
                    pre_state,
                    post_state,
                    info,
                );
            }
            let tracked _disk_request_token = self.instance.borrow()
                .disk_transitions(
                    KVStoreTokenized::Label::DiskOp {
                        disk_request_tuples,
                        disk_response_tuples,
                    },
                    post_state,
                    &mut model,
                    token.get(),
                );
            self.model = Tracked(model);
            self.persistent_journal_seq_end = persistent_seq_end;
            self.sync_phase = BetreeSyncPhaseImpl::None;
            proof {
                assert(self.outstanding_requests@
                    == Map::<ID, OutstandingReqInfo>::empty());
                assert(self.state().outstanding_cache_reqs
                    == Map::<ID, Address>::empty());
                assert(self.outstanding_requests_wf());
                assert(self.outstanding_cache_reqs_match_model());
                assert(self.outstanding_requests_single_flight());
                assert(self.state().journal.journal == self.journal@);
                assert(self.state().branch == self.branch@);
                assert(self.state().free_aus =~= self.au_pool@);
                self.journal.view_seq_end_ensures();
                assert(self.journal.seq_end()
                    == pre_journal.seq_end());
                assert(self.branch@.betree == pre_branch.betree);
                assert(pre_state.state.journal.journal.seq_end()
                    == pre_state.state.branch.betree.memtable
                        .seq_end);
                assert(self.state().journal.journal.seq_end()
                    == self.state().branch.betree.memtable.seq_end);
                assert(self.journal.ready_wf(
                    self.disk_au_count,
                ));
                self.journal.wf_implies_basic_wf();
                assert(self.au_pool@.disjoint(
                    self.journal.owned_aus(),
                )) by {
                    assert(self.journal.owned_aus()
                        =~= old(self).journal.owned_aus()
                            - journal_discarded_aus);
                    assert(pre_pool.disjoint(
                        old(self).journal.owned_aus(),
                    ));
                    assert(branch_discarded_aus.disjoint(
                        old(self).journal.owned_aus(),
                    ));
                }
                assert(self.branch_owned_aus_bounded()) by {
                    reveal(Implementation::branch_owned_aus_bounded);
                    assert forall |au: AU| #[trigger]
                        (self.branch.ownership.betree.all_aus()
                            + self.branch.ownership.branches
                                .all_summary_aus()).contains(au)
                        implies 0 < au
                            && au < self.disk_au_count as nat by {
                        assert((old(self).branch.ownership.betree
                            .all_aus()
                            + old(self).branch.ownership.branches
                                .all_summary_aus()).contains(au));
                        assert(old(self).branch_owned_aus_bounded());
                    }
                }
                assert(self.branch.control.metadata.root
                    == image.payload.branch);
                if self.branch.control.metadata.root.is_some() {
                    assert(image@.wf());
                    assert(image@.addresses_bounded());
                    assert(image@.payload.branch is Some);
                    assert(image@.payload.branch.unwrap().au
                        < image@.geometry.formatted_au_count);
                    assert(image@.geometry.formatted_au_count
                        == self.disk_au_count as nat);
                    assert(self.branch.control.metadata.root
                        .unwrap()@.au
                        < self.disk_au_count as nat);
                }
                assert(self.phase_alignment());
                assert(self.sync_wf());
                assert(self.store_flush_wf());
                assert(self.common_inv());
                assert(self.inv());
            }
            api.log("unified-cache Betree store sync complete");
            return;
        }
    }


    fn complete_journal_sync_response(
        &mut self,
        id: ID,
        token: Tracked<DiskRespShard>,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).outstanding_requests@.contains_key(id),
            old(self).outstanding_requests@[id] is SuperblockWrite,
            old(self).sync_phase is SuperblockWriteIssued,
            old(self).sync_phase->req_id == id,
            old(self).branch.control.frozen_metadata is None,
            token@.instance_id() == old(self).instance_id(),
            token@.multiset()
                == multiset_map_singleton(
                    id,
                    DiskResponse::WriteResp {},
                ),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let ghost response = DiskResponse::WriteResp {};
        proof {
            self.sync_write_response_certificate(id, token);
        }
        let req_info = self.outstanding_requests.remove(&id);
        match req_info {
            Some(OutstandingReqInfo::SuperblockWrite) => {},
            _ => unreached(),
        }
        let mut phase = BetreeSyncPhaseImpl::None;
        core::mem::swap(&mut self.sync_phase, &mut phase);
        let (image, req_id) = match phase {
            BetreeSyncPhaseImpl::SuperblockWriteIssued {
                image,
                req_id,
            } => (image, req_id),
            _ => unreached(),
        };
        let boundary = image.payload.journal.snapshot.boundary_lsn;
        let persistent_seq_end = image.payload.journal.seq_end;
        let ghost abstract_image = image@@;
        let ghost pre_state = self.model@.value();
        let ghost pre_journal = self.journal@;
        let ghost pre_branch = self.branch@;
        let ghost pre_pool = self.au_pool@;
        let ghost discarded_aus = Set::<AU>::empty();
        let old_journal_seq_end = self.journal.exec_seq_end();
        proof {
            assert(req_id == id) by {
                assert(old(self).outstanding_requests@
                    .contains_key(req_id));
                assert(old(self).outstanding_requests@
                    .contains_key(id));
                assert(old(self).outstanding_requests_single_flight());
            }
            assert(pre_state.state.sync_phase
                == AtomicBetreeSyncPhase::SuperblockWriteIssued {
                    req_id: id,
                    image: abstract_image,
                });
            assert(boundary as nat == self.journal.seq_start());
            self.journal.view_seq_end_ensures();
            assert(old_journal_seq_end as nat
                == pre_journal.seq_end());
            self.journal.seq_start_le_marshalled_end();
            self.journal.discard_at_seq_start_deallocates_nothing();
        }
        self.journal.discard_old(
            boundary,
            self.disk_au_count,
        );
        let ghost new_journal = AtomicJournalState::State {
            journal: self.journal@,
            persistent_seq_end: abstract_image.journal_seq_end,
            mini_allocator: self.journal.journal_alloc.i(),
            in_flight: None,
        };
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                journal: new_journal,
                free_aus: pre_state.state.free_aus
                    + discarded_aus,
                persistent_image: Some(abstract_image),
                sync_phase: AtomicBetreeSyncPhase::None,
                ..pre_state.state
            },
        };
        let ghost disk_request_tuples = Multiset::empty();
        let ghost disk_response_tuples =
            multiset_map_singleton(id, response);
        let tracked mut model =
            KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
            let old_index = pre_journal.status.unwrap()
                .lsn_au_index;
            let kept = crate::allocation_layer::
                AllocationJournal_v::
                lsn_au_index_discard_up_to(
                    old_index,
                    boundary as nat,
                );
            assert(old_index.values() - kept.values()
                =~= discarded_aus);
            assert(CachedJournal::State::next(
                pre_journal,
                self.journal@,
                CachedJournal::Label::DiscardOld {
                    start_lsn: boundary as nat,
                    require_end: pre_journal.seq_end(),
                    deallocs: discarded_aus,
                },
            ));
            assert(pre_state.state.journal.journal
                == pre_journal);
            assert(self.journal.journal_alloc.i()
                == pre_state.state.journal.mini_allocator);
            assert(pre_state.state.journal.mini_allocator
                .prune(discarded_aus)
                == pre_state.state.journal.mini_allocator) by {
                assert(pre_state.state.journal.mini_allocator.allocs
                    .remove_keys(discarded_aus)
                    == pre_state.state.journal.mini_allocator.allocs) by {
                    assert_maps_equal!(
                        pre_state.state.journal.mini_allocator.allocs
                            .remove_keys(discarded_aus),
                        pre_state.state.journal.mini_allocator.allocs,
                        au => {}
                    );
                }
            }
            assert(AtomicJournalState::State::commit_complete(
                pre_state.state.journal,
                new_journal,
                AtomicJournalState::Label::CommitComplete {
                    require_end: pre_state.state.journal.journal
                        .seq_end(),
                    discarded_aus,
                },
                self.journal@,
            )) by {

            }
            assert(AtomicJournalState::State::next_by(
                pre_state.state.journal,
                new_journal,
                AtomicJournalState::Label::CommitComplete {
                    require_end: pre_state.state.journal.journal
                        .seq_end(),
                    discarded_aus,
                },
                AtomicJournalState::Step::commit_complete(
                    self.journal@,
                ),
            )) by {
                reveal(AtomicJournalState::State::next_by);
            }
            assert(AtomicJournalState::State::next(
                pre_state.state.journal,
                new_journal,
                AtomicJournalState::Label::CommitComplete {
                    require_end: pre_state.state.journal.journal
                        .seq_end(),
                    discarded_aus,
                },
            )) by {
                reveal(AtomicJournalState::State::next);
            }
            multiset_map_singleton_ensures(id, response);
            assert(response == DiskResponse::WriteResp {});
            assert(disk_response_tuples
                == Multiset::singleton((
                    id,
                    DiskResponse::WriteResp {},
                ))) by {
                assert(disk_response_tuples
                    == Multiset::empty().insert((id, response)));
            }
            assert(UnifiedCacheBetreeSystem::State::
                execute_journal_sync_end(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Disk,
                    discarded_aus,
                    new_journal,
                    disk_request_tuples,
                    disk_response_tuples,
                ));
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                UnifiedCacheBetreeSystem::Step::
                    execute_journal_sync_end(
                        discarded_aus,
                        new_journal,
                        disk_request_tuples,
                        disk_response_tuples,
                    ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            let info = ProgramDiskInfo {
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheBetreeProgramModel::
                disk_step_matches_info(
                    pre_state.state,
                    UnifiedCacheBetreeSystem::Step::
                        execute_journal_sync_end(
                            discarded_aus,
                            new_journal,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                    info,
                ));
            UnifiedCacheBetreeProgramModel::lift_disk_step(
                pre_state,
                post_state,
                info,
            );
        }
        let tracked _disk_request_token = self.instance.borrow()
            .disk_transitions(
                KVStoreTokenized::Label::DiskOp {
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                token.get(),
            );
        self.model = Tracked(model);
        self.persistent_journal_seq_end = persistent_seq_end;
        self.sync_phase = BetreeSyncPhaseImpl::None;
        proof {
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty());
            assert(self.state().outstanding_cache_reqs
                == Map::<ID, Address>::empty());
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
            assert(self.state().journal.journal == self.journal@);
            self.journal.view_seq_end_ensures();
            assert(self.journal.seq_end()
                == old_journal_seq_end as nat);
            assert(old_journal_seq_end as nat
                == pre_journal.seq_end());
            assert(pre_state.state.journal.journal.seq_end()
                == pre_state.state.branch.betree.memtable.seq_end);
            assert(self.state().journal.journal.seq_end()
                == self.state().branch.betree.memtable.seq_end);
            self.journal.wf_implies_basic_wf();
            self.journal.view_ensures();
            old(self).journal.view_ensures();
            assert(self.journal.index_ready());
            assert(old(self).journal.index_ready());
            assert(self.journal@.status.unwrap().lsn_au_index
                == old(self).journal@.status.unwrap()
                    .lsn_au_index);
            JournalImpl::allocator_index_alignment_preserved(
                &old(self).journal,
                &self.journal,
            );
            assert(self.sync_wf()) by {
                assert forall |i: int|
                    0 <= i < self.sync_requests
                        .superblocking_reqs@.len()
                    implies #[trigger] self.state().sync_req_map[
                        self.sync_requests.superblocking_reqs@[i]
                    ] <= self.state().journal.persistent_seq_end by {
                    assert(old(self).state().sync_req_map[
                        old(self).sync_requests
                            .superblocking_reqs@[i]
                    ] <= abstract_image.journal_seq_end);
                }
            }
            assert(self.phase_alignment());
            assert(self.compaction_executor_wf()) by {
                reveal(Implementation::compaction_executor_wf);
                assert(old(self).compaction_work is None) by {
                    if old(self).compaction_work is Some {
                        assert(old(self).sync_phase is None);
                        assert(false);
                    }
                }
            }
            assert(Self::same_journal_sync_stable_state(
                old(self), self,
            ));
            Self::common_inv_after_journal_sync(old(self), self);
            assert(self.inv());
        }
        api.log("unified-cache Betree journal sync complete");
    }


    #[verifier::spinoff_prover]
    pub fn handle_disk_response(
        &mut self,
        rec: DiskResponseRecord<UnifiedCacheBetreeProgramModel>,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            rec.token@.instance_id() == old(self).instance_id(),
            rec.token@.multiset()
                == multiset_map_singleton(rec.id, rec.disk_response@),
            rec.disk_response is ReadResp
                ==> rec.disk_response->data.len() == PAGE_SIZE_BYTES,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            old(self).disk_response_inv_facts(old(api));
        }
        let DiskResponseRecord { id, disk_response, token } = rec;
        let ghost response = disk_response@;
        let ghost pre_outstanding = self.outstanding_requests@;
        let req_info = self.outstanding_requests.remove(&id);
        match req_info {
            None => {
                api.log("unified-cache Betree unexpected disk response");
            },
            Some(OutstandingReqInfo::CacheRead {
                addr,
                load_handle,
                purpose,
            }) => match disk_response {
                IDiskResponse::ReadResp { data } => {
                    let mut load_handle = load_handle;
                    load_handle.rec = data;
                    let ghost pre_state = self.model@.value();
                    proof {
                        assert(pre_outstanding.contains_key(id));
                        assert(!(pre_state.state.recovery_state is Begin));
                        assert(!(pre_state.state.recovery_state
                            is AwaitingSuperblock));
                        assert(old(self).cache.entry_fetched(&addr));
                        assert(old(self).cache.valid_load_handle(
                            &addr,
                            load_handle,
                        ));
                    }
                    let ghost pre_cache_reqs =
                        pre_state.state.outstanding_cache_reqs;
                    self.cache.load_release(&addr, load_handle);

                    // A completed load can expose a page that was absent when
                    // the full ghost branch source was selected. Keep the job
                    // queued, then rebuild its proof cursor from the warmed
                    // cache through the ordinary abort path.
                    match self.compaction_work {
                        Some(work) => match work.phase {
                            CompactionWorkPhase::Scanning => {
                                let _ = self.compaction_candidates.push(
                                    work.candidate,
                                );
                                self.compaction_work = Some(
                                    CompactionWorkItem {
                                        phase: CompactionWorkPhase::AbortCompactor,
                                        ..work
                                    },
                                );
                            },
                            _ => {},
                        },
                        None => {},
                    }

                    let ghost resp_map = map![id => response];
                    let ghost disk_request_tuples = Multiset::empty();
                    let ghost disk_response_tuples =
                        multiset_map_singleton(id, response);
                    let ghost post_state = UnifiedCacheBetreeProgramModel {
                        state: UnifiedCacheBetreeSystem::State {
                            cache: self.cache@,
                            outstanding_cache_reqs: pre_state.state
                                .outstanding_cache_reqs
                                .remove_keys(resp_map.dom()),
                            ..pre_state.state
                        },
                    };
                    let tracked mut model =
                        KVStoreTokenized::model::arbitrary();
                    proof {
                        tracked_swap(self.model.borrow_mut(), &mut model);
                    }

                    proof {
                        assert(pre_state.state.outstanding_cache_reqs
                            == map![id => addr@]) by {
                            assert_maps_equal!(
                                pre_state.state.outstanding_cache_reqs,
                                map![id => addr@],
                                other => {
                                    if other != id
                                        && pre_state.state
                                            .outstanding_cache_reqs
                                            .contains_key(other)
                                    {
                                        assert(old(self).outstanding_requests@
                                            .contains_key(other));
                                        assert(old(self).outstanding_requests@
                                            .contains_key(id));
                                        assert(old(self)
                                            .outstanding_requests_single_flight());
                                        assert(other == id);
                                    }
                                }
                            );
                        }
                        multiset_map_singleton_ensures(id, response);
                        assert(multiset_to_map(disk_response_tuples)
                            == resp_map);
                        Self::cache_resps_singleton(
                            pre_cache_reqs,
                            id,
                            addr@,
                            response,
                        );
                        assert(UnifiedCacheBetreeSystem::State::cache_io_end(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Disk,
                            resp_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ));
                        assert(UnifiedCacheBetreeSystem::State::next_by(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Disk,
                            UnifiedCacheBetreeSystem::Step::cache_io_end(
                                resp_map,
                                self.cache@,
                                disk_request_tuples,
                                disk_response_tuples,
                            ),
                        )) by {
                            reveal(UnifiedCacheBetreeSystem::State::next_by);
                        }
                        let info = ProgramDiskInfo {
                            reqs: disk_request_tuples,
                            resps: disk_response_tuples,
                        };
                        assert(UnifiedCacheBetreeProgramModel::
                            disk_step_matches_info(
                                pre_state.state,
                                UnifiedCacheBetreeSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                                info,
                            ));
                        UnifiedCacheBetreeProgramModel::lift_disk_step(
                            pre_state,
                            post_state,
                            info,
                        );
                        assert(post_state.state.outstanding_cache_reqs
                            == Map::<ID, Address>::empty()) by {
                            assert_maps_equal!(
                                post_state.state.outstanding_cache_reqs,
                                Map::<ID, Address>::empty(),
                                other => {
                                    if post_state.state
                                        .outstanding_cache_reqs
                                        .contains_key(other)
                                    {
                                        assert(pre_state.state
                                            .outstanding_cache_reqs
                                            .contains_key(other));
                                        assert(other == id);
                                        assert(resp_map.dom().contains(other));
                                    }
                                }
                            );
                        }
                    }

                    let tracked _disk_req_token =
                        self.instance.borrow().disk_transitions(
                            KVStoreTokenized::Label::DiskOp {
                                disk_request_tuples,
                                disk_response_tuples,
                            },
                            post_state,
                            &mut model,
                            token.get(),
                        );
                    self.model = Tracked(model);
                    proof {
                        assert(self.outstanding_requests@
                            == Map::<ID, OutstandingReqInfo>::empty());
                        assert(self.state().outstanding_cache_reqs
                            == Map::<ID, Address>::empty());
                        assert(self.outstanding_requests_wf());
                        assert(self.outstanding_cache_reqs_match_model());
                        assert(self.outstanding_requests_single_flight());
                        assert(self.state().cache == self.cache@);
                        assert(self.sync_wf());
                        assert(self.store_flush_wf()) by {
                            reveal(Implementation::store_flush_wf);
                            match self.store_flush_phase {
                                StoreFlushPhaseImpl::Building { idx, .. }
                                | StoreFlushPhaseImpl::Sealed { idx, .. } => {
                                    let cache_lbl = Cache::Label::DiskOps {
                                        requests: Set::empty(),
                                        responses: map![addr@ => response],
                                    };
                                    assert(Cache::State::next(
                                        old(self).cache@,
                                        self.cache@,
                                        cache_lbl,
                                    ));
                                    Cache::State::inv_next(
                                        old(self).cache@,
                                        self.cache@,
                                        cache_lbl,
                                    );
                                    self.branch.wip_branches@[idx as int]
                                        .cache_inv_preserved_by_valid_reads(
                                            old(self).cache@,
                                            self.cache@,
                                        );
                                },
                                _ => {},
                            }
                        }
                        match self.compaction_work {
                            Some(work) if work.output_idx == Some(0usize) => {
                                self.branch.wip_branches@[0]
                                    .cache_inv_preserved_by_valid_reads(
                                        old(self).cache@,
                                        self.cache@,
                                    );
                            },
                            _ => {},
                        }
                        assert(self.phase_alignment());
                        match old(self).compaction_work {
                            Some(work) if work.phase is Scanning => {
                                assert(self.compaction_work is Some);
                                assert(self.compaction_work.unwrap().phase
                                    is AbortCompactor);
                                assert(self.compaction_executor_wf()) by {
                                    reveal(Implementation::compaction_executor_wf);
                                }
                            },
                            _ => {
                                assert(self.compaction_work
                                    == old(self).compaction_work);
                                Self::compaction_executor_wf_frame(
                                    old(self), self,
                                );
                            },
                        }
                        assert(self.compaction_candidates.wf());
                        assert(self.compaction_candidates.capacity
                            == COMPACTION_CANDIDATE_CAPACITY);
                        assert forall |i: int|
                            0 <= i < self.compaction_candidates.entries@.len()
                            implies #[trigger]
                                self.compaction_candidates.entries@[i].fuel
                                    == CACHE_SIZE_RECS by {
                            if i < old(self).compaction_candidates.entries@.len() {
                            } else {
                                assert(old(self).compaction_work is Some);
                                assert(old(self).compaction_work.unwrap()
                                    .candidate.fuel == CACHE_SIZE_RECS);
                            }
                        }
                        assert(Self::same_non_cache_io_state(
                            old(self), self,
                        ));
                        Self::common_inv_after_cache_io(old(self), self);
                        assert(self.inv());
                    }
                },
                IDiskResponse::WriteResp {} => {
                    self.outstanding_requests.insert(
                        id,
                        OutstandingReqInfo::CacheRead {
                            addr,
                            load_handle,
                            purpose,
                        },
                    );
                    api.log("unified-cache Betree read got write response");
                },
            },
            Some(OutstandingReqInfo::CacheWrite {
                addr,
                write_handle,
            }) => match disk_response {
                IDiskResponse::WriteResp {} => {
                    let ghost pre_state = self.model@.value();
                    proof {
                        assert(pre_outstanding.contains_key(id));
                        assert(old(self).cache.valid_writeback_handle(
                            &addr,
                            write_handle,
                        ));
                    }
                    let ghost pre_cache_reqs =
                        pre_state.state.outstanding_cache_reqs;
                    self.cache.complete_writeback(&addr, write_handle);

                    let ghost resp_map = map![id => response];
                    let ghost disk_request_tuples = Multiset::empty();
                    let ghost disk_response_tuples =
                        multiset_map_singleton(id, response);
                    let ghost post_state = UnifiedCacheBetreeProgramModel {
                        state: UnifiedCacheBetreeSystem::State {
                            cache: self.cache@,
                            outstanding_cache_reqs: pre_state.state
                                .outstanding_cache_reqs
                                .remove_keys(resp_map.dom()),
                            ..pre_state.state
                        },
                    };
                    let tracked mut model =
                        KVStoreTokenized::model::arbitrary();
                    proof {
                        tracked_swap(self.model.borrow_mut(), &mut model);
                        assert(pre_state.state.outstanding_cache_reqs
                            == map![id => addr@]) by {
                            assert_maps_equal!(
                                pre_state.state.outstanding_cache_reqs,
                                map![id => addr@],
                                other => {
                                    if other != id
                                        && pre_state.state
                                            .outstanding_cache_reqs
                                            .contains_key(other)
                                    {
                                        assert(old(self).outstanding_requests@
                                            .contains_key(other));
                                        assert(old(self).outstanding_requests@
                                            .contains_key(id));
                                        assert(other == id);
                                    }
                                }
                            );
                        }
                        multiset_map_singleton_ensures(id, response);
                        assert(multiset_to_map(disk_response_tuples)
                            == resp_map);
                        Self::cache_resps_singleton(
                            pre_cache_reqs,
                            id,
                            addr@,
                            response,
                        );
                        assert(UnifiedCacheBetreeSystem::State::cache_io_end(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Disk,
                            resp_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ));
                        assert(UnifiedCacheBetreeSystem::State::next_by(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Disk,
                            UnifiedCacheBetreeSystem::Step::cache_io_end(
                                resp_map,
                                self.cache@,
                                disk_request_tuples,
                                disk_response_tuples,
                            ),
                        )) by {
                            reveal(UnifiedCacheBetreeSystem::State::next_by);
                        }
                        let info = ProgramDiskInfo {
                            reqs: disk_request_tuples,
                            resps: disk_response_tuples,
                        };
                        assert(UnifiedCacheBetreeProgramModel::
                            disk_step_matches_info(
                                pre_state.state,
                                UnifiedCacheBetreeSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                                info,
                            ));
                        UnifiedCacheBetreeProgramModel::lift_disk_step(
                            pre_state,
                            post_state,
                            info,
                        );
                    }
                    let tracked _disk_req_token =
                        self.instance.borrow().disk_transitions(
                            KVStoreTokenized::Label::DiskOp {
                                disk_request_tuples,
                                disk_response_tuples,
                            },
                            post_state,
                            &mut model,
                            token.get(),
                        );
                    self.model = Tracked(model);
                    proof {
                        assert(self.outstanding_requests@
                            == Map::<ID, OutstandingReqInfo>::empty());
                        assert(self.state().outstanding_cache_reqs
                            == Map::<ID, Address>::empty());
                        assert(self.outstanding_requests_wf());
                        assert(self.outstanding_cache_reqs_match_model());
                        assert(self.outstanding_requests_single_flight());
                        assert(response is WriteResp);
                        assert forall |read_addr: Address, data: RawPage|
                            old(self).cache@.valid_read(read_addr, data)
                            implies self.cache@.valid_read(
                                read_addr,
                                data,
                            ) by {
                            Cache::State::write_response_preserves_valid_read(
                                old(self).cache@,
                                self.cache@,
                                addr@,
                                read_addr,
                                data,
                            );
                        }
                        assert forall |read_addr: Address, data: RawPage|
                            self.cache@.valid_read(read_addr, data)
                            implies old(self).cache@.valid_read(
                                read_addr,
                                data,
                            ) by {
                            Cache::State::write_response_preserves_valid_read(
                                old(self).cache@,
                                self.cache@,
                                addr@,
                                read_addr,
                                data,
                            );
                        }
                        match self.compaction_work {
                            Some(work) if work.output_idx == Some(0usize) => {
                                self.branch.wip_branches@[0]
                                    .cache_inv_preserved_by_valid_reads(
                                        old(self).cache@,
                                        self.cache@,
                                    );
                            },
                            _ => {},
                        }
                        match self.compaction_work {
                            Some(work) if work.phase is Scanning => {
                                self.branch.compactors@[0].merge->0
                                    .cache_inv_preserved_by_backward_valid_reads(
                                        old(self).cache@,
                                        self.cache@,
                                    );
                            },
                            _ => {},
                        }
                        assert(self.phase_alignment());
                        assert(self.sync_wf());
                        assert(self.store_flush_wf()) by {
                            reveal(Implementation::store_flush_wf);
                            match self.store_flush_phase {
                                StoreFlushPhaseImpl::Building { idx, .. }
                                | StoreFlushPhaseImpl::Sealed { idx, .. } => {
                                    let cache_lbl = Cache::Label::DiskOps {
                                        requests: Set::empty(),
                                        responses: map![addr@ => response],
                                    };
                                    assert(Cache::State::next(
                                        old(self).cache@,
                                        self.cache@,
                                        cache_lbl,
                                    ));
                                    Cache::State::inv_next(
                                        old(self).cache@,
                                        self.cache@,
                                        cache_lbl,
                                    );
                                    self.branch.wip_branches@[idx as int]
                                        .cache_inv_preserved_by_valid_reads(
                                            old(self).cache@,
                                            self.cache@,
                                        );
                                },
                                _ => {},
                            }
                        }
                        Self::compaction_executor_wf_frame(old(self), self);
                        assert(Self::same_non_cache_io_state(
                            old(self), self,
                        ));
                        Self::common_inv_after_cache_io(old(self), self);
                        assert(self.inv());
                    }
                },
                IDiskResponse::ReadResp { .. } => {
                    self.outstanding_requests.insert(
                        id,
                        OutstandingReqInfo::CacheWrite {
                            addr,
                            write_handle,
                        },
                    );
                    api.log("unified-cache Betree write got read response");
                },
            },
            Some(OutstandingReqInfo::SuperblockWrite) => match disk_response {
                IDiskResponse::ReadResp { .. } => {
                    self.outstanding_requests.insert(
                        id,
                        OutstandingReqInfo::SuperblockWrite,
                    );
                    api.log("unified-cache Betree superblock write got read response");
                },
                IDiskResponse::WriteResp {} => {
                    if self.branch.control.frozen_metadata.is_some() {
                        self.outstanding_requests.insert(
                            id,
                            OutstandingReqInfo::SuperblockWrite,
                        );
                        self.complete_store_sync_response(id, token, api);
                        return;
                    }
                    self.outstanding_requests.insert(
                        id,
                        OutstandingReqInfo::SuperblockWrite,
                    );
                    self.complete_journal_sync_response(id, token, api);
                    return;
                },
            },
        }
    }

    fn recover_superblock_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is FetchingSuperblock,
            old(self).state().recovery_state is AwaitingSuperblock,
        ensures
            self.inv_api(api),
            self.recovery_phase is LoadingJournal,
            progress,
    {
        api.log("await unified-cache Betree superblock response");
        let ghost pre_state = self.model@.value();
        let DiskResponseRecord {
            id: disk_req_id,
            disk_response: i_disk_response,
            token: disk_response_token,
        } = api.blocking_receive_disk_response();
        proof {
            self.recovery_superblock_response_certificate(
                disk_req_id,
                i_disk_response@,
                disk_response_token,
            );
        }
        let ghost recovered_raw = i_disk_response@->data;

        let raw_page = match i_disk_response {
            IDiskResponse::ReadResp { data } => data,
            IDiskResponse::WriteResp {} => unreached(),
        };
        proof {
            assert(raw_page@ == recovered_raw);
            assert(abstract_superblock_raw_wf(raw_page@));
        }

        let layout = DiskLayout::new();
        let superblock = layout.parse(&raw_page);
        if superblock.geometry.pages_per_au != self.disk_page_count
            || superblock.geometry.formatted_au_count > self.disk_au_count
        {
            api.fatal_geometry_mismatch(
                superblock.geometry.formatted_au_count as u64,
                self.disk_au_count as u64,
                superblock.geometry.pages_per_au as u64,
                self.disk_page_count as u64,
            );
        }

        self.persistent_journal_seq_end =
            superblock.payload.journal.seq_end;
        self.journal = JournalImpl::new(
            superblock.payload.journal.snapshot,
            0,
        );
        let metadata = BetreeMetadataImpl {
            root: superblock.payload.branch,
            seq_end: superblock.payload.journal.snapshot.boundary_lsn,
        };
        proof {
            let image = layout.spec_parse(raw_page@);
            assert(superblock@ == layout.spec_parse_inner(raw_page@));
            assert(superblock@@ == image);
            assert(superblock@.wf());
            assert(image.wf());
            assert(superblock@.geometry.formatted_au_count
                <= self.disk_au_count as nat);
            assert(metadata@ ==
                crate::implementation::UnifiedCacheBetreeSystem_v::
                    betree_metadata_from_superblock(image));
            assert(metadata.wf());
            assert(self.journal.snapshot_geometry_bounded(
                self.disk_au_count,
            ));
        }
        self.branch.initialize_from_metadata(metadata);

        let ghost image = layout.spec_parse(raw_page@);
        let ghost new_journal = AtomicJournalState::State {
            journal: self.journal@,
            mini_allocator: self.journal.journal_alloc.i(),
            persistent_seq_end: image.journal_seq_end,
            in_flight: None,
        };
        let ghost new_branch = self.branch@;
        let ghost disk_request_tuples = Multiset::empty();
        let ghost disk_response_tuples =
            multiset_map_singleton(disk_req_id, i_disk_response@);
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                recovery_state: RecoveryState::SuperblockAvailable,
                journal: new_journal,
                branch: new_branch,
                persistent_image: Some(image),
                sync_phase: AtomicBetreeSyncPhase::None,
                sync_req_map: Map::<SyncReqId, nat>::empty(),
                ..pre_state.state
            },
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof { tracked_swap(self.model.borrow_mut(), &mut model); }

        proof {
            self.journal.view_ensures();
            assert(!self.journal.index_ready());
            assert(image.wf());
            assert(superblock_matches(raw_page@, image));
            assert(AtomicJournalState::State::initialize(
                new_journal,
                image.journal_snapshot,
                image.journal_seq_end,
            )) by {

            }
            assert(AtomicJournalState::State::init_by(
                new_journal,
                AtomicJournalState::Config::initialize(
                    image.journal_snapshot,
                    image.journal_seq_end,
                ),
            )) by {
                reveal(AtomicJournalState::State::init_by);
            }
            assert(AtomicBranchBetreeState::State::init_by(
                new_branch,
                AtomicBranchBetreeState::Config::initialize(
                    crate::implementation::UnifiedCacheBetreeSystem_v::
                        betree_metadata_from_superblock(image),
                ),
            ));
            multiset_map_singleton_ensures(
                disk_req_id,
                i_disk_response@,
            );
            assert(disk_response_tuples == Multiset::singleton((
                disk_req_id,
                DiskResponse::ReadResp { data: raw_page@ },
            )));
            assert(UnifiedCacheBetreeSystem::State::superblock_recovery(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                disk_req_id,
                raw_page@,
                image,
                new_journal,
                new_branch,
                disk_request_tuples,
                disk_response_tuples,
            ));
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                UnifiedCacheBetreeSystem::Step::superblock_recovery(
                    disk_req_id,
                    raw_page@,
                    image,
                    new_journal,
                    new_branch,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            let info = ProgramDiskInfo {
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheBetreeProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheBetreeSystem::Step::superblock_recovery(
                    disk_req_id,
                    raw_page@,
                    image,
                    new_journal,
                    new_branch,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
                info,
            ));
            UnifiedCacheBetreeProgramModel::lift_disk_step(
                pre_state,
                post_state,
                info,
            );
        }

        let tracked _disk_req_token =
            self.instance.borrow().disk_transitions(
                KVStoreTokenized::Label::DiskOp {
                    disk_request_tuples,
                    disk_response_tuples,
                },
                post_state,
                &mut model,
                disk_response_token.get(),
            );
        self.model = Tracked(model);
        self.recovery_phase = RecoveryPhase::LoadingJournal;

        proof {
            assert(self.state().journal.journal == self.journal@);
            assert(self.state().journal.mini_allocator
                == self.journal.journal_alloc.i());
            assert(self.state().journal.persistent_seq_end
                == self.persistent_journal_seq_end as nat);
            assert(self.state().branch == self.branch@);
            assert(self.journal.snapshot_geometry_bounded(
                self.disk_au_count,
            ));
            assert(self.phase_alignment());
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty());
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
            assert(self.common_inv());
            assert(self.inv());
        }
        true
    }

    fn recover_journal_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is LoadingJournal,
        ensures
            self.inv_api(api),
            self.recovery_phase is LoadingJournal
                || self.recovery_phase is LoadingBranch,
    {
        if !self.outstanding_requests.is_empty() {
            return false;
        }
        proof {
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty()) by {
                assert_maps_equal!(
                    self.outstanding_requests@,
                    Map::<ID, OutstandingReqInfo>::empty(),
                    id => {
                        if self.outstanding_requests@
                            .contains_key(id)
                        {
                            assert(!self.outstanding_requests@.is_empty());
                        }
                    }
                );
            }
            assert(self.state().outstanding_cache_reqs
                == Map::<ID, Address>::empty()) by {
                assert_maps_equal!(
                    self.state().outstanding_cache_reqs,
                    Map::<ID, Address>::empty(),
                    id => {
                        if self.state().outstanding_cache_reqs
                            .contains_key(id)
                        {
                            assert(self.outstanding_requests@
                                .contains_key(id));
                        }
                    }
                );
            }
        }

        let ghost journal_raw_disk = self.journal_recovery_raw_disk();
        let ghost pre_state = self.model@.value();
        let ghost pre_cache = self.cache@;
        let ghost pre_journal = self.journal@;
        let ghost pre_pool = self.au_pool@;
        proof {
            self.journal.view_ensures();
            assert(!self.journal.index_ready());
            assert(self.journal@.status is None);
        }
        let step = self.journal.recover_index_step_for_unified(
            &mut self.cache,
            Ghost(journal_raw_disk),
            Ghost(pre_state.state.journal),
            self.disk_au_count,
        );
        match step {
            UnifiedRecoverIndexResult::CacheLoad {
                slot_handle,
                addr,
            } => {
                proof {
                    self.journal.view_ensures();
                    assert(!self.journal.index_ready());
                    assert(self.journal@ == pre_journal);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_read_io(
                    addr,
                    slot_handle,
                    CacheReadPurpose::JournalIndex,
                    api,
                )
            },
            UnifiedRecoverIndexResult::IndexProgress {} => {
                proof {
                    self.journal.view_ensures();
                    assert(!self.journal.index_ready());
                    assert(self.cache@ == pre_cache);
                    assert(self.journal@ == pre_journal);
                    assert(self.inv_api(api));
                }
                true
            },
            UnifiedRecoverIndexResult::IndexComplete {
                reads,
                discovered_aus,
            } => {
                let ghost discovered = iau_vec_set(discovered_aus@);
                self.au_pool.remove_aus(
                    self.disk_au_count,
                    discovered_aus,
                );
                let ghost new_atomic_journal = AtomicJournalState::State {
                    journal: self.journal@,
                    ..pre_state.state.journal
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        journal: new_atomic_journal,
                        free_aus: pre_state.state.free_aus - discovered,
                        ..pre_state.state
                    },
                };
                let tracked mut model =
                    KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }

                proof {
                    let (cache_lbl, journal_lbl) =
                        crate::implementation::JournalImpl_v::
                            load_index_labels(reads@);
                    assert(pre_state.state.cache == pre_cache);
                    assert(pre_state.state.journal.journal == pre_journal);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        self.cache@,
                        cache_lbl,
                    ));
                    assert(AtomicJournalState::State::next(
                        pre_state.state.journal,
                        new_atomic_journal,
                        AtomicJournalState::Label::LoadIndex {
                            reads: to_journal_records(reads@),
                            discovered_aus: discovered,
                        },
                    ));
                    assert(UnifiedCacheBetreeSystem::State::
                        journal_load_index(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            reads@,
                            reads@,
                            discovered,
                            self.cache@,
                            new_atomic_journal,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::journal_load_index(
                            reads@,
                            reads@,
                            discovered,
                            self.cache@,
                            new_atomic_journal,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }

                let tracked _internal_token =
                    self.instance.borrow().internal(
                        KVStoreTokenized::Label::InternalOp {},
                        post_state,
                        &mut model,
                    );
                self.model = Tracked(model);
                self.recovery_phase = RecoveryPhase::LoadingBranch;
                proof {
                    assert(self.au_pool@ =~= pre_pool - discovered);
                    assert(self.state().free_aus =~= self.au_pool@);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i());
                    assert(self.journal.wf());
                    assert(self.journal.index_ready());
                    assert(self.journal.index_aus_bounded(
                        self.disk_au_count,
                    ));
                    assert(self.phase_alignment());
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                    assert(self.common_inv());
                    assert(self.inv());
                }
                api.log("unified-cache Betree journal index recovered");
                true
            },
        }
    }

    fn recover_branch_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is LoadingBranch,
        ensures
            self.inv_api(api),
            self.recovery_phase is LoadingBranch
                || self.recovery_phase is ReplayingJournal,
    {
        if !self.outstanding_requests.is_empty() {
            return false;
        }
        proof {
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty()) by {
                assert_maps_equal!(
                    self.outstanding_requests@,
                    Map::<ID, OutstandingReqInfo>::empty(),
                    id => {
                        if self.outstanding_requests@.contains_key(id) {
                            assert(!self.outstanding_requests@.is_empty());
                        }
                    }
                );
            }
            assert(self.state().outstanding_cache_reqs
                == Map::<ID, Address>::empty()) by {
                assert_maps_equal!(
                    self.state().outstanding_cache_reqs,
                    Map::<ID, Address>::empty(),
                    id => {
                        if self.state().outstanding_cache_reqs
                            .contains_key(id)
                        {
                            assert(self.outstanding_requests@
                                .contains_key(id));
                        }
                    }
                );
            }
        }

        if self.branch.control.metadata_loaded {
            let ghost pre_state = self.model@.value();
            let ghost post_state = UnifiedCacheBetreeProgramModel {
                state: UnifiedCacheBetreeSystem::State {
                    recovery_state: RecoveryState::MetadataLoadComplete,
                    ..pre_state.state
                },
            };
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }
            proof {
                self.journal.view_ensures();
                assert(pre_state.state.journal.ready());
                assert(UnifiedCacheBetreeSystem::State::
                    metadata_load_complete(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                    ));
                assert(UnifiedCacheBetreeSystem::State::next_by(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Internal,
                    UnifiedCacheBetreeSystem::Step::
                        metadata_load_complete(),
                )) by {
                    reveal(UnifiedCacheBetreeSystem::State::next_by);
                }
                UnifiedCacheBetreeProgramModel::lift_internal_step(
                    pre_state,
                    post_state,
                );
            }
            let tracked _internal_token = self.instance.borrow().internal(
                KVStoreTokenized::Label::InternalOp {},
                post_state,
                &mut model,
            );
            self.model = Tracked(model);
            self.recovery_phase = RecoveryPhase::ReplayingJournal;
            proof {
                assert(self.phase_alignment());
                assert(self.outstanding_requests_wf());
                assert(self.outstanding_cache_reqs_match_model());
                assert(self.outstanding_requests_single_flight());
                assert(self.common_inv());
                assert(self.inv());
            }
            api.log("unified-cache Betree metadata recovered");
            return true;
        }

        if !self.branch.control.loading {
            let ghost pre_state = self.model@.value();
            let result = self.branch.recovery_begin();
            match result {
                BranchBetreeControlResult::Noop => {
                    proof { assert(false); }
                    return false;
                },
                BranchBetreeControlResult::Applied => { },
            }
            let ghost new_branch = self.branch@;
            let ghost post_state = UnifiedCacheBetreeProgramModel {
                state: UnifiedCacheBetreeSystem::State {
                    branch: new_branch,
                    ..pre_state.state
                },
            };
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }
            proof {
                assert(AtomicBranchBetreeState::State::next(
                    pre_state.state.branch,
                    new_branch,
                    AtomicBranchBetreeState::Label::Internal,
                ));
                assert(UnifiedCacheBetreeSystem::State::branch_internal(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Internal,
                    new_branch,
                ));
                assert(UnifiedCacheBetreeSystem::State::next_by(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Internal,
                    UnifiedCacheBetreeSystem::Step::branch_internal(
                        new_branch,
                    ),
                )) by {
                    reveal(UnifiedCacheBetreeSystem::State::next_by);
                }
                UnifiedCacheBetreeProgramModel::lift_internal_step(
                    pre_state,
                    post_state,
                );
            }
            let tracked _internal_token = self.instance.borrow().internal(
                KVStoreTokenized::Label::InternalOp {},
                post_state,
                &mut model,
            );
            self.model = Tracked(model);
            proof {
                assert(self.phase_alignment());
                assert(self.outstanding_requests_wf());
                assert(self.outstanding_cache_reqs_match_model());
                assert(self.outstanding_requests_single_flight());
                assert(self.common_inv());
                assert(self.inv());
            }
            return true;
        }

        let ghost pre_state = self.model@.value();
        let ghost pre_cache = self.cache@;
        let step = self.branch.recover_metadata_step(&mut self.cache);
        match step {
            BranchBetreeRecoveryStepResult::NeedCacheLoad {
                addr,
                handle,
            } => {
                proof {
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_read_io(
                    addr,
                    handle,
                    CacheReadPurpose::BranchMetadata,
                    api,
                )
            },
            BranchBetreeRecoveryStepResult::Advanced {
                label,
                reads,
            } => {
                let ghost access = recovery_page_access(label@);
                let ghost branch_lbl =
                    AtomicBranchBetreeState::Label::RecoveryAccess{access};
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }
                proof {
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_access(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            branch_lbl,
                            access,
                            self.cache@,
                            self.branch@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_access(
                                branch_lbl,
                                access,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _internal_token =
                    self.instance.borrow().internal(
                        KVStoreTokenized::Label::InternalOp {},
                        post_state,
                        &mut model,
                    );
                self.model = Tracked(model);
                proof {
                    assert(self.phase_alignment());
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                    assert(self.common_inv());
                    assert(self.inv());
                }
                true
            },
            BranchBetreeRecoveryStepResult::Complete => {
                if !self.branch.recovery.ownership.all_owned_aus_bounded(
                    self.disk_au_count,
                ) {
                    proof { assert(self.inv_api(api)); }
                    api.log("unified-cache Betree recovered AU is out of range");
                    return false;
                }
                let ghost (semantic_recovery, persistent_image) =
                    self.branch_recovery_semantic_certificate();
                proof {
                    self.branch.recovery.
                        completion_matches_from_semantic_recovery(
                            self.branch.control.metadata@,
                            semantic_recovery,
                            persistent_image,
                        );
                }
                let discovered_aus = self.branch.recovered_durable_aus();
                let ghost discovered = iau_seq_set(discovered_aus@);
                self.branch.recovery_complete();
                self.au_pool.remove_aus(
                    self.disk_au_count,
                    discovered_aus,
                );
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        branch: self.branch@,
                        free_aus: pre_state.state.free_aus - discovered,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof { tracked_swap(self.model.borrow_mut(), &mut model); }
                proof {
                    assert(discovered
                        == pre_state.state.branch.control.recovery
                            .loaded_betree(
                                pre_state.state.branch.control.metadata,
                            ).durable_aus());
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_recovery_complete(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            discovered,
                            self.branch@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_recovery_complete(
                                discovered,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _internal_token =
                    self.instance.borrow().internal(
                        KVStoreTokenized::Label::InternalOp {},
                        post_state,
                        &mut model,
                    );
                self.model = Tracked(model);
                proof {
                    assert(self.state().free_aus =~= self.au_pool@);
                    assert(self.phase_alignment());
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                    assert(self.common_inv());
                    assert(self.inv());
                }
                true
            },
            BranchBetreeRecoveryStepResult::CacheFull
            | BranchBetreeRecoveryStepResult::Blocked
            | BranchBetreeRecoveryStepResult::InvalidPage => {
                proof {
                    assert(self.inv_api(api));
                }
                false
            },
        }
    }

    fn recover_replay_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReplayingJournal,
        ensures
            self.inv_api(api),
            self.recovery_phase is ReplayingJournal
                || self.recovery_phase is ReadyForUserOperation,
    {
        if !self.outstanding_requests.is_empty() {
            return false;
        }
        proof {
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty()) by {
                assert_maps_equal!(
                    self.outstanding_requests@,
                    Map::<ID, OutstandingReqInfo>::empty(),
                    id => {
                        if self.outstanding_requests@.contains_key(id) {
                            assert(!self.outstanding_requests@.is_empty());
                        }
                    }
                );
            }
            assert(self.state().outstanding_cache_reqs
                == Map::<ID, Address>::empty()) by {
                assert_maps_equal!(
                    self.state().outstanding_cache_reqs,
                    Map::<ID, Address>::empty(),
                    id => {
                        if self.state().outstanding_cache_reqs
                            .contains_key(id)
                        {
                            assert(self.outstanding_requests@
                                .contains_key(id));
                        }
                    }
                );
            }
        }

        let start_lsn = self.branch.exec_seq_end();
        let journal_start_lsn = self.journal.exec_seq_start();
        let journal_end_lsn = self.journal.exec_seq_end();
        if start_lsn < journal_start_lsn
            || start_lsn > journal_end_lsn
        {
            api.log("unified-cache Betree invalid replay range");
            return false;
        }

        if start_lsn == journal_end_lsn {
            let ghost pre_state = self.model@.value();
            let ghost end_lsn = pre_state.state.branch.betree.memtable.seq_end;
            let ghost post_state = UnifiedCacheBetreeProgramModel {
                state: UnifiedCacheBetreeSystem::State {
                    recovery_state: RecoveryState::RecoveryComplete,
                    ..pre_state.state
                },
            };
            let tracked mut model = KVStoreTokenized::model::arbitrary();
            proof { tracked_swap(self.model.borrow_mut(), &mut model); }
            proof {
                self.journal.view_ensures();
                self.journal.view_seq_end_ensures();
                assert(pre_state.state.journal.journal == self.journal@);
                assert(pre_state.state.journal.journal.status is Some);
                assert(end_lsn == start_lsn as nat);
                assert(pre_state.state.journal.journal.seq_end()
                    == journal_end_lsn as nat);
                let journal_lbl = AtomicJournalState::Label::QueryEndLsn {
                    end_lsn,
                };
                assert(CachedJournal::State::query_end_lsn(
                    pre_state.state.journal.journal,
                    pre_state.state.journal.journal,
                    CachedJournal::Label::QueryEndLsn { end_lsn },
                )) by {

                }
                assert(CachedJournal::State::next_by(
                    pre_state.state.journal.journal,
                    pre_state.state.journal.journal,
                    CachedJournal::Label::QueryEndLsn { end_lsn },
                    CachedJournal::Step::query_end_lsn(),
                )) by {
                    reveal(CachedJournal::State::next_by);
                }
                assert(CachedJournal::State::next(
                    pre_state.state.journal.journal,
                    pre_state.state.journal.journal,
                    CachedJournal::Label::QueryEndLsn { end_lsn },
                )) by {
                    reveal(CachedJournal::State::next);
                }
                assert(AtomicJournalState::State::query_end_lsn(
                    pre_state.state.journal,
                    pre_state.state.journal,
                    journal_lbl,
                )) by {

                }
                assert(AtomicJournalState::State::next_by(
                    pre_state.state.journal,
                    pre_state.state.journal,
                    journal_lbl,
                    AtomicJournalState::Step::query_end_lsn(),
                )) by {
                    reveal(AtomicJournalState::State::next_by);
                }
                assert(AtomicJournalState::State::next(
                    pre_state.state.journal,
                    pre_state.state.journal,
                    journal_lbl,
                )) by {
                    reveal(AtomicJournalState::State::next);
                }
                assert(UnifiedCacheBetreeSystem::State::recovery_complete(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Internal,
                ));
                assert(UnifiedCacheBetreeSystem::State::next_by(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Internal,
                    UnifiedCacheBetreeSystem::Step::recovery_complete(),
                )) by {
                    reveal(UnifiedCacheBetreeSystem::State::next_by);
                }
                UnifiedCacheBetreeProgramModel::lift_internal_step(
                    pre_state,
                    post_state,
                );
            }
            let tracked _internal_token = self.instance.borrow().internal(
                KVStoreTokenized::Label::InternalOp {},
                post_state,
                &mut model,
            );
            self.model = Tracked(model);
            proof {
                assert(self.branch.wip_branches@.len() == 0) by {
                    assert(old(self).branch.wip_branches@.len() == 0) by {
                        reveal(Implementation::phase_alignment);
                    }
                }
            }
            self.recovery_phase = RecoveryPhase::ReadyForUserOperation;
            proof {
                assert(self.phase_alignment());
                assert(self.outstanding_requests_wf());
                assert(self.outstanding_cache_reqs_match_model());
                assert(self.outstanding_requests_single_flight());
                assert(self.common_inv());
                assert(self.inv());
            }
            api.log("unified-cache Betree recovery complete");
            return true;
        }

        let ghost journal_raw_disk = self.journal_recovery_raw_disk();
        let ghost pre_state = self.model@.value();
        let ghost pre_cache = self.cache@;
        let ghost pre_branch = self.branch@;
        proof {
            self.journal.view_seq_start_ensures();
            self.journal.view_seq_end_ensures();
            assert(self.journal.seq_start() <= start_lsn as nat);
            assert((start_lsn as nat) < self.journal.seq_end());
        }
        let replay = self.journal.recover_map_step_for_unified(
            &mut self.cache,
            start_lsn,
            Ghost(journal_raw_disk),
        );
        match replay {
            UnifiedRecoverMapResult::NotInCache {} => {
                api.log("unified-cache Betree replay page not in cache");
                false
            },
            UnifiedRecoverMapResult::InvalidRecord {} => {
                api.log("unified-cache Betree replay invalid record");
                false
            },
            UnifiedRecoverMapResult::FetchSuccess {
                reads,
                addr,
                record: _,
                keys,
                msgs,
            } => {
                let puts = Self::zip_keyed_messages(
                    &keys,
                    &msgs,
                    start_lsn,
                );
                let put_result = self.branch.put_batch(&puts);
                match put_result {
                    BranchBetreePutResult::Noop => {
                        proof {
                            let lbls = crate::implementation::JournalImpl_v::
                                map_recovery_labels(
                                    self.journal.seq_start(),
                                    reads@,
                                    addr@,
                                );
                            assert(lbls.0 == Cache::Label::Access {
                                reads: reads@,
                                writes: Map::empty(),
                            });
                            Cache::State::access_read_only_is_noop(
                                pre_cache,
                                self.cache@,
                                reads@,
                            );
                            assert(self.cache@ == pre_cache);
                            assert(self.inv_api(api));
                        }
                        false
                    },
                    BranchBetreePutResult::Applied => {
                        let ghost post_state = UnifiedCacheBetreeProgramModel {
                            state: UnifiedCacheBetreeSystem::State {
                                cache: self.cache@,
                                branch: self.branch@,
                                ..pre_state.state
                            },
                        };
                        let tracked mut model =
                            KVStoreTokenized::model::arbitrary();
                        proof {
                            tracked_swap(
                                self.model.borrow_mut(),
                                &mut model,
                            );
                        }
                        proof {
                            let full_msgs = to_journal_records(reads@)[addr@]
                                .message_seq;
                            let journal_records = full_msgs.maybe_discard_old(
                                pre_state.state.journal.journal.snapshot
                                    .boundary_lsn,
                            );
                            let branch_records = full_msgs.maybe_discard_old(
                                pre_state.state.branch.betree.memtable.seq_end,
                            );
                            let journal_lbls = crate::implementation::
                                JournalImpl_v::map_recovery_labels(
                                    self.journal.seq_start(),
                                    reads@,
                                    addr@,
                                );
                            self.journal.view_seq_start_ensures();
                            assert(journal_lbls.0 == Cache::Label::Access {
                                reads: reads@,
                                writes: Map::empty(),
                            });
                            assert(journal_lbls.1
                                == CachedJournal::Label::ReadForRecovery {
                                    messages: journal_records,
                                    reads: to_journal_records(reads@),
                                });
                            let atomic_journal_lbl =
                                AtomicJournalState::Label::ReadForRecovery {
                                    messages: journal_records,
                                    reads: to_journal_records(reads@),
                                };
                            assert(pre_state.state.journal.journal
                                == self.journal@);
                            assert(CachedJournal::State::next(
                                self.journal@,
                                self.journal@,
                                journal_lbls.1,
                            ));
                            assert(AtomicJournalState::State::
                                read_for_recovery(
                                    pre_state.state.journal,
                                    pre_state.state.journal,
                                    atomic_journal_lbl,
                                    self.journal@,
                                ));
                            assert(AtomicJournalState::State::next_by(
                                pre_state.state.journal,
                                pre_state.state.journal,
                                atomic_journal_lbl,
                                AtomicJournalState::Step::
                                    read_for_recovery(self.journal@),
                            )) by {
                                reveal(AtomicJournalState::State::next_by);
                            }
                            assert(AtomicJournalState::State::next(
                                pre_state.state.journal,
                                pre_state.state.journal,
                                atomic_journal_lbl,
                            )) by {
                                reveal(AtomicJournalState::State::next);
                            }
                            assert(branch_records
                                == MemtableImpl::history_from_seq(
                                    start_lsn as nat,
                                    puts@,
                                ));
                            assert(UnifiedCacheBetreeSystem::State::
                                read_for_recovery(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheBetreeSystem::Label::Internal,
                                    addr@,
                                    reads@,
                                    self.cache@,
                                    pre_state.state.journal,
                                    self.branch@,
                                ));
                            assert(UnifiedCacheBetreeSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheBetreeSystem::Label::Internal,
                                UnifiedCacheBetreeSystem::Step::
                                    read_for_recovery(
                                        addr@,
                                        reads@,
                                        self.cache@,
                                        pre_state.state.journal,
                                        self.branch@,
                                    ),
                            )) by {
                                reveal(UnifiedCacheBetreeSystem::State::next_by);
                            }
                            UnifiedCacheBetreeProgramModel::
                                lift_internal_step(pre_state, post_state);
                        }
                        let tracked _internal_token =
                            self.instance.borrow().internal(
                                KVStoreTokenized::Label::InternalOp {},
                                post_state,
                                &mut model,
                            );
                        self.model = Tracked(model);
                        proof {
                            assert(self.phase_alignment());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                            assert(self.common_inv());
                            assert(self.inv());
                        }
                        true
                    },
                }
            },
        }
    }

    fn record_execute_noop(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            req.input is NoopInput,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let reply = Reply { output: Output::NoopOutput, id: req.id };
        let ghost post_state = self.model@.value();
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
            let map_req = req.mapspec_req();
            let map_reply = reply.mapspec_reply();
            assert(UnifiedCacheBetreeSystem::State::valid_request_reply_pair(
                map_req,
                map_reply,
            ));
            assert(UnifiedCacheBetreeSystem::State::execute_noop(
                post_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Execute {
                    req: map_req,
                    reply: map_reply,
                },
            )) by {

            }
            assert(UnifiedCacheBetreeSystem::State::next_by(
                post_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Execute {
                    req: map_req,
                    reply: map_reply,
                },
                UnifiedCacheBetreeSystem::Step::execute_noop(),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            assert(UnifiedCacheBetreeSystem::State::next(
                post_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Execute {
                    req: map_req,
                    reply: map_reply,
                },
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next);
            }
            UnifiedCacheBetreeProgramModel::lift_execute_step(
                post_state,
                post_state,
                map_req,
                map_reply,
            );
        }
        let tracked new_reply_token =
            self.instance.borrow().execute_transition(
                KVStoreTokenized::Label::ExecuteOp { req, reply },
                post_state,
                &mut model,
                req_shard.get(),
            );
        self.model = Tracked(model);
        api.send_reply(reply, Tracked(new_reply_token), true);
        proof {
            assert(self.pending_client_op_wf());
            assert(self.common_inv());
            assert(self.inv());
            assert(self.inv_api(api));
        }
    }

    fn continue_pending_client_op(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        if !self.outstanding_requests.is_empty() {
            return false;
        }
        proof {
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty()) by {
                assert_maps_equal!(
                    self.outstanding_requests@,
                    Map::<ID, OutstandingReqInfo>::empty(),
                    id => {
                        if self.outstanding_requests@.contains_key(id) {
                            assert(!self.outstanding_requests@.is_empty());
                        }
                    }
                );
            }
            assert(self.state().outstanding_cache_reqs
                == Map::<ID, Address>::empty()) by {
                assert_maps_equal!(
                    self.state().outstanding_cache_reqs,
                    Map::<ID, Address>::empty(),
                    id => {
                        if self.state().outstanding_cache_reqs
                            .contains_key(id)
                        {
                            assert(self.outstanding_requests@
                                .contains_key(id));
                        }
                    }
                );
            }
        }

        let mut pending = None;
        core::mem::swap(&mut self.pending_client_op, &mut pending);
        match pending {
            None => false,
            Some(PendingClientOp::Put {
                req,
                req_shard,
                key,
                value,
            }) => {
                let puts_blocked = match self.store_flush_phase {
                    StoreFlushPhaseImpl::Building { .. }
                    | StoreFlushPhaseImpl::Sealed { .. }
                    | StoreFlushPhaseImpl::Ready { .. } => true,
                    StoreFlushPhaseImpl::None
                    | StoreFlushPhaseImpl::Pending => false,
                };
                if puts_blocked {
                    self.pending_client_op = Some(PendingClientOp::Put {
                        req,
                        req_shard,
                        key,
                        value,
                    });
                    proof { assert(self.inv_api(api)); }
                    return false;
                }
                let ghost pre_state = self.model@.value();
                let ghost pre_branch = self.branch@;
                let ghost pre_journal = self.journal@;
                proof { self.journal.view_seq_end_ensures(); }
                let mut puts = Vec::<KeyedMessage>::new();
                puts.push(KeyedMessage {
                    key,
                    message: Message::Define { value },
                });
                match self.branch.put_batch(&puts) {
                    BranchBetreePutResult::Noop => {
                        self.pending_client_op = Some(PendingClientOp::Put {
                            req,
                            req_shard,
                            key,
                            value,
                        });
                        proof { assert(self.inv_api(api)); }
                        false
                    },
                    BranchBetreePutResult::Applied => {
                        self.journal.insert(key, value);
                        proof { self.journal.view_seq_end_ensures(); }
                        let reply = Reply {
                            output: Output::PutOutput,
                            id: req.id,
                        };
                        let ghost records = MemtableImpl::history_from_seq(
                            pre_state.state.branch.betree.memtable.seq_end,
                            puts@,
                        );
                        let ghost new_journal = AtomicJournalState::State {
                            journal: self.journal@,
                            ..pre_state.state.journal
                        };
                        let ghost post_state = UnifiedCacheBetreeProgramModel {
                            state: UnifiedCacheBetreeSystem::State {
                                journal: new_journal,
                                branch: self.branch@,
                                ..pre_state.state
                            },
                        };
                        let tracked mut model =
                            KVStoreTokenized::model::arbitrary();
                        proof {
                            let map_req = req.mapspec_req();
                            let map_reply = reply.mapspec_reply();
                            assert(puts@ == seq![KeyedMessage::from_kv(
                                key,
                                value,
                            )]);
                            assert(records == MsgHistory::singleton_at(
                                pre_state.state.branch.betree.memtable.seq_end,
                                KeyedMessage::from_kv(key, value),
                            )) by {

                                assert_maps_equal!(
                                    records.msgs,
                                    MsgHistory::singleton_at(
                                        pre_state.state.branch.betree
                                            .memtable.seq_end,
                                        KeyedMessage::from_kv(key, value),
                                    ).msgs,
                                    lsn => { }
                                );
                            }
                            assert(pre_state.state.branch == pre_branch);
                            assert(pre_state.state.journal.journal
                                == pre_journal);
                            assert(pre_state.state.journal.journal.seq_end()
                                == pre_state.state.branch.betree
                                    .memtable.seq_end);
                            let journal_records = MsgHistory::singleton_at(
                                pre_journal.seq_end(),
                                KeyedMessage::from_kv(key, value),
                            );
                            assert(records == journal_records);
                            assert(CachedJournal::State::put(
                                pre_journal,
                                self.journal@,
                                CachedJournal::Label::Put {
                                    messages: journal_records,
                                },
                            ));
                            assert(CachedJournal::State::put(
                                pre_state.state.journal.journal,
                                self.journal@,
                                CachedJournal::Label::Put {
                                    messages: journal_records,
                                },
                            ));
                            assert(CachedJournal::State::next_by(
                                pre_state.state.journal.journal,
                                self.journal@,
                                CachedJournal::Label::Put {
                                    messages: journal_records,
                                },
                                CachedJournal::Step::put(),
                            )) by {
                                reveal(CachedJournal::State::next_by);
                            }
                            assert(CachedJournal::State::next(
                                pre_state.state.journal.journal,
                                self.journal@,
                                CachedJournal::Label::Put {
                                    messages: journal_records,
                                },
                            )) by {
                                reveal(CachedJournal::State::next);
                            }
                            assert(AtomicJournalState::State::put(
                                pre_state.state.journal,
                                new_journal,
                                AtomicJournalState::Label::Put {
                                    messages: records,
                                },
                                self.journal@,
                            )) by {

                            }
                            assert(AtomicJournalState::State::next_by(
                                pre_state.state.journal,
                                new_journal,
                                AtomicJournalState::Label::Put {
                                    messages: records,
                                },
                                AtomicJournalState::Step::put(self.journal@),
                            )) by {
                                reveal(AtomicJournalState::State::next_by);
                            }
                            assert(AtomicJournalState::State::next(
                                pre_state.state.journal,
                                new_journal,
                                AtomicJournalState::Label::Put {
                                    messages: records,
                                },
                            )) by {
                                reveal(AtomicJournalState::State::next);
                            }
                            assert(AtomicBranchBetreeState::State::next(
                                pre_state.state.branch,
                                self.branch@,
                                AtomicBranchBetreeState::Label::Put {
                                    puts: records,
                                },
                            ));
                            AtomicBranchBetreeState::State::put_effect(
                                pre_state.state.branch,
                                self.branch@,
                                records,
                            );
                            CachedBranchBetree::State::put_effect(
                                pre_state.state.branch.betree,
                                self.branch@.betree,
                                records,
                            );

                            crate::betree::Memtable_v::Memtable::apply_puts_end(
                                pre_state.state.branch.betree.memtable,
                                records,
                            );
                            assert(self.branch@.betree.memtable.seq_end
                                == records.seq_end);
                            assert(records.seq_end == pre_journal.seq_end() + 1);
                            assert(self.journal@.seq_end()
                                == pre_journal.seq_end() + 1);
                            assert(post_state.state.journal.journal.seq_end()
                                == post_state.state.branch.betree
                                    .memtable.seq_end);
                            assert(UnifiedCacheBetreeSystem::State::execute_put(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheBetreeSystem::Label::Execute {
                                    req: map_req,
                                    reply: map_reply,
                                },
                                new_journal,
                                self.branch@,
                            ));
                            assert(UnifiedCacheBetreeSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheBetreeSystem::Label::Execute {
                                    req: map_req,
                                    reply: map_reply,
                                },
                                UnifiedCacheBetreeSystem::Step::execute_put(
                                    new_journal,
                                    self.branch@,
                                ),
                            )) by {
                                reveal(UnifiedCacheBetreeSystem::State::next_by);
                            }
                            assert(UnifiedCacheBetreeSystem::State::next(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheBetreeSystem::Label::Execute {
                                    req: map_req,
                                    reply: map_reply,
                                },
                            )) by {
                                reveal(UnifiedCacheBetreeSystem::State::next);
                            }
                            UnifiedCacheBetreeProgramModel::lift_execute_step(
                                pre_state,
                                post_state,
                                map_req,
                                map_reply,
                            );
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }
                        let tracked new_reply_token =
                            self.instance.borrow().execute_transition(
                                KVStoreTokenized::Label::ExecuteOp { req, reply },
                                post_state,
                                &mut model,
                                req_shard.get(),
                            );
                        self.model = Tracked(model);
                        api.send_reply(reply, Tracked(new_reply_token), true);
                        proof {
                            assert(self.phase_alignment());
                            assert(self.pending_client_op_wf());
                            assert(self.common_inv());
                            assert(self.inv());
                            assert(self.inv_api(api));
                        }
                        true
                    },
                }
            },
            Some(PendingClientOp::Query { req, req_shard, key }) => {
                proof { self.ready_query_cache_certificate(); }
                let ghost pre_state = self.model@.value();
                let ghost pre_cache = self.cache@;
                let query_result = self.branch.query_with_cache(
                    &mut self.cache,
                    key,
                );
                proof {
                    match self.compaction_work {
                        Some(work) if work.phase is Scanning => {
                            self.branch.compactors@[0].merge->0
                                .cache_inv_preserved_by_backward_valid_reads(
                                    pre_cache,
                                    self.cache@,
                                );
                            assert(self.branch.compactors@[0]
                                .cache_inv(self.cache@));
                        },
                        _ => {},
                    }
                    match self.store_flush_phase {
                        StoreFlushPhaseImpl::Building { idx, .. }
                        | StoreFlushPhaseImpl::Sealed { idx, .. } => {
                            self.branch.wip_branches@[idx as int]
                                .cache_inv_preserved_by_valid_reads(
                                    pre_cache,
                                    self.cache@,
                                );
                        },
                        _ => {},
                    }
                }
                match query_result {
                    BranchBetreeQueryResult::Hit {
                        value,
                        access,
                    } => {
                        let reply = Reply {
                            output: Output::QueryOutput { value },
                            id: req.id,
                        };
                        let ghost post_state = UnifiedCacheBetreeProgramModel {
                            state: UnifiedCacheBetreeSystem::State {
                                cache: self.cache@,
                                ..pre_state.state
                            },
                        };
                        let tracked mut model =
                            KVStoreTokenized::model::arbitrary();
                        proof {
                            let map_req = req.mapspec_req();
                            let map_reply = reply.mapspec_reply();
                            assert(pre_state.state.cache == pre_cache);
                            assert(UnifiedCacheBetreeSystem::State::execute_query(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheBetreeSystem::Label::Execute {
                                    req: map_req,
                                    reply: map_reply,
                                },
                                self.cache@,
                                access@,
                            ));
                            assert(UnifiedCacheBetreeSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheBetreeSystem::Label::Execute {
                                    req: map_req,
                                    reply: map_reply,
                                },
                                UnifiedCacheBetreeSystem::Step::execute_query(
                                    self.cache@,
                                    access@,
                                ),
                            )) by {
                                reveal(UnifiedCacheBetreeSystem::State::next_by);
                            }
                            assert(UnifiedCacheBetreeSystem::State::next(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheBetreeSystem::Label::Execute {
                                    req: map_req,
                                    reply: map_reply,
                                },
                            )) by {
                                reveal(UnifiedCacheBetreeSystem::State::next);
                            }
                            UnifiedCacheBetreeProgramModel::lift_execute_step(
                                pre_state,
                                post_state,
                                map_req,
                                map_reply,
                            );
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }
                        let tracked new_reply_token =
                            self.instance.borrow().execute_transition(
                                KVStoreTokenized::Label::ExecuteOp { req, reply },
                                post_state,
                                &mut model,
                                req_shard.get(),
                            );
                        self.model = Tracked(model);
                        api.send_reply(reply, Tracked(new_reply_token), true);
                        proof {
                            assert(self.phase_alignment());
                            assert(self.pending_client_op_wf());
                            assert(self.common_inv());
                            assert(self.inv());
                            assert(self.inv_api(api));
                        }
                        true
                    },
                    BranchBetreeQueryResult::NeedCacheLoad { addr, handle } => {
                        self.pending_client_op = Some(PendingClientOp::Query {
                            req,
                            req_shard,
                            key,
                        });
                        proof {
                            let owned = self.branch.ownership.betree.active_aus()
                                + self.branch.ownership.branches
                                    .active_summary_aus();
                            assert(owned.contains(addr@.au));
                            assert(addresses_in_aus(owned).contains(addr@));
                            assert(addr@ != spec_superblock_addr());
                            assert(self.cache_read_io_lag_inv());
                        }
                        self.issue_acquired_cache_read_io(
                            addr,
                            handle,
                            CacheReadPurpose::ClientQuery,
                            api,
                        )
                    },
                    BranchBetreeQueryResult::CacheFull => {
                        self.pending_client_op = Some(PendingClientOp::Query {
                            req,
                            req_shard,
                            key,
                        });
                        api.log("unified-cache Betree query waits for cache space");
                        proof { assert(self.inv_api(api)); }
                        false
                    },
                    BranchBetreeQueryResult::Blocked => {
                        self.pending_client_op = Some(PendingClientOp::Query {
                            req,
                            req_shard,
                            key,
                        });
                        api.log("unified-cache Betree query waits");
                        proof { assert(self.inv_api(api)); }
                        false
                    },
                    BranchBetreeQueryResult::InvalidPage => {
                        self.pending_client_op = Some(PendingClientOp::Query {
                            req,
                            req_shard,
                            key,
                        });
                        api.log("unified-cache Betree query found an invalid page");
                        proof { assert(self.inv_api(api)); }
                        false
                    },
                }
            },
        }
    }

    fn record_execute_put(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        key: Key,
        value: Value,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            req.input == (Input::PutInput { key, value }),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        self.pending_client_op = Some(PendingClientOp::Put {
            req,
            req_shard,
            key,
            value,
        });
        let _ = self.continue_pending_client_op(api);
    }

    fn record_execute_query(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        key: Key,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            req.input == (Input::QueryInput { key }),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        self.pending_client_op = Some(PendingClientOp::Query {
            req,
            req_shard,
            key,
        });
        let _ = self.continue_pending_client_op(api);
    }

    fn record_accept_sync_request(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            req.input is SyncInput,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        if self.sync_requests.contains_id(req.id) {
            api.log("duplicate unified-cache Betree sync request ignored");
            proof { assert(self.inv_api(api)); }
            return;
        }

        let ghost old_ids = self.sync_requests.all_ids();
        let ghost pre_state = self.model@.value();
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                sync_req_map: pre_state.state.sync_req_map.insert(
                    req.id,
                    pre_state.state.branch.betree.memtable.seq_end,
                ),
                ..pre_state.state
            },
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();

        proof {
            assert(!old_ids.to_set().contains(req.id));
            assert(!pre_state.state.sync_req_map.contains_key(req.id));
            assert(pre_state.state.client_ready());
            assert(UnifiedCacheBetreeSystem::State::accept_sync_request(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::AcceptSyncRequest {
                    sync_req_id: req.id,
                },
            )) by {

            }
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::AcceptSyncRequest {
                    sync_req_id: req.id,
                },
                UnifiedCacheBetreeSystem::Step::accept_sync_request(),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            assert(UnifiedCacheBetreeSystem::State::next(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::AcceptSyncRequest {
                    sync_req_id: req.id,
                },
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next);
            }
            UnifiedCacheBetreeProgramModel::lift_accept_sync_step(
                pre_state,
                post_state,
                req.id,
            );
            tracked_swap(self.model.borrow_mut(), &mut model);
        }

        let tracked _accepted = self.instance.borrow().accept_sync_request(
            KVStoreTokenized::Label::RequestSyncOp {
                sync_req_id: req.id,
            },
            post_state,
            &mut model,
            req_shard.get(),
        );
        self.model = Tracked(model);
        self.sync_requests.push_buffered(req.id);

        proof {
            assert(self.sync_requests.all_ids().to_set()
                =~= self.state().sync_req_map.dom()) by {
                assert(self.sync_requests.all_ids().to_set()
                    =~= old_ids.to_set().insert(req.id));
                assert(self.state().sync_req_map.dom()
                    =~= pre_state.state.sync_req_map.dom().insert(req.id));
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.journal_cleaning_reqs@[i]
                ] <= self.sync_requests.sync_target_lsn as nat by {
                let id = self.sync_requests.journal_cleaning_reqs@[i];
                assert(id != req.id) by {
                    if id == req.id {
                        assert(self.sync_requests.journal_cleaning_reqs@
                            == old(self).sync_requests.journal_cleaning_reqs@);
                        assert(old_ids[i]
                            == old(self).sync_requests.journal_cleaning_reqs@[i]);
                        assert(old_ids[i] == req.id);
                        assert(old_ids.contains(req.id));
                        assert(old_ids.to_set().contains(req.id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id]
                    == pre_state.state.sync_req_map[id]);
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.superblocking_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.superblocking_reqs@[i]
                ] <= match &self.sync_phase {
                    BetreeSyncPhaseImpl::SuperblockWriteIssued { image, .. } =>
                        image@@.journal_seq_end,
                    _ => self.state().journal.persistent_seq_end,
                } by {
                let id = self.sync_requests.superblocking_reqs@[i];
                assert(id != req.id) by {
                    if id == req.id {
                        assert(self.sync_requests.superblocking_reqs@
                            == old(self).sync_requests.superblocking_reqs@);
                        let j = old(self).sync_requests.journal_cleaning_reqs@.len()
                            as int + i;
                        assert(0 <= j < old_ids.len());
                        assert(old_ids[j] == id);
                        assert(old_ids.contains(req.id));
                        assert(old_ids.to_set().contains(req.id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id]
                    == pre_state.state.sync_req_map[id]);
            }
            assert(self.sync_wf());
            assert(self.common_inv());
            assert(self.inv());
            assert(self.inv_api(api));
        }
        api.log("unified-cache Betree sync request buffered");
    }

    fn promote_buffered_sync_requests(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is None,
            old(self).sync_requests.journal_cleaning_reqs@.len() == 0,
            old(self).sync_requests.superblocking_reqs@.len() == 0,
            old(self).sync_counter + 1 != STORE_SYNC_INTERVAL
                || old(self).compaction_work is None,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.state() == old(self).state(),
            progress <==> old(self).sync_requests.buffered_reqs@.len() > 0,
    {
        if self.sync_requests.buffered_reqs.len() == 0 {
            proof { assert(self.inv_api(api)); }
            return false;
        }
        proof {
            self.ready_journal_sync_metadata_facts();
        }
        let ghost pre_sync = self.sync_requests;
        let target = self.branch.exec_seq_end();
        self.sync_requests.promote_buffered(target);
        let store_cycle = self.sync_counter + 1 == STORE_SYNC_INTERVAL;
        if store_cycle {
            self.sync_counter = 0;
            self.store_flush_phase = StoreFlushPhaseImpl::Pending;
        } else {
            self.sync_counter = self.sync_counter + 1;
        }
        proof {
            assert(self.state() == old(self).state());
            assert(self.sync_requests.all_ids() == pre_sync.all_ids());
            assert forall |i: int|
                0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.journal_cleaning_reqs@[i]
                ] <= self.sync_requests.sync_target_lsn as nat by {
                assert(self.sync_requests.journal_cleaning_reqs@[i]
                    == pre_sync.buffered_reqs@[i]);
                assert(self.sync_requests.sync_target_lsn as nat
                    == self.state().branch.betree.memtable.seq_end);
            }
            assert(self.state().journal.persistent_seq_end
                <= self.sync_requests.sync_target_lsn as nat);
            assert(self.store_flush_wf());
            assert(self.sync_wf());
            assert(self.common_inv());
            assert(self.inv_api(api));
        }
        if store_cycle {
            api.log("unified-cache Betree store sync cycle promoted");
        } else {
            api.log("unified-cache Betree journal sync cycle promoted");
        }
        true
    }

    fn record_store_flush_begin(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).store_flush_phase is Pending,
            old(self).compaction_work is None,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress,
    {
        let seq_end = self.branch.exec_seq_end();
        if self.branch.wip_branches.len() != 0 {
            self.store_flush_phase = StoreFlushPhaseImpl::None;
            proof {
                assert(self.store_flush_wf());
                assert(self.common_inv());
                assert(self.inv_api(api));
            }
            api.log("unified-cache Betree store flush found an existing WIP branch");
            return true;
        }
        proof {
            self.ready_journal_cache_certificate();
            assert(self.branch.wip_branches@.len() == 0);
        }
        if self.branch.memtable.is_empty() {
            self.store_flush_phase = StoreFlushPhaseImpl::Ready { seq_end };
            proof {
                assert(self.branch.memtable@.is_empty());
                assert(self.store_flush_wf());
                assert(self.common_inv());
                assert(self.inv_api(api));
            }
            api.log("unified-cache Betree empty memtable ready for store sync");
            return true;
        }

        let ghost pre_state = self.model@.value();
        match self.branch.branch_begin_bulk(
            BETREE_BRANCH_FREE_AU_THRESHOLD,
        ) {
            BranchBetreeBulkStartResult::Started { idx } => {
                let ghost empty = Map::<Address, RawPage>::empty();
                let ghost access = PageAccess::empty();
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        branch: self.branch@,
                        ..pre_state.state
                    },
                };
                let tracked mut model =
                    KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    let access = PageAccess::empty();
                    assert(pre_state.state.branch == old(self).branch@);
                    assert(access == PageAccess::empty());
                    assert(access.reads() == empty);
                    assert(access.writes() == empty);
                    assert(AtomicBranchBetreeState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access,
                        },
                    ));
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        pre_state.state.cache,
                        Cache::Label::Access {
                            reads: empty,
                            writes: empty,
                        },
                    )) by {
                        Cache::State::access_empty_is_noop(
                            pre_state.state.cache,
                        );
                    }
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            Set::empty(),
                            Set::empty(),
                            access,
                            pre_state.state.cache,
                            self.branch@,
                        )) by {

                        assert(pre_state.state.branch.control.reclaimable(
                            Set::empty(),
                        ) =~= Set::<AU>::empty()) by {

                        }
                        assert_sets_equal!(
                            (pre_state.state.free_aus - Set::empty())
                                + pre_state.state.branch.control.reclaimable(
                                    Set::empty(),
                                ),
                            pre_state.state.free_aus,
                            au => {}
                        );
                    }
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_alloc_access(
                                Set::empty(),
                                Set::empty(),
                                access,
                                pre_state.state.cache,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.store_flush_phase = StoreFlushPhaseImpl::Building {
                    idx,
                    seq_end,
                };
                proof {
                    assert(idx == 0);
                    assert(self.branch.wip_branches@.len() == 1);
                    assert(self.branch.wip_branches@[idx as int]
                        .bulk_builder is Some);
                    assert(!self.branch.wip_branches@[idx as int].sealed);
                    assert(self.branch.wip_branches@[idx as int]
                        .mini_allocator.i().all_aus().is_empty());
                    assert(self.branch.wip_branches@[idx as int]
                        .mini_allocator.bounded(self.disk_au_count));
                    assert(self.branch.memtable.seq_end == seq_end);
                    assert(self.store_flush_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree memtable bulk build started");
                true
            },
            BranchBetreeBulkStartResult::Empty => {
                self.store_flush_phase = StoreFlushPhaseImpl::None;
                proof {
                    assert(self.store_flush_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                true
            },
            BranchBetreeBulkStartResult::Overflow
            | BranchBetreeBulkStartResult::InvalidCapacity
            | BranchBetreeBulkStartResult::Blocked => {
                self.store_flush_phase = StoreFlushPhaseImpl::None;
                proof {
                    assert(self.store_flush_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree store flush planning failed; using journal sync");
                true
            },
        }
    }

    fn record_wip_branch_refill(
        &mut self,
        idx: usize,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            match old(self).store_flush_phase {
                StoreFlushPhaseImpl::Building {
                    idx: phase_idx,
                    ..
                } => phase_idx == idx,
                _ => false,
            } || match old(self).compaction_work {
                Some(work) => {
                    &&& work.output_idx == Some(idx)
                    &&& (work.phase is Scanning
                        || work.phase is FinishingInput
                        || work.phase is FinishingLevels
                        || work.phase is Sealing)
                },
                None => false,
            },
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            self.ready_branch_allocation_certificate();
        }
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch = self.branch@;
        let allocation = self.au_pool.alloc(
            self.disk_au_count,
            BETREE_BRANCH_FREE_AU_THRESHOLD,
        );
        let allocation = match allocation {
            Some(allocation) => allocation,
            None => {
                proof { assert(self.inv_api(api)); }
                return false;
            },
        };
        let ghost allocs = allocation.as_set();
        proof {
            allocation.vec_set_matches(self.disk_au_count);
        }
        let aus = allocation.aus;
        proof {
            assert(MiniAllocatorImpl::iau_seq_unique(aus@)) by {
                assert forall |i: int, j: int|
                    0 <= i < aus@.len()
                        && 0 <= j < aus@.len()
                        && #[trigger] aus@[i] == #[trigger] aus@[j]
                    implies i == j by {
                    assert((aus@[i] as nat)
                        == (allocation.run.start as nat) + (i as nat));
                    assert((aus@[j] as nat)
                        == (allocation.run.start as nat) + (j as nat));
                }
            }
            assert(iau_vec_set(aus@) =~= allocs);
            assert(allocs <= pre_pool);
            assert(pre_pool.disjoint(pre_branch.betree.owned_aus()));
            assert(pre_branch.betree.is_fresh(allocs)) by {


            }
        }
        match self.branch.branch_fill_aus(idx, aus) {
            BranchBetreeWipResult::Noop => {
                proof { assert(false); }
                false
            },
            BranchBetreeWipResult::Applied { idx: post_idx } => {
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        free_aus: self.au_pool@,
                        branch: self.branch@,
                        ..pre_state.state
                    },
                };
                let tracked mut model =
                    KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    let access = PageAccess::empty();
                    assert(post_idx == idx);
                    assert(pre_state.state.branch == pre_branch);
                    assert(pre_state.state.free_aus =~= pre_pool);
                    assert(allocs.disjoint(
                        pre_state.state.branch.control.protected_aus(),
                    ));
                    assert(AtomicBranchBetreeState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs,
                            deallocs: Set::empty(),
                            access,
                        },
                    ));
                    assert_sets_equal!(
                        (pre_state.state.free_aus - allocs)
                            + pre_state.state.branch.control.reclaimable(
                                Set::empty(),
                            ),
                        self.au_pool@,
                        au => {

                        }
                    );
                    PageAccess::empty_cached_access_is_empty();
                    assert(access.reads()
                        == Map::<Address, RawPage>::empty());
                    assert(access.writes()
                        == Map::<Address, RawPage>::empty());
                    Cache::State::access_empty_is_noop(pre_state.state.cache);
                    assert(UnifiedCacheBetreeSystem::State::branch_internal_alloc_access(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        allocs,
                        Set::empty(),
                        access,
                        pre_state.state.cache,
                        self.branch@,
                    )) by {

                    }
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::branch_internal_alloc_access(
                            allocs,
                            Set::empty(),
                            access,
                            pre_state.state.cache,
                            self.branch@,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    assert(self.store_flush_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree WIP branch AU refill");
                true
            },
        }
    }

    fn record_store_branch_abort(
        &mut self,
        idx: usize,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            match old(self).store_flush_phase {
                StoreFlushPhaseImpl::Building {
                    idx: phase_idx,
                    ..
                } | StoreFlushPhaseImpl::Sealed {
                    idx: phase_idx,
                    ..
                } => phase_idx == idx,
                _ => false,
            },
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.store_flush_phase is None,
            progress,
    {
        proof {
            self.ready_branch_allocation_certificate();
        }
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch = self.branch@;
        let result = self.branch.branch_abort(idx);
        let deallocs = match result {
            BranchBetreeAbortResult::Aborted { deallocs } => deallocs,
        };
        let ghost dealloc_set = iau_seq_set(deallocs@);
        proof {
            assert(iau_vec_set(deallocs@) =~= dealloc_set) by {
                assert forall |au: AU|
                    #[trigger] iau_vec_set(deallocs@).contains(au)
                        <==> dealloc_set.contains(au) by {
                }
            }
            assert(dealloc_set
                == old(self).branch.wip_branches@[idx as int]
                    .mini_allocator.i().all_aus());
            assert(pre_pool.disjoint(dealloc_set)) by {
                assert(dealloc_set <= pre_branch.betree.owned_aus()) by {

                }
            }
            assert forall |i: int| 0 <= i < deallocs@.len() implies {
                &&& 0 < #[trigger] (deallocs@[i] as nat)
                &&& (deallocs@[i] as nat) < self.disk_au_count as nat
            } by {
                assert(old(self).branch.wip_branches@[idx as int]
                    .mini_allocator.bounded(self.disk_au_count));
                let au = deallocs@[i] as nat;
                assert(dealloc_set.contains(au));
            }
        }
        self.au_pool.free_aus(self.disk_au_count, &deallocs);

        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                free_aus: self.au_pool@,
                branch: self.branch@,
                ..pre_state.state
            },
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
            let access = PageAccess::empty();
            assert(pre_state.state.branch == pre_branch);
            assert(pre_state.state.free_aus =~= pre_pool);
            assert(dealloc_set.disjoint(
                pre_state.state.branch.control.protected_aus(),
            ));
            assert(AtomicBranchBetreeState::State::next(
                pre_state.state.branch,
                self.branch@,
                AtomicBranchBetreeState::Label::InternalAllocAccess {
                    allocs: Set::empty(),
                    deallocs: dealloc_set,
                    access,
                },
            ));
            assert_sets_equal!(
                pre_state.state.branch.control.reclaimable(dealloc_set),
                dealloc_set,
                au => {

                }
            );
            assert_sets_equal!(
                (pre_state.state.free_aus - Set::empty())
                    + pre_state.state.branch.control.reclaimable(
                        dealloc_set,
                    ),
                self.au_pool@,
                au => {}
            );
            PageAccess::empty_cached_access_is_empty();
            assert(access.reads()
                == Map::<Address, RawPage>::empty());
            assert(access.writes()
                == Map::<Address, RawPage>::empty());
            Cache::State::access_empty_is_noop(pre_state.state.cache);
            assert(UnifiedCacheBetreeSystem::State::branch_internal_alloc_access(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Internal,
                Set::empty(),
                dealloc_set,
                access,
                pre_state.state.cache,
                self.branch@,
            )) by {

            }
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Internal,
                UnifiedCacheBetreeSystem::Step::branch_internal_alloc_access(
                    Set::empty(),
                    dealloc_set,
                    access,
                    pre_state.state.cache,
                    self.branch@,
                ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            UnifiedCacheBetreeProgramModel::lift_internal_step(
                pre_state,
                post_state,
            );
        }
        let tracked _internal_token = self.instance.borrow().internal(
            KVStoreTokenized::Label::InternalOp {},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);
        self.store_flush_phase = StoreFlushPhaseImpl::None;
        proof {
            assert(self.store_flush_wf());
            assert(self.common_inv());
            assert(self.inv_api(api));
        }
        api.log("unified-cache Betree WIP branch aborted");
        true
    }

    fn record_store_stage_page(
        &mut self,
        idx: usize,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            match old(self).store_flush_phase {
                StoreFlushPhaseImpl::Building {
                    idx: phase_idx,
                    ..
                } => phase_idx == idx,
                _ => false,
            },
            old(self).branch.wip_branches@[idx as int]
                .memtable_builder().phase is Leaves
                || old(self).branch.wip_branches@[idx as int]
                    .memtable_builder().phase is Index,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let ghost pre_state = self.model@.value();
        match self.branch.branch_stage_bulk_page(
            &mut self.cache,
            idx,
            self.disk_au_count,
            self.disk_page_count,
        ) {
            BranchBetreeBuildResult::NeedsAUs
            | BranchBetreeBuildResult::CacheFull
            | BranchBetreeBuildResult::Blocked => {
                proof { assert(self.inv_api(api)); }
                false
            },
            BranchBetreeBuildResult::InvalidPage => {
                proof { assert(self.inv_api(api)); }
                self.record_store_branch_abort(idx, api)
            },
            BranchBetreeBuildResult::Applied {
                idx: post_idx,
                prepared_cache,
                access,
                event,
            } => {
                let ghost prepared_cache_v = prepared_cache@;
                let ghost access_v = access@;
                let ghost event_v = event@;
                let ghost branch_event = BranchBuildEvent::StagePage {
                    addr: event_v->addr,
                };
                let ghost reserve_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: prepared_cache_v,
                        ..pre_state.state
                    },
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        ..reserve_state.state
                    },
                };
                let tracked mut model =
                    KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::cache_internal(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        prepared_cache_v,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::cache_internal(
                            prepared_cache_v,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        reserve_state,
                    );
                }
                let tracked _reserve_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    reserve_state,
                    &mut model,
                );
                proof {
                    assert(post_idx == idx);
                    assert(event_v is StagePage);
                    assert(branch_event.cached_event(access_v) == event_v) by {

                    }
                    assert(AtomicBranchBetreeState::State::next(
                        reserve_state.state.branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access_v,
                        },
                    ));
                    assert_sets_equal!(
                        (reserve_state.state.free_aus - Set::empty())
                            + reserve_state.state.branch.control.reclaimable(
                                Set::empty(),
                            ),
                        reserve_state.state.free_aus,
                        au => {

                        }
                    );
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            reserve_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            Set::empty(),
                            Set::empty(),
                            access_v,
                            self.cache@,
                            self.branch@,
                        )) by {

                    }
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_alloc_access(
                                Set::empty(),
                                Set::empty(),
                                access_v,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        reserve_state,
                        post_state,
                    );
                }
                let tracked _access_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    );
                    Cache::State::inv_next(
                        prepared_cache_v,
                        self.cache@,
                        Cache::Label::Access {
                            reads: access_v.reads(),
                            writes: access_v.writes(),
                        },
                    );
                    assert(self.store_flush_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree staged one branch page");
                true
            },
        }
    }

    fn record_store_bulk_seal(
        &mut self,
        idx: usize,
        seq_end: u64,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).store_flush_phase == (StoreFlushPhaseImpl::Building {
                idx,
                seq_end,
            }),
            old(self).branch.wip_branches@[idx as int]
                .memtable_builder().phase is ReadyLeafRoot
                || old(self).branch.wip_branches@[idx as int]
                    .memtable_builder().phase is ReadyIndexRoot,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            self.ready_branch_allocation_certificate();
        }
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch = self.branch@;
        let ghost pre_wip_aus = self.branch.wip_branches@[idx as int]
            .mini_allocator.i().all_aus();
        match self.branch.branch_bulk_seal(
            &mut self.cache,
            idx,
            self.disk_au_count,
            self.disk_page_count,
        ) {
            BranchBetreeBulkSealResult::NeedsAUs
            | BranchBetreeBulkSealResult::CacheFull
            | BranchBetreeBulkSealResult::Blocked => {
                proof { assert(self.inv_api(api)); }
                false
            },
            BranchBetreeBulkSealResult::InvalidPage => {
                proof { assert(self.inv_api(api)); }
                self.record_store_branch_abort(idx, api)
            },
            BranchBetreeBulkSealResult::Sealed {
                idx: post_idx,
                root,
                aux_ptr,
                prepared_cache,
                access,
                event,
                deallocs,
                branch: _,
            } => {
                let ghost prepared_cache_v = prepared_cache@;
                let ghost access_v = access@;
                let ghost event_v = event@;
                let ghost dealloc_set = iau_vec_set(deallocs@);
                let ghost branch_event = BranchBuildEvent::BulkSeal {
                    root: root@,
                    aux_ptr: iopt_addr(aux_ptr),
                };
                proof {
                    assert(post_idx == idx);
                    assert(event_v is BulkSeal);
                    assert(dealloc_set <= pre_wip_aus);
                    assert(pre_pool.disjoint(dealloc_set)) by {
                        assert(pre_wip_aus <= pre_branch.betree.owned_aus()) by {

                        }
                    }
                    assert forall |i: int| 0 <= i < deallocs@.len() implies {
                        &&& 0 < #[trigger] (deallocs@[i] as nat)
                        &&& (deallocs@[i] as nat)
                            < self.disk_au_count as nat
                    } by {
                        let au = deallocs@[i] as nat;
                        assert(dealloc_set.contains(au));
                        assert(old(self).branch.wip_branches@[idx as int]
                            .mini_allocator.bounded(self.disk_au_count));
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &deallocs,
                );

                let ghost reserve_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: prepared_cache_v,
                        ..pre_state.state
                    },
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        free_aus: self.au_pool@,
                        ..reserve_state.state
                    },
                };
                let tracked mut model =
                    KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::cache_internal(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        prepared_cache_v,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::cache_internal(
                            prepared_cache_v,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        reserve_state,
                    );
                }
                let tracked _reserve_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    reserve_state,
                    &mut model,
                );
                proof {
                    assert(branch_event.cached_event(access_v) == event_v) by {

                    }
                    assert(AtomicBranchBetreeState::State::next(
                        reserve_state.state.branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: dealloc_set,
                            access: access_v,
                        },
                    ));
                    assert(dealloc_set.disjoint(
                        reserve_state.state.branch.control.protected_aus(),
                    ));
                    assert_sets_equal!(
                        reserve_state.state.branch.control.reclaimable(
                            dealloc_set,
                        ),
                        dealloc_set,
                        au => {

                        }
                    );
                    assert_sets_equal!(
                        (reserve_state.state.free_aus - Set::empty())
                            + reserve_state.state.branch.control.reclaimable(
                                dealloc_set,
                            ),
                        self.au_pool@,
                        au => {}
                    );
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            reserve_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            Set::empty(),
                            dealloc_set,
                            access_v,
                            self.cache@,
                            self.branch@,
                        )) by {

                    }
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_alloc_access(
                                Set::empty(),
                                dealloc_set,
                                access_v,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        reserve_state,
                        post_state,
                    );
                }
                let tracked _access_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.store_flush_phase = StoreFlushPhaseImpl::Sealed {
                    idx,
                    seq_end,
                };
                proof {
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    );
                    Cache::State::inv_next(
                        prepared_cache_v,
                        self.cache@,
                        Cache::Label::Access {
                            reads: access_v.reads(),
                            writes: access_v.writes(),
                        },
                    );
                    assert(self.store_flush_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree sealed memtable branch");
                true
            },
        }
    }

    fn record_store_install_root(
        &mut self,
        idx: usize,
        seq_end: u64,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).store_flush_phase == (StoreFlushPhaseImpl::Sealed {
                idx,
                seq_end,
            }),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            self.ready_branch_allocation_certificate();
            if self.branch.root is Some {
                self.ready_query_cache_certificate();
                let key = Key(0);
                assert(cached_betree_root_wf(
                    self.cache@,
                    self.branch.root.unwrap()@,
                )) by {


                    assert(cached_betree_query_valid(
                        self.cache@,
                        self.branch.root.unwrap()@,
                        key,
                        CACHE_SIZE_RECS as nat,
                        CACHE_SIZE_RECS as nat,
                        self.branch.ownership.betree.active_aus(),
                        self.branch.ownership.branches.active_summary_map(),
                        self.branch.ownership.branches.active_summary_aus(),
                    ));

                }
                let key = Key(0);
                assert(cached_betree_query_valid(
                    self.cache@,
                    self.branch.root.unwrap()@,
                    key,
                    CACHE_SIZE_RECS as nat,
                    CACHE_SIZE_RECS as nat,
                    self.branch.ownership.betree.active_aus(),
                    self.branch.ownership.branches.active_summary_map(),
                    self.branch.ownership.branches.active_summary_aus(),
                ));

                assert(self.branch.ownership.betree.active_aus().contains(
                    self.branch.root.unwrap()@.au,
                ));
                assert(addresses_in_aus(
                    self.branch.ownership.betree.active_aus()
                        + self.branch.ownership.branches.active_summary_aus(),
                ).contains(self.branch.root.unwrap()@));
                assert(self.branch.root.unwrap()@
                    != spec_superblock_addr());
            }
        }
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch = self.branch@;
        let ghost pre_branch_impl = *self;
        let allocation = match self.au_pool.alloc(
            self.disk_au_count,
            1,
        ) {
            Some(allocation) => allocation,
            None => {
                proof { assert(self.inv_api(api)); }
                return false;
            },
        };
        let ghost alloc_set = allocation.as_set();
        proof {
            allocation.vec_set_matches(self.disk_au_count);
            assert(alloc_set <= pre_pool);
        }
        let new_root = betree_addr_for_au(allocation.run.start);
        let rollback_aus = allocation.aus;
        proof {
            assert(new_root@.wf());
            assert(alloc_set == set![new_root@.au]) by {

                assert((allocation.run.end as nat)
                    == (allocation.run.start as nat) + 1);
                assert_sets_equal!(alloc_set, set![new_root@.au], au => {


                });
            }
            assert(pre_branch.betree.is_fresh(alloc_set)) by {


            }
            assert(pre_branch_impl.branch.ownership.betree.all_aus()
                .disjoint(alloc_set));
            assert(pre_branch_impl.branch.ownership.branches
                .all_summary_aus().disjoint(alloc_set));
            assert(pre_branch_impl.branch.wip_branches@[idx as int]
                .mini_allocator.i().all_aus().disjoint(alloc_set));
        }

        let attempt = if self.branch.root.is_none() {
            match self.branch.flush_initial_memtable_with_cache(
                &mut self.cache,
                idx,
                new_root,
            ) {
                BranchBetreeFlushResult::Flushed {
                    new_root: _,
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                } => StoreRootFlushAttempt::Flushed {
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                    reclaimed: Vec::<IAU>::new(),
                },
                BranchBetreeFlushResult::CacheFull => {
                    StoreRootFlushAttempt::CacheFull
                },
                BranchBetreeFlushResult::Blocked => {
                    StoreRootFlushAttempt::Blocked
                },
                BranchBetreeFlushResult::InvalidPage => {
                    StoreRootFlushAttempt::InvalidPage
                },
            }
        } else {
            match self.branch.flush_existing_memtable_with_cache(
                &mut self.cache,
                idx,
                new_root,
            ) {
                BranchBetreeExistingFlushResult::Flushed {
                    new_root: _,
                    reclaimed,
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                } => StoreRootFlushAttempt::Flushed {
                    prepared_cache,
                    access,
                    allocs,
                    deallocs,
                    reclaimed,
                },
                BranchBetreeExistingFlushResult::NeedCacheLoad {
                    addr,
                    handle,
                } => StoreRootFlushAttempt::NeedCacheLoad { addr, handle },
                BranchBetreeExistingFlushResult::CacheFull => {
                    StoreRootFlushAttempt::CacheFull
                },
                BranchBetreeExistingFlushResult::Blocked => {
                    StoreRootFlushAttempt::Blocked
                },
                BranchBetreeExistingFlushResult::InvalidPage => {
                    StoreRootFlushAttempt::InvalidPage
                },
            }
        };

        match attempt {
            StoreRootFlushAttempt::NeedCacheLoad { addr, handle } => {
                proof {
                    assert(self.au_pool@.disjoint(
                        iau_vec_set(rollback_aus@),
                    ));
                    assert forall |i: int|
                        0 <= i < rollback_aus@.len() implies {
                        &&& 0 < #[trigger] (rollback_aus@[i] as nat)
                        &&& (rollback_aus@[i] as nat)
                            < self.disk_au_count as nat
                    } by {
                        assert(iau_vec_set(rollback_aus@) =~= alloc_set);
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &rollback_aus,
                );
                proof {
                    assert(self.au_pool@ =~= pre_pool);
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        self.cache@,
                        cache_load_label(&addr),
                    );
                    assert(self.common_inv());
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.state().outstanding_cache_reqs
                        == Map::<ID, Address>::empty()) by {
                        assert_maps_equal!(
                            self.state().outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if self.state().outstanding_cache_reqs
                                    .contains_key(id)
                                {
                                    assert(self.outstanding_requests@
                                        .contains_key(id));
                                }
                            }
                        );
                    }
                    assert(addr == pre_branch_impl.branch.root.unwrap());
                    assert(pre_branch_impl.branch.root.unwrap()@
                        != spec_superblock_addr());
                    assert(addr@ != spec_superblock_addr());
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_read_io(
                    addr,
                    handle,
                    CacheReadPurpose::MemtableFlushRoot,
                    api,
                )
            },
            StoreRootFlushAttempt::CacheFull
            | StoreRootFlushAttempt::Blocked => {
                proof {
                    assert(self.au_pool@.disjoint(
                        iau_vec_set(rollback_aus@),
                    ));
                    assert forall |i: int|
                        0 <= i < rollback_aus@.len() implies {
                        &&& 0 < #[trigger] (rollback_aus@[i] as nat)
                        &&& (rollback_aus@[i] as nat)
                            < self.disk_au_count as nat
                    } by {
                        assert(iau_vec_set(rollback_aus@) =~= alloc_set);
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &rollback_aus,
                );
                proof {
                    assert(self.au_pool@ =~= pre_pool);
                    assert(self.inv_api(api));
                }
                false
            },
            StoreRootFlushAttempt::InvalidPage => {
                proof {
                    assert(self.au_pool@.disjoint(
                        iau_vec_set(rollback_aus@),
                    ));
                    assert forall |i: int|
                        0 <= i < rollback_aus@.len() implies {
                        &&& 0 < #[trigger] (rollback_aus@[i] as nat)
                        &&& (rollback_aus@[i] as nat)
                            < self.disk_au_count as nat
                    } by {
                        assert(iau_vec_set(rollback_aus@) =~= alloc_set);
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &rollback_aus,
                );
                proof {
                    assert(self.au_pool@ =~= pre_pool);
                    assert(self.inv_api(api));
                }
                self.record_store_branch_abort(idx, api)
            },
            StoreRootFlushAttempt::Flushed {
                prepared_cache,
                access,
                allocs,
                deallocs,
                reclaimed,
            } => {
                let ghost prepared_cache_v = prepared_cache@;
                let ghost access_v = access@;
                let ghost allocs_v = allocs@;
                let ghost deallocs_v = deallocs@;
                let ghost reclaimed_set = iau_seq_set(reclaimed@);
                proof {
                    assert(allocs_v == alloc_set);
                    assert(self.branch.ownership.betree.all_aus()
                        <= pre_branch_impl.branch.ownership.betree.all_aus()
                            + allocs_v);
                    assert(self.branch.ownership.branches.all_summary_aus()
                        <= pre_branch_impl.branch.ownership.branches
                            .all_summary_aus()
                            + pre_branch_impl.branch.wip_branches@[
                                idx as int
                            ].mini_allocator.i().all_aus());
                    assert(reclaimed_set
                        == pre_branch.control.reclaimable(deallocs_v));
                    assert(reclaimed_set <= deallocs_v);
                    if pre_branch_impl.branch.root is None {
                        assert(deallocs_v.is_empty());
                    } else {
                        assert(deallocs_v == set![
                            pre_branch_impl.branch.root.unwrap()@.au
                        ]);
                        assert(pre_branch_impl.branch.ownership.betree
                            .active_aus().contains(
                                pre_branch_impl.branch.root.unwrap()@.au,
                            ));
                        assert(pre_branch_impl.branch.ownership.betree
                            .all_aus().contains(
                                pre_branch_impl.branch.root.unwrap()@.au,
                            ));
                    }
                    assert(deallocs_v <= pre_branch.betree.owned_aus()) by {

                    }
                    assert(self.au_pool@.disjoint(reclaimed_set));
                    assert(reclaimed_set.disjoint(
                        self.journal.owned_aus(),
                    )) by {
                        assert(pre_branch.betree.owned_aus().disjoint(
                            self.journal.owned_aus(),
                        ));
                    }
                    assert forall |i: int|
                        0 <= i < reclaimed@.len() implies {
                        &&& 0 < #[trigger] (reclaimed@[i] as nat)
                        &&& (reclaimed@[i] as nat)
                            < self.disk_au_count as nat
                    } by {
                        let au = reclaimed@[i] as nat;
                        assert(reclaimed_set.contains(au));
                        assert(deallocs_v.contains(au));
                        assert(pre_branch_impl.branch.root is Some);
                        assert(au
                            == pre_branch_impl.branch.root.unwrap()@.au);
                        assert((pre_branch_impl.branch.ownership.betree
                            .all_aus()
                            + pre_branch_impl.branch.ownership.branches
                                .all_summary_aus()).contains(au));
                        assert(pre_branch_impl.branch_owned_aus_bounded());
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &reclaimed,
                );

                let ghost reserve_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: prepared_cache_v,
                        ..pre_state.state
                    },
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        free_aus: self.au_pool@,
                        ..reserve_state.state
                    },
                };
                let tracked mut model =
                    KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(UnifiedCacheBetreeSystem::State::cache_internal(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        prepared_cache_v,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::cache_internal(
                            prepared_cache_v,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        reserve_state,
                    );
                }
                let tracked _reserve_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    reserve_state,
                    &mut model,
                );
                proof {
                    let lbl = AtomicBranchBetreeState::Label::InternalAllocAccess {
                        allocs: allocs_v,
                        deallocs: deallocs_v,
                        access: access_v,
                    };
                    assert(AtomicBranchBetreeState::State::next(
                        reserve_state.state.branch,
                        self.branch@,
                        lbl,
                    ));
                    assert_sets_equal!(
                        (reserve_state.state.free_aus - allocs_v)
                            + reserve_state.state.branch.control.reclaimable(
                                deallocs_v,
                            ),
                        self.au_pool@,
                        au => {}
                    );
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            reserve_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            allocs_v,
                            deallocs_v,
                            access_v,
                            self.cache@,
                            self.branch@,
                        )) by {

                    }
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_alloc_access(
                                allocs_v,
                                deallocs_v,
                                access_v,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        reserve_state,
                        post_state,
                    );
                }
                let tracked _access_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.store_flush_phase = StoreFlushPhaseImpl::Ready {
                    seq_end,
                };
                proof {
                    assert(self.branch_owned_aus_bounded()) by {
                        assert forall |au: AU| #[trigger]
                            (self.branch.ownership.betree.all_aus()
                                + self.branch.ownership.branches
                                    .all_summary_aus()).contains(au)
                            implies 0 < au
                                && au < self.disk_au_count as nat by {
                            assert((pre_branch_impl.branch.ownership.betree
                                .all_aus()
                                + pre_branch_impl.branch.ownership.branches
                                    .all_summary_aus()
                                + allocs_v
                                + pre_branch_impl.branch.wip_branches@[
                                    idx as int
                                ].mini_allocator.i().all_aus()).contains(au));
                            if allocs_v.contains(au) {
                                assert(au == new_root@.au);
                                assert(0 < au
                                    && au < self.disk_au_count as nat);
                            } else if pre_branch_impl.branch
                                .ownership.betree.all_aus().contains(au)
                                || pre_branch_impl.branch.ownership.branches
                                    .all_summary_aus().contains(au)
                            {
                                assert(pre_branch_impl
                                    .branch_owned_aus_bounded());
                            } else {
                                assert(pre_branch_impl.branch.wip_branches@[
                                    idx as int
                                ].mini_allocator.i().all_aus().contains(au));
                                pre_branch_impl.branch.wip_branches@[
                                    idx as int
                                ].mini_allocator.owned_au_bounded(
                                    self.disk_au_count,
                                    au,
                                );
                            }
                        }
                    }
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    );
                    Cache::State::inv_next(
                        prepared_cache_v,
                        self.cache@,
                        Cache::Label::Access {
                            reads: access_v.reads(),
                            writes: access_v.writes(),
                        },
                    );
                    assert(self.store_flush_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree installed flushed memtable");
                true
            },
        }
    }

    fn record_deliver_completed_sync_reply(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is None,
            old(self).sync_requests.superblocking_reqs@.len() > 0,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_sync = self.sync_requests;
        let sync_req_id = self.sync_requests.pop_superblocking();
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                sync_req_map: pre_state.state.sync_req_map.remove(
                    sync_req_id,
                ),
                ..pre_state.state
            },
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            assert(pre_sync.all_ids().to_set().contains(sync_req_id));
            assert(pre_state.state.sync_req_map.contains_key(sync_req_id));
            assert(pre_state.state.sync_req_map[sync_req_id]
                <= pre_state.state.journal.persistent_seq_end) by {
                let i = (pre_sync.superblocking_reqs@.len() - 1) as int;
                assert(0 <= i < pre_sync.superblocking_reqs@.len());
                assert(pre_sync.superblocking_reqs@[i] == sync_req_id);
            }
            assert(UnifiedCacheBetreeSystem::State::deliver_sync_reply(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::DeliverSyncReply {
                    sync_req_id,
                },
            )) by {

            }
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::DeliverSyncReply {
                    sync_req_id,
                },
                UnifiedCacheBetreeSystem::Step::deliver_sync_reply(),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            assert(UnifiedCacheBetreeSystem::State::next(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::DeliverSyncReply {
                    sync_req_id,
                },
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next);
            }
            UnifiedCacheBetreeProgramModel::lift_deliver_sync_step(
                pre_state,
                post_state,
                sync_req_id,
            );
            tracked_swap(self.model.borrow_mut(), &mut model);
        }
        let tracked reply_token = self.instance.borrow().deliver_sync_reply(
            KVStoreTokenized::Label::ReplySyncOp { sync_req_id },
            post_state,
            &mut model,
        );
        self.model = Tracked(model);
        let reply = Reply {
            id: sync_req_id,
            output: Output::SyncOutput,
        };
        proof {
            assert(!self.sync_requests.all_ids().to_set().contains(
                sync_req_id,
            ));
            assert(self.sync_requests.all_ids().to_set()
                =~= self.state().sync_req_map.dom()) by {
                assert(self.sync_requests.all_ids().to_set()
                    =~= pre_sync.all_ids().to_set().remove(sync_req_id));
                assert(self.state().sync_req_map.dom()
                    =~= pre_state.state.sync_req_map.dom().remove(
                        sync_req_id,
                    ));
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.buffered_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.buffered_reqs@[i]
                ] <= self.state().branch.betree.memtable.seq_end by {
                let id = self.sync_requests.buffered_reqs@[i];
                assert(id != sync_req_id) by {
                    if id == sync_req_id {
                        let j = self.sync_requests.journal_cleaning_reqs@.len()
                            as int
                            + self.sync_requests.superblocking_reqs@.len()
                                as int
                            + i;
                        assert(0 <= j < self.sync_requests.all_ids().len());
                        assert(self.sync_requests.all_ids()[j]
                            == sync_req_id);
                        assert(self.sync_requests.all_ids().to_set()
                            .contains(sync_req_id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id]
                    == pre_state.state.sync_req_map[id]);
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.journal_cleaning_reqs@[i]
                ] <= self.sync_requests.sync_target_lsn as nat by {
                let id = self.sync_requests.journal_cleaning_reqs@[i];
                assert(id != sync_req_id) by {
                    if id == sync_req_id {
                        assert(self.sync_requests.all_ids()[i]
                            == sync_req_id);
                        assert(self.sync_requests.all_ids().to_set()
                            .contains(sync_req_id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id]
                    == pre_state.state.sync_req_map[id]);
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.superblocking_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.superblocking_reqs@[i]
                ] <= self.state().journal.persistent_seq_end by {
                let id = self.sync_requests.superblocking_reqs@[i];
                assert(id != sync_req_id) by {
                    if id == sync_req_id {
                        let j = self.sync_requests.journal_cleaning_reqs@.len()
                            as int + i;
                        assert(0 <= j < self.sync_requests.all_ids().len());
                        assert(self.sync_requests.all_ids()[j]
                            == sync_req_id);
                        assert(self.sync_requests.all_ids().to_set()
                            .contains(sync_req_id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id]
                    == pre_state.state.sync_req_map[id]);
                assert(pre_sync.superblocking_reqs@[i]
                    == self.sync_requests.superblocking_reqs@[i]);
            }
            assert(self.sync_wf());
            assert(self.common_inv());
            assert(self.inv_api(api));
        }
        api.send_reply(reply, Tracked(reply_token), true);
        api.log("unified-cache Betree sync reply delivered");
        true
    }

    fn record_journal_sync_begin(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is None,
            old(self).store_flush_phase is None,
            old(self).compaction_work is None,
            old(self).sync_requests.journal_cleaning_reqs@.len() > 0,
            old(self).sync_requests.superblocking_reqs@.len() == 0,
            old(self).journal.clean_watermark()
                >= old(self).sync_requests.sync_target_lsn as nat,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            !progress ==> self.outstanding_requests@
                == old(self).outstanding_requests@,
    {
        if self.branch.control.frozen_metadata.is_some() {
            api.log("unified-cache Betree journal sync waits for branch sync");
            proof { assert(self.inv_api(api)); }
            return false;
        }
        proof {
            self.ready_journal_sync_metadata_facts();
        }
        let target = self.sync_requests.sync_target_lsn;
        let frozen = match self.journal.freeze_for_commit(
            target,
            self.disk_au_count,
        ) {
            CleanForCommitResult::NeedsFlush {} => {
                proof { assert(false); }
                return false;
            },
            CleanForCommitResult::Frozen { frozen_journal } => {
                frozen_journal
            },
        };

        proof {
            assert(self.state().journal.persistent_seq_end
                <= target as nat);
            assert(target as nat <= frozen.seq_end as nat);
            assert(self.persistent_journal_seq_end <= frozen.seq_end);
            self.journal.view_snapshot_ensures();
            assert(self.branch.control.metadata.seq_end as nat
                == self.journal@.snapshot.boundary_lsn);
            assert(self.journal@.snapshot.boundary_lsn
                == self.journal.snapshot.boundary_lsn as nat);
            self.journal.view_seq_start_ensures();
            assert(self.journal@.snapshot.boundary_lsn
                == self.journal.seq_start());
            assert(frozen.seq_start() as nat
                == self.journal.seq_start());
            assert(frozen.snapshot.boundary_lsn
                == frozen.seq_start());
            assert(self.branch.control.metadata.seq_end as nat
                == frozen.snapshot.boundary_lsn as nat);
            assert(self.branch.control.metadata.seq_end
                == frozen.snapshot.boundary_lsn);
            self.ready_journal_owned_aus_exclude_superblock();
        }
        let ghost pre_state = self.model@.value();
        let ghost pre_cache = self.cache@;
        match self.journal.prepare_freeze_reads(
            &frozen,
            &mut self.cache,
        ) {
            PrepareFreezeReadsResult::NeedCacheLoad {
                addr,
                slot_handle,
            } => {
                proof {
                    assert(addr@.au != spec_superblock_addr().au);
                    assert(addr@ != spec_superblock_addr());
                    assert(self.state().outstanding_cache_reqs
                        == Map::<ID, Address>::empty()) by {
                        assert_maps_equal!(
                            self.state().outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if self.state().outstanding_cache_reqs
                                    .contains_key(id)
                                {
                                    assert(self.outstanding_requests@
                                        .contains_key(id));
                                    assert(false);
                                }
                            }
                        );
                    }
                    assert(self.phase_alignment());
                    assert(self.sync_wf());
                    assert(self.common_inv());
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_read_io(
                    addr,
                    slot_handle,
                    CacheReadPurpose::SyncJournalRoot,
                    api,
                )
            },
            PrepareFreezeReadsResult::CacheFull => {
                api.log("unified-cache Betree sync waits for cache space");
                proof { assert(self.inv_api(api)); }
                false
            },
            PrepareFreezeReadsResult::Blocked => {
                api.log("unified-cache Betree sync root read blocked");
                proof { assert(self.inv_api(api)); }
                false
            },
            PrepareFreezeReadsResult::InvalidRecord => {
                api.log("unified-cache Betree sync root is invalid");
                proof { assert(self.inv_api(api)); }
                false
            },
            PrepareFreezeReadsResult::Ready { reads } => {
                let image = ISuperblock {
                    geometry: ISuperblockGeometry {
                        pages_per_au: self.disk_page_count,
                        formatted_au_count: self.disk_au_count,
                    },
                    payload: ISuperblockPayload {
                        journal: ISuperblockJournalImage {
                            snapshot: frozen.snapshot,
                            seq_end: frozen.seq_end,
                        },
                        branch: self.branch.control.metadata.root,
                    },
                };
                let layout = DiskLayout::new();
                if !layout.can_marshall(&image) {
                    proof {
                        assert(self.cache@ == pre_cache);
                        assert(self.inv_api(api));
                    }
                    return false;
                }

                let ghost abstract_image = image@@;
                let ghost journal_lbl = AtomicJournalState::Label::CommitStart {
                    snapshot: abstract_image.journal_snapshot,
                    seq_end: abstract_image.journal_seq_end,
                    reads: to_journal_records(reads@),
                };
                let ghost new_journal = AtomicJournalState::State {
                    in_flight: Some(AtomicJournalImage {
                        snapshot: abstract_image.journal_snapshot,
                        seq_end: abstract_image.journal_seq_end,
                    }),
                    ..pre_state.state.journal
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        journal: new_journal,
                        sync_phase: AtomicBetreeSyncPhase::Preparing {
                            image: abstract_image,
                            journal_ready: false,
                            branch_ready: true,
                        },
                        ..pre_state.state
                    },
                };
                let ghost disk_request_tuples = Multiset::empty();
                let ghost disk_response_tuples = Multiset::empty();
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    assert(pre_state.state.branch == self.branch@);
                    assert(pre_state.state.journal.persistent_seq_end
                        == self.persistent_journal_seq_end as nat);
                    assert(pre_state.state.journal.in_flight is None);
                    self.journal.clean_watermark_le_marshaled_seq_end();
                    self.journal.marshalled_seq_end_le_seq_end();
                    self.journal.view_seq_end_ensures();
                    assert(frozen.seq_end as nat
                        == self.journal.clean_watermark());
                    assert(frozen.seq_end as nat
                        <= self.journal.seq_end());
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(image@.geometry.wf()) by {
                        assert(image@.geometry.pages_per_au == page_count());
                    }
                    assert(image@.payload.wf()) by {
                        assert(frozen.wf());
                        assert(self.branch.control.metadata.wf());
                    }
                    assert(image@.addresses_bounded()) by {
                        assert(frozen.geometry_bounded(self.disk_au_count));
                        if self.branch.control.metadata.root is Some {
                            assert(self.branch.control.metadata.root.unwrap()@.au
                                < self.disk_au_count as nat);
                        }
                    }
                    assert(image@.wf());
                    assert(abstract_image.wf());
                    assert(UnifiedCacheBetreeSystem::State::
                        journal_sync_image_metadata_valid(
                            pre_state.state,
                            abstract_image,
                        )) by {

                        assert(crate::implementation::
                            UnifiedCacheBetreeSystem_v::
                            betree_metadata_from_superblock(abstract_image)
                            == self.branch.control.metadata@);
                        assert(pre_state.state.branch.control.metadata
                            == self.branch.control.metadata@);
                        assert(pre_state.state.journal.persistent_seq_end
                            == self.persistent_journal_seq_end as nat);
                        assert(frozen.seq_end as nat
                            <= self.journal.seq_end());
                    }
                    assert(AtomicJournalState::State::commit_start(
                        pre_state.state.journal,
                        new_journal,
                        journal_lbl,
                    )) by {

                    }
                    assert(AtomicJournalState::State::next_by(
                        pre_state.state.journal,
                        new_journal,
                        journal_lbl,
                        AtomicJournalState::Step::commit_start(),
                    )) by {
                        reveal(AtomicJournalState::State::next_by);
                    }
                    assert(AtomicJournalState::State::next(
                        pre_state.state.journal,
                        new_journal,
                        journal_lbl,
                    )) by {
                        reveal(AtomicJournalState::State::next);
                    }
                    assert(UnifiedCacheBetreeSystem::State::
                        execute_journal_sync_begin(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Disk,
                            abstract_image,
                            reads@,
                            self.cache@,
                            new_journal,
                            disk_request_tuples,
                            disk_response_tuples,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Disk,
                        UnifiedCacheBetreeSystem::Step::
                            execute_journal_sync_begin(
                                abstract_image,
                                reads@,
                                self.cache@,
                                new_journal,
                                disk_request_tuples,
                                disk_response_tuples,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    let info = ProgramDiskInfo {
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheBetreeProgramModel::
                        disk_step_matches_info(
                            pre_state.state,
                            UnifiedCacheBetreeSystem::Step::
                                execute_journal_sync_begin(
                                    abstract_image,
                                    reads@,
                                    self.cache@,
                                    new_journal,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                            info,
                        ));
                    UnifiedCacheBetreeProgramModel::lift_disk_step(
                        pre_state,
                        post_state,
                        info,
                    );
                }
                let tracked empty_responses =
                    DiskRespShard::empty(self.instance_id());
                let tracked _empty_requests = self.instance.borrow()
                    .disk_transitions(
                        KVStoreTokenized::Label::DiskOp {
                            disk_request_tuples,
                            disk_response_tuples,
                        },
                        post_state,
                        &mut model,
                        empty_responses,
                    );
                self.model = Tracked(model);
                self.sync_phase = BetreeSyncPhaseImpl::Preparing {
                    image,
                    journal_ready: false,
                    branch_ready: true,
                };
                proof {
                    assert(self.sync_wf());
                    assert(self.phase_alignment());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree journal sync frozen");
                true
            },
        }
    }

    fn record_store_sync_begin(
        &mut self,
        seq_end: u64,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is None,
            old(self).store_flush_phase == (StoreFlushPhaseImpl::Ready {
                seq_end,
            }),
            old(self).journal.marshalled_seq_end() == seq_end as nat,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress ==> self.sync_phase is Preparing,
            !progress ==> self.sync_phase == old(self).sync_phase,
    {
        if !self.branch.ownership.all_owned_aus_bounded(
            self.disk_au_count,
        ) {
            proof { assert(self.inv_api(api)); }
            return false;
        }
        proof {
            self.ready_journal_sync_metadata_facts();
            self.ready_query_cache_certificate();
            assert(self.store_flush_wf());
            assert(self.branch.memtable@.is_empty());
            assert(self.branch.memtable.seq_end == seq_end);
            self.journal.view_seq_end_ensures();
            assert(self.journal.seq_end() == seq_end as nat);
        }
        let frozen = self.journal.freeze_empty_for_store_commit(seq_end);
        let image = ISuperblock {
            geometry: ISuperblockGeometry {
                pages_per_au: self.disk_page_count,
                formatted_au_count: self.disk_au_count,
            },
            payload: ISuperblockPayload {
                journal: ISuperblockJournalImage {
                    snapshot: frozen.snapshot,
                    seq_end: frozen.seq_end,
                },
                branch: self.branch.root,
            },
        };
        let layout = DiskLayout::new();
        if !layout.can_marshall(&image) {
            proof { assert(self.inv_api(api)); }
            return false;
        }

        let ghost pre_state = self.model@.value();
        let ghost pre_branch = self.branch@;
        match self.branch.commit_start() {
            BranchBetreeCommitResult::Noop => {
                proof { assert(self.inv_api(api)); }
                false
            },
            BranchBetreeCommitResult::Applied => {
                let ghost abstract_image = image@@;
                let ghost empty = Map::<Address, RawPage>::empty();
                let ghost journal_lbl = AtomicJournalState::Label::CommitStart {
                    snapshot: abstract_image.journal_snapshot,
                    seq_end: abstract_image.journal_seq_end,
                    reads: to_journal_records(empty),
                };
                let ghost new_journal = AtomicJournalState::State {
                    in_flight: Some(AtomicJournalImage {
                        snapshot: abstract_image.journal_snapshot,
                        seq_end: abstract_image.journal_seq_end,
                    }),
                    ..pre_state.state.journal
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        journal: new_journal,
                        branch: self.branch@,
                        sync_phase: AtomicBetreeSyncPhase::Preparing {
                            image: abstract_image,
                            journal_ready: false,
                            branch_ready: false,
                        },
                        ..pre_state.state
                    },
                };
                let ghost disk_request_tuples = Multiset::empty();
                let ghost disk_response_tuples = Multiset::empty();
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    assert(image@.geometry.wf()) by {
                        assert(image@.geometry.pages_per_au == page_count());
                    }
                    assert(image@.payload.wf()) by {
                        assert(frozen.wf());
                    }
                    assert(image@.addresses_bounded()) by {
                        assert(image@.payload.branch
                            == iopt_addr(old(self).branch.root));
                        if image@.payload.branch is Some {
                            assert(old(self).branch.root is Some);
                            assert(image@.payload.branch.unwrap().au
                                == old(self).branch.root.unwrap()@.au);
                            assert(old(self).branch.ownership.betree
                                .active_aus().contains(
                                    old(self).branch.root.unwrap()@.au,
                                ));
                            assert(old(self).branch.ownership.betree.all_aus()
                                .contains(old(self).branch.root.unwrap()@.au));
                            assert((old(self).branch.ownership.betree.all_aus()
                                + old(self).branch.ownership.branches
                                    .all_summary_aus()).contains(
                                        old(self).branch.root.unwrap()@.au,
                                    ));
                            assert(old(self).branch_owned_aus_bounded());
                            assert(old(self).branch.root.unwrap()@.au
                                < self.disk_au_count as nat);
                            assert(image@.geometry.formatted_au_count
                                == self.disk_au_count as nat);
                            assert(image@.payload.branch.unwrap().au
                                < image@.geometry.formatted_au_count);
                        }
                    }
                    assert(image@.wf());
                    assert(abstract_image.wf());
                    assert(UnifiedCacheBetreeSystem::State::
                        store_sync_image_metadata_valid(
                            pre_state.state,
                            abstract_image,
                        )) by {

                        assert(crate::implementation::
                            UnifiedCacheBetreeSystem_v::
                            betree_metadata_from_superblock(abstract_image)
                            == crate::implementation::
                                CrashAwareCachingDiskBranchBetree_v::
                                CachingDiskBranchBetreeMetadata {
                                    root: pre_state.state.branch.betree.root,
                                    seq_end: pre_state.state.branch.betree
                                        .memtable.seq_end,
                                });
                    }
                    assert(AtomicJournalState::State::commit_start(
                        pre_state.state.journal,
                        new_journal,
                        journal_lbl,
                    )) by {

                        assert(pre_state.state.journal.journal
                            == self.journal@);
                        assert(pre_state.state.journal.persistent_seq_end
                            <= abstract_image.journal_seq_end);

                        assert(to_journal_records(empty)
                            == Map::<Address, crate::journal::LinkedJournal_v::
                                JournalRecord>::empty());
                        assert(abstract_image.journal_snapshot
                            == frozen.snapshot@);
                        assert(CachedJournal::State::next(
                            self.journal@,
                            self.journal@,
                            CachedJournal::Label::FreezeForCommit {
                                frozen: frozen.snapshot@,
                                reads: Map::empty(),
                            },
                        ));
                        assert(CachedJournal::State::next(
                            pre_state.state.journal.journal,
                            pre_state.state.journal.journal,
                            CachedJournal::Label::FreezeForCommit {
                                frozen: abstract_image.journal_snapshot,
                                reads: Map::empty(),
                            },
                        ));
                    }
                    assert(AtomicJournalState::State::next(
                        pre_state.state.journal,
                        new_journal,
                        journal_lbl,
                    )) by {
                        reveal(AtomicJournalState::State::next);
                        assert(AtomicJournalState::State::next_by(
                            pre_state.state.journal,
                            new_journal,
                            journal_lbl,
                            AtomicJournalState::Step::commit_start(),
                        )) by {
                            reveal(AtomicJournalState::State::next_by);
                        }
                        reveal(AtomicJournalState::State::next_by);
                    }
                    Cache::State::access_empty_is_noop(pre_state.state.cache);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        pre_state.state.cache,
                        Cache::Label::Access {
                            reads: empty,
                            writes: empty,
                        },
                    ));
                    assert(AtomicBranchBetreeState::State::next(
                        pre_branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::CommitStart {
                            image: crate::implementation::
                                CachedBranchBetree_v::FrozenBranchBetree {
                                    root: pre_branch.betree.root,
                                    seq_end: pre_branch.betree.memtable.seq_end,
                            },
                        },
                    ));
                    assert(UnifiedCacheBetreeSystem::State::
                        execute_store_sync_begin(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Disk,
                            abstract_image,
                            empty,
                            pre_state.state.cache,
                            new_journal,
                            disk_request_tuples,
                            disk_response_tuples,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Disk,
                        UnifiedCacheBetreeSystem::Step::
                            execute_store_sync_begin(
                                abstract_image,
                                empty,
                                pre_state.state.cache,
                                new_journal,
                                disk_request_tuples,
                                disk_response_tuples,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    let info = ProgramDiskInfo {
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheBetreeProgramModel::
                        disk_step_matches_info(
                            pre_state.state,
                            UnifiedCacheBetreeSystem::Step::
                                execute_store_sync_begin(
                                    abstract_image,
                                    empty,
                                    pre_state.state.cache,
                                    new_journal,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                            info,
                        ));
                    UnifiedCacheBetreeProgramModel::lift_disk_step(
                        pre_state,
                        post_state,
                        info,
                    );
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }
                let tracked empty_responses =
                    DiskRespShard::empty(self.instance_id());
                let tracked _empty_requests = self.instance.borrow()
                    .disk_transitions(
                        KVStoreTokenized::Label::DiskOp {
                            disk_request_tuples,
                            disk_response_tuples,
                        },
                        post_state,
                        &mut model,
                        empty_responses,
                    );
                self.model = Tracked(model);
                self.sync_phase = BetreeSyncPhaseImpl::Preparing {
                    image,
                    journal_ready: false,
                    branch_ready: false,
                };
                self.store_flush_phase = StoreFlushPhaseImpl::None;
                proof {
                    self.journal.seq_start_le_marshalled_end();
                    assert(self.sync_wf());
                    assert(self.store_flush_wf());
                    assert(self.phase_alignment());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree store sync frozen");
                true
            },
        }
    }

    fn record_sync_journal_prepare(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is Preparing,
            !old(self).sync_phase->journal_ready,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress ==> self.sync_phase is Preparing,
            progress ==> self.sync_phase->journal_ready,
            !progress ==> self.sync_phase == old(self).sync_phase,
    {
        let (has_root, image_seq_end, concrete_branch_ready) =
            match &self.sync_phase {
            BetreeSyncPhaseImpl::Preparing {
                image,
                branch_ready,
                ..
            } => (
                image.payload.journal.snapshot.freshest_rec.is_some(),
                image.payload.journal.seq_end,
                *branch_ready,
            ),
            _ => unreached(),
        };
        let clean = self.journal.exec_clean_watermark();
        if has_root && image_seq_end > clean {
            api.log("unified-cache Betree journal sync waits for clean root");
            proof { assert(self.inv_api(api)); }
            return false;
        }

        let ghost pre_state = self.model@.value();
        let ghost abstract_image = match pre_state.state.sync_phase {
            AtomicBetreeSyncPhase::Preparing { image, .. } => image,
            _ => arbitrary(),
        };
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                sync_phase: AtomicBetreeSyncPhase::Preparing {
                    image: abstract_image,
                    journal_ready: true,
                    branch_ready: concrete_branch_ready,
                },
                ..pre_state.state
            },
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            self.journal.view_ensures();
            assert(self.journal.index_ready());
            assert(pre_state.state.journal.journal == self.journal@);
            assert(pre_state.state.journal.journal.status is Some);
            assert(pre_state.state.sync_phase
                == AtomicBetreeSyncPhase::Preparing {
                    image: abstract_image,
                    journal_ready: false,
                    branch_ready: concrete_branch_ready,
                });
            self.journal.view_clean_watermark_ensures();
            assert(AtomicJournalState::State::commit_prepared(
                pre_state.state.journal,
                pre_state.state.journal,
                AtomicJournalState::Label::CommitPrepared,
            )) by {

                if abstract_image.journal_snapshot.freshest_rec() is Some {
                    assert(abstract_image.journal_seq_end
                        == image_seq_end as nat);
                    assert(abstract_image.journal_seq_end
                        <= pre_state.state.journal.journal
                            .clean_watermark());
                }
            }
            assert(AtomicJournalState::State::next_by(
                pre_state.state.journal,
                pre_state.state.journal,
                AtomicJournalState::Label::CommitPrepared,
                AtomicJournalState::Step::commit_prepared(),
            )) by {
                reveal(AtomicJournalState::State::next_by);
            }
            assert(AtomicJournalState::State::next(
                pre_state.state.journal,
                pre_state.state.journal,
                AtomicJournalState::Label::CommitPrepared,
            )) by {
                reveal(AtomicJournalState::State::next);
            }
            assert(UnifiedCacheBetreeSystem::State::
                execute_sync_journal_prepare(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Internal,
                ));
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Internal,
                UnifiedCacheBetreeSystem::Step::
                    execute_sync_journal_prepare(),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            UnifiedCacheBetreeProgramModel::lift_internal_step(
                pre_state,
                post_state,
            );
            tracked_swap(self.model.borrow_mut(), &mut model);
        }
        let tracked _internal_token = self.instance.borrow().internal(
            KVStoreTokenized::Label::InternalOp {},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);
        let mut phase = BetreeSyncPhaseImpl::None;
        core::mem::swap(&mut self.sync_phase, &mut phase);
        self.sync_phase = match phase {
            BetreeSyncPhaseImpl::Preparing {
                image,
                branch_ready,
                ..
            } => {
                BetreeSyncPhaseImpl::Preparing {
                    image,
                    journal_ready: true,
                    branch_ready,
                }
            },
            _ => unreached(),
        };
        proof {
            assert(self.sync_wf());
            assert(self.common_inv());
            assert(self.inv_api(api));
        }
        api.log("unified-cache Betree journal sync prepared");
        true
    }

    fn record_sync_branch_prepare(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is Preparing,
            !old(self).sync_phase->branch_ready,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress ==> self.sync_phase is Preparing,
            !progress ==> self.sync_phase == old(self).sync_phase,
    {
        proof {
            assert(self.sync_wf());
            assert(self.branch.control.frozen_metadata is Some);
            assert(self.branch.ownership.frozen_aus()
                == self.branch.ownership.current_durable_aus());
            self.frozen_branch_aus_exclude_superblock();
        }
        let frozen_aus = self.branch.frozen_aus_vec();
        match self.cache.begin_writeback_for_aus(&frozen_aus) {
            AuSetWritebackResult::Busy => {
                proof { assert(self.inv_api(api)); }
                false
            },
            AuSetWritebackResult::Acquired { addr, handle } => {
                proof {
                    assert(iau_vec_set(frozen_aus@).contains(addr@.au));
                    assert(addr@.au != spec_superblock_addr().au);
                    assert(addr@ != spec_superblock_addr());
                    assert(self.common_inv());
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.state().outstanding_cache_reqs
                        == Map::<ID, Address>::empty()) by {
                        assert_maps_equal!(
                            self.state().outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if self.state().outstanding_cache_reqs
                                    .contains_key(id)
                                {
                                    assert(self.outstanding_requests@
                                        .contains_key(id));
                                }
                            }
                        );
                    }
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_write_io(
                    addr,
                    handle,
                    api,
                )
            },
            AuSetWritebackResult::Complete => {
                let (concrete_image, journal_ready) = match &self.sync_phase {
                    BetreeSyncPhaseImpl::Preparing {
                        image,
                        journal_ready,
                        ..
                    } => (image, *journal_ready),
                    _ => unreached(),
                };
                let ghost pre_state = self.model@.value();
                let ghost abstract_image = match pre_state.state.sync_phase {
                    AtomicBetreeSyncPhase::Preparing { image, .. } => image,
                    _ => arbitrary(),
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        sync_phase: AtomicBetreeSyncPhase::Preparing {
                            image: abstract_image,
                            journal_ready,
                            branch_ready: true,
                        },
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    assert(pre_state.state.sync_phase
                        == AtomicBetreeSyncPhase::Preparing {
                            image: abstract_image,
                            journal_ready,
                            branch_ready: false,
                        });
                    assert(pre_state.state.branch == self.branch@);
                    assert(pre_state.state.branch.control.frozen is Some);
                    assert(pre_state.state.branch.control.frozen.unwrap().aus
                        == iau_vec_set(frozen_aus@));
                    self.branch.commit_prepared_step();
                    assert(AtomicBranchBetreeState::State::next(
                        pre_state.state.branch,
                        pre_state.state.branch,
                        AtomicBranchBetreeState::Label::CommitPrepared,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::
                        execute_sync_branch_prepare(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            self.cache@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            execute_sync_branch_prepare(self.cache@),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                let mut phase = BetreeSyncPhaseImpl::None;
                core::mem::swap(&mut self.sync_phase, &mut phase);
                self.sync_phase = match phase {
                    BetreeSyncPhaseImpl::Preparing { image, .. } => {
                        BetreeSyncPhaseImpl::Preparing {
                            image,
                            journal_ready,
                            branch_ready: true,
                        }
                    },
                    _ => unreached(),
                };
                proof {
                    assert(concrete_image@@ == abstract_image);
                    assert(self.sync_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree branch sync prepared");
                true
            },
        }
    }

    fn issue_sync_superblock_write(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is Preparing,
            old(self).sync_phase->journal_ready,
            old(self).sync_phase->branch_ready,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress ==> self.sync_phase is SuperblockWriteIssued,
            !progress ==> self.sync_phase == old(self).sync_phase,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_sync = self.sync_requests;
        let mut phase = BetreeSyncPhaseImpl::None;
        core::mem::swap(&mut self.sync_phase, &mut phase);
        let image = match phase {
            BetreeSyncPhaseImpl::Preparing {
                image,
                journal_ready: true,
                branch_ready: true,
            } => image,
            _ => unreached(),
        };
        let layout = DiskLayout::new();
        if !layout.can_marshall(&image) {
            self.sync_phase = BetreeSyncPhaseImpl::Preparing {
                image,
                journal_ready: true,
                branch_ready: true,
            };
            proof { assert(self.inv_api(api)); }
            return false;
        }
        let raw_page = layout.marshall(&image);
        let req_id_perm = Tracked(api.send_disk_request_predict_id());
        let disk_req = IDiskRequest::WriteReq {
            to: superblock_addr(),
            data: raw_page,
        };
        let ghost abstract_image = image@@;
        let ghost disk_request_tuples =
            multiset_map_singleton(req_id_perm@, disk_req@);
        let ghost disk_response_tuples = Multiset::empty();
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                sync_phase: AtomicBetreeSyncPhase::SuperblockWriteIssued {
                    req_id: req_id_perm@,
                    image: abstract_image,
                },
                ..pre_state.state
            },
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
            assert(pre_state.state.sync_phase
                == AtomicBetreeSyncPhase::Preparing {
                    image: abstract_image,
                    journal_ready: true,
                    branch_ready: true,
                });
            assert(superblock_matches(disk_req@->data, abstract_image));
            multiset_map_singleton_ensures(req_id_perm@, disk_req@);
            assert(disk_request_tuples
                == Multiset::singleton((req_id_perm@, disk_req@))) by {
                assert(disk_request_tuples
                    == Multiset::empty().insert((
                        req_id_perm@,
                        disk_req@,
                    )));
            }
            assert(UnifiedCacheBetreeSystem::State::
                execute_sync_superblock_write(
                    pre_state.state,
                    post_state.state,
                    UnifiedCacheBetreeSystem::Label::Disk,
                    req_id_perm@,
                    disk_req@,
                    disk_request_tuples,
                    disk_response_tuples,
                ));
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                UnifiedCacheBetreeSystem::Step::
                    execute_sync_superblock_write(
                        req_id_perm@,
                        disk_req@,
                        disk_request_tuples,
                        disk_response_tuples,
                    ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            let info = ProgramDiskInfo {
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheBetreeProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheBetreeSystem::Step::
                    execute_sync_superblock_write(
                        req_id_perm@,
                        disk_req@,
                        disk_request_tuples,
                        disk_response_tuples,
                    ),
                info,
            ));
            UnifiedCacheBetreeProgramModel::lift_disk_step(
                pre_state,
                post_state,
                info,
            );
        }
        let tracked empty_responses =
            DiskRespShard::empty(self.instance_id());
        let tracked request_token = self.instance.borrow().disk_transitions(
            KVStoreTokenized::Label::DiskOp {
                disk_request_tuples,
                disk_response_tuples,
            },
            post_state,
            &mut model,
            empty_responses,
        );
        self.model = Tracked(model);
        let id = api.send_disk_request(
            disk_req,
            req_id_perm,
            Tracked(request_token),
        );
        self.sync_requests.move_cleaning_to_superblocking();
        self.outstanding_requests.insert(
            id,
            OutstandingReqInfo::SuperblockWrite,
        );
        self.sync_phase = BetreeSyncPhaseImpl::SuperblockWriteIssued {
            image,
            req_id: id,
        };
        proof {
            assert(id == req_id_perm@);
            assert(self.sync_requests.all_ids() == pre_sync.all_ids());
            assert(self.outstanding_requests@.dom() =~= set![id]);
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
            assert(self.sync_wf()) by {
                assert forall |i: int|
                    0 <= i < self.sync_requests.superblocking_reqs@.len()
                    implies #[trigger] self.state().sync_req_map[
                        self.sync_requests.superblocking_reqs@[i]
                    ] <= abstract_image.journal_seq_end by {
                    assert(self.sync_requests.superblocking_reqs@[i]
                        == pre_sync.journal_cleaning_reqs@[i]);
                    assert(pre_state.state.sync_req_map[
                        pre_sync.journal_cleaning_reqs@[i]
                    ] <= pre_sync.sync_target_lsn as nat);
                    assert(pre_sync.sync_target_lsn as nat
                        <= abstract_image.journal_seq_end);
                }
            }
            assert(self.common_inv());
            assert(self.inv_api(api));
        }
        api.log("unified-cache Betree superblock write issued");
        true
    }

    fn record_journal_refill_for_ready(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is None,
            old(self).store_flush_phase is None,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.sync_phase == old(self).sync_phase,
            self.store_flush_phase == old(self).store_flush_phase,
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        proof {
            self.ready_branch_allocation_certificate();
            old(self).journal.view_ensures();
            assert(old(self).phase_alignment());
            assert(old(self).journal.wf());
            assert(old(self).journal.index_ready());
            assert(old(self).journal.ready_wf(old(self).disk_au_count));
        }
        match self.journal.background_refill_aus(
            &mut self.au_pool,
            self.disk_au_count,
        ) {
            None => {
                proof {
                    self.journal.same_view_preserves_ready_wf(old(self).journal);
                    assert(self.au_pool@ =~= old(self).au_pool@);
                    assert(self.journal.allocator_index_aligned()) by {
                        assert(self.journal@ == old(self).journal@);
                        assert(self.journal.journal_alloc.i()
                            == old(self).journal.journal_alloc.i());
                    }
                    assert(self.sync_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                false
            },
            Some(allocation) => {
                let ghost aus = allocation.as_set();
                let ghost new_journal = AtomicJournalState::State {
                    mini_allocator: self.journal.journal_alloc.i(),
                    ..pre_state.state.journal
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        free_aus: self.au_pool@,
                        journal: new_journal,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    self.journal.same_view_preserves_ready_wf(old(self).journal);
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(pre_state.state.recovery_state is RecoveryComplete);
                    assert(pre_state.state.journal.ready()) by {
                        assert(old(self).journal.index_ready());
                        assert(old(self).journal@.status is Some);
                    }
                    assert(pre_state.state.branch.control.metadata_loaded);
                    assert(pre_state.state.allocation_metadata_loaded());
                    assert(aus <= pre_state.state.free_aus) by {
                        assert(aus <= pre_pool);
                    }
                    assert(new_journal.mini_allocator
                        == pre_state.state.journal.mini_allocator.add_aus(aus));
                    assert(new_journal.journal
                        == pre_state.state.journal.journal);
                    assert(AtomicJournalState::State::fill_aus(
                        pre_state.state.journal,
                        new_journal,
                        AtomicJournalState::Label::FillAUs { aus },
                    )) by {

                    }
                    assert(AtomicJournalState::State::next_by(
                        pre_state.state.journal,
                        new_journal,
                        AtomicJournalState::Label::FillAUs { aus },
                        AtomicJournalState::Step::fill_aus(),
                    )) by {
                        reveal(AtomicJournalState::State::next_by);
                    }
                    assert(AtomicJournalState::State::next(
                        pre_state.state.journal,
                        new_journal,
                        AtomicJournalState::Label::FillAUs { aus },
                    )) by {
                        reveal(AtomicJournalState::State::next);
                    }
                    assert(UnifiedCacheBetreeSystem::State::journal_fill_aus(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        aus,
                        new_journal,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::journal_fill_aus(
                            aus,
                            new_journal,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    old(self).journal.journal_alloc.all_aus_match();
                    self.journal.journal_alloc.all_aus_match();
                    assert(self.journal.owned_aus()
                        =~= old(self).journal.owned_aus() + aus) by {
                        assert(self.journal.journal_alloc.i().all_aus()
                            =~= old(self).journal.journal_alloc.i()
                                .all_aus() + aus);
                    }
                    match self.compaction_work {
                        Some(work) if work.output_idx == Some(0usize) => {
                            let ghost wip_aus = self.branch.wip_branches@[0]
                                .mini_allocator.i().all_aus();
                            assert(wip_aus <= old(self).branch.betree_i()
                                .owned_aus());
                            assert(pre_pool.disjoint(wip_aus));
                            assert(aus.disjoint(wip_aus));
                            assert(wip_aus.disjoint(
                                self.journal.owned_aus(),
                            ));
                        },
                        _ => {},
                    }
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i());
                    assert(self.state().free_aus =~= self.au_pool@);
                    assert(self.journal.allocator_index_aligned()) by {
                        assert(old(self).journal.allocator_index_aligned());
                        assert(self.journal@ == old(self).journal@);
                        assert(self.journal.journal_alloc.i().allocated_aus()
                            == old(self).journal.journal_alloc.i().allocated_aus());
                    }
                    assert(self.sync_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree journal AU refill");
                true
            },
        }
    }

    fn record_journal_marshall_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is None,
            old(self).store_flush_phase is None
                || old(self).store_flush_phase is Ready,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.sync_phase == old(self).sync_phase,
            self.store_flush_phase == old(self).store_flush_phase,
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost pre_state = self.model@.value();
        proof {
            self.ready_journal_cache_certificate();
            self.ready_branch_allocation_certificate();
            old(self).journal.view_ensures();
            assert(old(self).journal.ready_wf(old(self).disk_au_count));
        }
        let seq_end = self.journal.exec_seq_end();
        let marshalled = self.journal.exec_marshaled_seq_end();
        if seq_end == marshalled {
            proof { assert(self.inv_api(api)); }
            return false;
        }

        match self.journal.internal_journal_marshall_reserve_slot(
            &mut self.cache,
            self.disk_au_count,
            self.disk_page_count,
        ) {
            MarshalReserveResult::CacheFull {} => {
                proof {
                    self.journal.wf_implies_basic_wf();
                    self.journal.same_view_preserves_ready_wf(old(self).journal);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i());
                    assert(self.phase_alignment());
                    assert(self.sync_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree journal marshalling cache full");
                false
            },
            MarshalReserveResult::Reserved { addr, slot_handle } => {
                let ghost reserved_cache = self.cache@;
                let ghost reserve_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: reserved_cache,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        reserve_state.state.cache,
                        Cache::Label::Internal,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::cache_internal(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        reserve_state.state.cache,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::cache_internal(
                            reserve_state.state.cache,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        reserve_state,
                    );
                }
                let tracked _reserve_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    reserve_state,
                    &mut model,
                );
                proof {
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        reserve_state.state.cache,
                        Cache::Label::Internal,
                    );
                    self.journal.view_seq_end_ensures();
                    self.journal.view_marshaled_seq_end_ensures();
                    old(self).journal.view_seq_end_ensures();
                    old(self).journal.view_marshaled_seq_end_ensures();
                    assert(self.journal.seq_end()
                        == old(self).journal.seq_end());
                    assert(self.journal.marshalled_seq_end()
                        == old(self).journal.marshalled_seq_end());
                    assert(self.journal.seq_end()
                        != self.journal.marshalled_seq_end());
                }
                let raw_page = self.journal.internal_journal_marshall_commit_reserved(
                    &mut self.cache,
                    addr,
                    slot_handle,
                );
                let ghost writes = Map::<Address, RawPage>::empty()
                    .insert(addr@, raw_page@);
                let ghost journal_lbl = AtomicJournalState::Label::JournalMarshal {
                    addr: addr@,
                    writes: to_journal_records(writes),
                };
                let ghost new_atomic_journal = AtomicJournalState::State {
                    journal: self.journal@,
                    mini_allocator: self.journal.journal_alloc.i(),
                    ..reserve_state.state.journal
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        journal: new_atomic_journal,
                        ..reserve_state.state
                    },
                };
                proof {
                    assert(reserve_state.state.journal.journal
                        == old(self).journal@);
                    assert(reserve_state.state.journal.mini_allocator
                        == old(self).journal.journal_alloc.i());
                    assert(new_atomic_journal.mini_allocator
                        == reserve_state.state.journal.mini_allocator.allocate(addr@));
                    assert(CachedJournal::State::next(
                        reserve_state.state.journal.journal,
                        new_atomic_journal.journal,
                        CachedJournal::Label::JournalMarshal {
                            writes: to_journal_records(writes),
                        },
                    )) by {
                        assert(journal_marshall_labels(addr@, raw_page@).0
                            == CachedJournal::Label::JournalMarshal {
                                writes: to_journal_records(writes),
                            });
                    }
                    assert(AtomicJournalState::State::internal_access_next(
                        reserve_state.state.journal,
                        new_atomic_journal,
                        journal_lbl,
                        Map::empty(),
                        writes,
                    )) by {

                        assert(AtomicJournalState::State::journal_marshal(
                            reserve_state.state.journal,
                            new_atomic_journal,
                            journal_lbl,
                            new_atomic_journal.journal,
                        )) by {

                        }
                    }
                    assert(Cache::State::next(
                        reserve_state.state.cache,
                        post_state.state.cache,
                        Cache::Label::Access {
                            reads: Map::empty(),
                            writes,
                        },
                    )) by {
                        assert(journal_marshall_labels(addr@, raw_page@).1
                            == Cache::Label::Access {
                                reads: Map::empty(),
                                writes,
                            });
                    }
                    assert(UnifiedCacheBetreeSystem::State::journal_internal_access(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        journal_lbl,
                        Map::empty(),
                        writes,
                        post_state.state.cache,
                        new_atomic_journal,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::journal_internal_access(
                            journal_lbl,
                            Map::empty(),
                            writes,
                            post_state.state.cache,
                            new_atomic_journal,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        reserve_state,
                        post_state,
                    );
                }
                let tracked _marshall_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    assert forall |read_addr: Address, data: RawPage|
                        pre_state.state.cache.valid_read(read_addr, data)
                        implies self.cache@.valid_read(read_addr, data) by {
                        assert(reserved_cache.valid_read(read_addr, data));
                        assert(read_addr != addr@) by {
                            if read_addr == addr@ {
                                FracCacheImpl::entry_fetched_from_view(
                                    &old(self).cache,
                                    &addr,
                                );
                                assert(old(self).cache.entry_fetched(&addr));
                                assert(false);
                            }
                        }
                        assert(!writes.contains_key(read_addr));
                        Cache::State::access_preserves_unwritten_valid_read(
                            reserved_cache,
                            self.cache@,
                            Map::empty(),
                            writes,
                            read_addr,
                            data,
                        );
                    }
                    match self.compaction_work {
                        Some(work) if work.output_idx == Some(0usize) => {
                            old(self).branch.wip_branches@[0]
                                .cache_inv_preserved_by_valid_reads(
                                    pre_state.state.cache,
                                    self.cache@,
                                );
                        },
                        _ => {},
                    }
                    match self.compaction_work {
                        Some(work) if work.phase is Scanning => {
                            old(self).journal.journal_alloc.all_aus_match();
                            old(self).branch
                                .compactor_input_aus_subset_active(0);
                            assert(old(self).journal.owned_aus().contains(
                                addr@.au,
                            ));
                            let ghost source_aus = old(self).branch
                                .compactors@[0].merge->0.source_aus();
                            assert(source_aus <= old(self).branch
                                .ownership.branches.active_summary_aus());
                            assert(source_aus <= old(self).branch
                                .betree_i().owned_aus());
                            assert(writes.dom().disjoint(
                                addresses_in_aus(source_aus),
                            )) by {
                                assert(writes.dom() == set![addr@]);
                            }
                            old(self).branch.compactors@[0].merge->0
                                .cache_inv_preserved_by_unrelated_access(
                                    pre_state.state.cache,
                                    reserved_cache,
                                    self.cache@,
                                    Map::empty(),
                                    writes,
                                );
                        },
                        _ => {},
                    }
                    self.journal.wf_implies_basic_wf();
                    self.journal.view_ensures();
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i());
                    assert(self.journal.index_aus_bounded(
                        self.disk_au_count,
                    )) by {
                        assert forall |au: AU|
                            #[trigger] self.journal@.status.unwrap()
                                .lsn_au_index.values().contains(au)
                            implies au < self.disk_au_count as nat by {
                            if old(self).journal@.status.unwrap()
                                .lsn_au_index.values().contains(au)
                            {
                                assert(old(self).journal.index_aus_bounded(
                                    old(self).disk_au_count,
                                ));
                            } else {
                                assert(au == addr@.au);
                                assert(old(self).journal.journal_alloc.i()
                                    .can_allocate(addr@));
                                assert(old(self).journal.journal_alloc
                                    .bounded(old(self).disk_au_count));
                                old(self).journal.journal_alloc
                                    .allocated_aus_bounded(old(self).disk_au_count);
                            }
                        }
                    }
                    old(self).journal.journal_alloc.i()
                        .allocate_allocated_aus(addr@);
                    assert(self.journal.allocator_index_aligned());
                    self.journal.view_seq_end_ensures();
                    old(self).journal.view_seq_end_ensures();
                    assert(self.state().journal.journal.seq_end()
                        == old(self).state().journal.journal.seq_end());
                    assert(self.state().branch
                        == old(self).state().branch);
                    assert(self.phase_alignment());
                    assert(self.sync_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree journal marshalling");
                true
            },
        }
    }

    fn record_journal_writeback_for_target(
        &mut self,
        target: u64,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is None,
            old(self).store_flush_phase is None,
            target as nat <= old(self).journal.marshalled_seq_end(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.sync_phase == old(self).sync_phase,
            self.store_flush_phase == old(self).store_flush_phase,
            !progress ==> self.outstanding_requests@
                == old(self).outstanding_requests@,
    {
        proof {
            self.ready_journal_owned_aus_exclude_superblock();
        }
        let old_clean = self.journal.exec_clean_watermark();
        match self.journal.begin_writeback_for_target(
            &mut self.cache,
            target,
        ) {
            BeginWritebackForTargetResult::Complete { flushed_domain } => {
                let new_clean = self.journal.exec_clean_watermark();
                if new_clean == old_clean {
                    proof {
                        self.journal.view_ensures();
                        self.journal.wf_implies_basic_wf();
                        assert(self.state().journal.journal == self.journal@);
                        assert(self.phase_alignment());
                        assert(self.common_inv());
                        assert(self.inv_api(api));
                    }
                    return false;
                }
                let ghost pre_state = self.model@.value();
                let ghost aus = to_aus(flushed_domain@);
                let ghost new_atomic_journal = AtomicJournalState::State {
                    journal: self.journal@,
                    ..pre_state.state.journal
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        journal: new_atomic_journal,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(old_clean < new_clean);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        pre_state.state.cache,
                        Cache::Label::EvictableCheck { aus },
                    ));
                    assert(CachedJournal::State::next(
                        pre_state.state.journal.journal,
                        self.journal@,
                        CachedJournal::Label::ObserveCleanAUs { aus },
                    ));
                    assert(AtomicJournalState::State::observe_clean_aus(
                        pre_state.state.journal,
                        new_atomic_journal,
                        AtomicJournalState::Label::ObserveCleanAUs { aus },
                        self.journal@,
                    )) by {

                    }
                    assert(AtomicJournalState::State::next_by(
                        pre_state.state.journal,
                        new_atomic_journal,
                        AtomicJournalState::Label::ObserveCleanAUs { aus },
                        AtomicJournalState::Step::observe_clean_aus(
                            self.journal@,
                        ),
                    )) by {
                        reveal(AtomicJournalState::State::next_by);
                    }
                    assert(AtomicJournalState::State::next(
                        pre_state.state.journal,
                        new_atomic_journal,
                        AtomicJournalState::Label::ObserveCleanAUs { aus },
                    )) by {
                        reveal(AtomicJournalState::State::next);
                    }
                    assert(UnifiedCacheBetreeSystem::State::
                        observe_clean_journal_aus(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            aus,
                            pre_state.state.cache,
                            new_atomic_journal,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            observe_clean_journal_aus(
                                aus,
                                pre_state.state.cache,
                                new_atomic_journal,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    JournalImpl::writeback_preserves_ready_wf(
                        &old(self).journal,
                        &self.journal,
                        self.disk_au_count,
                    );
                    self.journal.wf_implies_basic_wf();
                    assert(self.state().journal.journal == self.journal@);
                    self.journal.view_seq_end_ensures();
                    old(self).journal.view_seq_end_ensures();
                    assert(self.state().journal.journal.seq_end()
                        == old(self).state().journal.journal.seq_end());
                    assert(self.phase_alignment());
                    assert(self.sync_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree journal clean watermark advanced");
                true
            },
            BeginWritebackForTargetResult::Acquired {
                request,
                flushed_domain,
            } => {
                let new_clean = self.journal.exec_clean_watermark();
                let clean_changed = new_clean != old_clean;
                let write_data = request.handle.rec.clone();
                let addr = request.addr;
                let ghost pre_state = self.model@.value();
                let ghost aus = to_aus(flushed_domain@);
                let ghost clean_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        journal: AtomicJournalState::State {
                            journal: self.journal@,
                            ..pre_state.state.journal
                        },
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    assert(old(self).journal@.status.unwrap()
                        .lsn_au_index.values().contains(addr@.au));
                    assert(addr@.au != spec_superblock_addr().au);
                    assert(addr@ != spec_superblock_addr());
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    if clean_changed {
                        assert(old_clean < new_clean);
                        assert(Cache::State::next(
                            pre_state.state.cache,
                            pre_state.state.cache,
                            Cache::Label::EvictableCheck { aus },
                        ));
                        assert(CachedJournal::State::next(
                            pre_state.state.journal.journal,
                            self.journal@,
                            CachedJournal::Label::ObserveCleanAUs { aus },
                        ));
                        assert(AtomicJournalState::State::observe_clean_aus(
                            pre_state.state.journal,
                            clean_state.state.journal,
                            AtomicJournalState::Label::ObserveCleanAUs { aus },
                            self.journal@,
                        )) by {

                        }
                        assert(AtomicJournalState::State::next_by(
                            pre_state.state.journal,
                            clean_state.state.journal,
                            AtomicJournalState::Label::ObserveCleanAUs { aus },
                            AtomicJournalState::Step::observe_clean_aus(
                                self.journal@,
                            ),
                        )) by {
                            reveal(AtomicJournalState::State::next_by);
                        }
                        assert(AtomicJournalState::State::next(
                            pre_state.state.journal,
                            clean_state.state.journal,
                            AtomicJournalState::Label::ObserveCleanAUs { aus },
                        )) by {
                            reveal(AtomicJournalState::State::next);
                        }
                        assert(UnifiedCacheBetreeSystem::State::
                            observe_clean_journal_aus(
                                pre_state.state,
                                clean_state.state,
                                UnifiedCacheBetreeSystem::Label::Internal,
                                aus,
                                pre_state.state.cache,
                                clean_state.state.journal,
                            ));
                        assert(UnifiedCacheBetreeSystem::State::next_by(
                            pre_state.state,
                            clean_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            UnifiedCacheBetreeSystem::Step::
                                observe_clean_journal_aus(
                                    aus,
                                    pre_state.state.cache,
                                    clean_state.state.journal,
                                ),
                        )) by {
                            reveal(UnifiedCacheBetreeSystem::State::next_by);
                        }
                        UnifiedCacheBetreeProgramModel::lift_internal_step(
                            pre_state,
                            clean_state,
                        );
                    }
                }
                if clean_changed {
                    let tracked _internal_token =
                        self.instance.borrow().internal(
                            KVStoreTokenized::Label::InternalOp {},
                            clean_state,
                            &mut model,
                        );
                }

                let req_id_perm = Tracked(api.send_disk_request_predict_id());
                let disk_req = IDiskRequest::WriteReq {
                    to: addr,
                    data: write_data,
                };
                let ghost updated = map![req_id_perm@ => addr@];
                let ghost req_map = map![req_id_perm@ => disk_req@];
                let ghost disk_request_tuples =
                    multiset_map_singleton(req_id_perm@, disk_req@);
                let ghost disk_response_tuples = Multiset::empty();
                let ghost model_before_disk = if clean_changed {
                    clean_state
                } else {
                    pre_state
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        outstanding_cache_reqs: model_before_disk.state
                            .outstanding_cache_reqs
                            .union_prefer_right(updated),
                        ..model_before_disk.state
                    },
                };
                proof {
                    FracCacheImpl::valid_writeback_handle_has_inv(
                        &self.cache,
                        &addr,
                        request.handle,
                    );
                    multiset_map_singleton_ensures(req_id_perm@, disk_req@);
                    assert(multiset_to_map(disk_request_tuples) == req_map);
                    Self::singleton_updated_addr_map(
                        req_id_perm@,
                        disk_req@,
                        addr@,
                    );
                    singleton_map_values(req_id_perm@, disk_req@);
                    assert(!updated.contains_value(spec_superblock_addr()));
                    assert(Cache::State::next(
                        model_before_disk.state.cache,
                        self.cache@,
                        Cache::Label::DiskOps {
                            requests: req_map.values(),
                            responses: Map::empty(),
                        },
                    ));
                    assert(UnifiedCacheBetreeSystem::State::cache_io_begin(
                        model_before_disk.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Disk,
                        req_map,
                        self.cache@,
                        disk_request_tuples,
                        disk_response_tuples,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        model_before_disk.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Disk,
                        UnifiedCacheBetreeSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    let info = ProgramDiskInfo {
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheBetreeProgramModel::
                        disk_step_matches_info(
                            model_before_disk.state,
                            UnifiedCacheBetreeSystem::Step::cache_io_begin(
                                req_map,
                                self.cache@,
                                disk_request_tuples,
                                disk_response_tuples,
                            ),
                            info,
                        ));
                    UnifiedCacheBetreeProgramModel::lift_disk_step(
                        model_before_disk,
                        post_state,
                        info,
                    );
                }
                let tracked empty_disk_responses =
                    DiskRespShard::empty(self.instance_id());
                let tracked new_disk_req_token =
                    self.instance.borrow().disk_transitions(
                        KVStoreTokenized::Label::DiskOp {
                            disk_request_tuples,
                            disk_response_tuples,
                        },
                        post_state,
                        &mut model,
                        empty_disk_responses,
                    );
                self.model = Tracked(model);
                let id = api.send_disk_request(
                    disk_req,
                    req_id_perm,
                    Tracked(new_disk_req_token),
                );
                self.outstanding_requests.insert(
                    id,
                    OutstandingReqInfo::CacheWrite {
                        addr,
                        write_handle: request.handle,
                    },
                );
                proof {
                    assert(req_map.values() == set![DiskRequest::WriteReq {
                        to: addr@,
                        data: request.handle.rec@,
                    }]);
                    assert forall |read_addr: Address, data: RawPage|
                        pre_state.state.cache.valid_read(read_addr, data)
                        implies self.cache@.valid_read(read_addr, data) by {
                        Cache::State::write_request_preserves_valid_read(
                            pre_state.state.cache,
                            self.cache@,
                            addr@,
                            request.handle.rec@,
                            read_addr,
                            data,
                        );
                    }
                    assert forall |read_addr: Address, data: RawPage|
                        self.cache@.valid_read(read_addr, data)
                        implies pre_state.state.cache.valid_read(
                            read_addr,
                            data,
                        ) by {
                        Cache::State::write_request_preserves_valid_read(
                            pre_state.state.cache,
                            self.cache@,
                            addr@,
                            request.handle.rec@,
                            read_addr,
                            data,
                        );
                    }
                    match self.compaction_work {
                        Some(work) if work.output_idx == Some(0usize) => {
                            old(self).branch.wip_branches@[0]
                                .cache_inv_preserved_by_valid_reads(
                                    pre_state.state.cache,
                                    self.cache@,
                                );
                        },
                        _ => {},
                    }
                    match self.compaction_work {
                        Some(work) if work.phase is Scanning => {
                            old(self).branch.compactors@[0].merge->0
                                .cache_inv_preserved_by_backward_valid_reads(
                                    pre_state.state.cache,
                                    self.cache@,
                                );
                        },
                        _ => {},
                    }
                    JournalImpl::writeback_preserves_ready_wf(
                        &old(self).journal,
                        &self.journal,
                        self.disk_au_count,
                    );
                    assert(self.outstanding_requests@.dom() =~= set![id]);
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                    self.journal.wf_implies_basic_wf();
                    self.journal.view_seq_end_ensures();
                    old(self).journal.view_seq_end_ensures();
                    assert(self.state().journal.journal.seq_end()
                        == old(self).state().journal.journal.seq_end());
                    assert(self.phase_alignment());
                    assert(self.sync_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree journal cache writeback");
                true
            },
        }
    }

    fn record_compaction_admit(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_phase is None,
            old(self).store_flush_phase is None,
            old(self).compaction_work is None,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.sync_phase is None,
            self.store_flush_phase is None,
            self.outstanding_requests@ == old(self).outstanding_requests@,
            progress <==> old(self).compaction_candidates.entries@.len() > 0,
    {
        let candidate = match self.compaction_candidates.pop() {
            Some(candidate) => candidate,
            None => {
                proof { assert(self.inv_api(api)); }
                return false;
            },
        };
        self.compaction_work = Some(CompactionWorkItem {
            candidate,
            phase: CompactionWorkPhase::Begin,
            input_idx: None,
            output_idx: None,
        });
        proof {
            assert(candidate.wf());
            assert(self.branch.compactors@.len() == 0);
            assert(self.branch.wip_branches@.len() == 0) by {
                reveal(Implementation::store_flush_wf);
            }
            assert(self.compaction_executor_wf());
            assert(self.common_inv());
            assert(self.inv_api(api));
        }
        api.log("unified-cache Betree admitted compaction candidate");
        true
    }

    fn record_compaction_begin(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is Begin,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
            assert(old(self).branch.compactors@.len() == 0);
            assert(old(self).branch.wip_branches@.len() == 0);
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let root = match self.branch.root {
            Some(root) => root,
            None => {
                self.compaction_work = None;
                proof {
                    assert(self.compaction_executor_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                return true;
            },
        };
        proof {
            self.ready_query_cache_certificate();
            self.ready_journal_cache_certificate();
            assert(self.branch.query_cache_inv(self.cache@));
            assert(cached_betree_query_valid(
                self.cache@,
                root@,
                candidate.route_key,
                candidate.fuel as nat,
                CACHE_SIZE_RECS as nat,
                self.branch.ownership.betree.active_aus(),
                self.branch.ownership.branches.active_summary_map(),
                self.branch.ownership.branches.active_summary_aus(),
            ));
            query_valid_implies_path_prefix_valid(
                self.cache@,
                root@,
                candidate.route_key,
                candidate.fuel as nat,
                candidate.target_depth as nat,
                CACHE_SIZE_RECS as nat,
                self.branch.ownership.betree.active_aus(),
                self.branch.ownership.branches.active_summary_map(),
                self.branch.ownership.branches.active_summary_aus(),
            );
        }
        let ghost pre_state = self.model@.value();
        match self.branch.compact_begin_with_cache(
            &mut self.cache,
            candidate.target_addr,
            candidate.route_key,
            candidate.target_depth,
            candidate.fuel,
            self.disk_page_count,
            candidate.start,
            candidate.end,
        ) {
            BranchBetreeCompactBeginResult::NeedCacheLoad { addr, handle } => {
                proof {
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        self.cache@,
                        cache_load_label(&addr),
                    );
                    assert(old(self).branch.ownership.betree.active_aus()
                        .contains(addr@.au));
                    assert(addr@ != spec_superblock_addr());
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.outstanding_requests_wf());
                    assert(self.state() == old(self).state());
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.phase_alignment());
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.state().outstanding_cache_reqs
                        == Map::<ID, Address>::empty()) by {
                        assert_maps_equal!(
                            self.state().outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if self.state().outstanding_cache_reqs
                                    .contains_key(id)
                                {
                                    assert(self.outstanding_requests@
                                        .contains_key(id));
                                }
                            }
                        );
                    }
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_read_io(
                    addr,
                    handle,
                    CacheReadPurpose::CompactionExecute,
                    api,
                )
            },
            BranchBetreeCompactBeginResult::Stale
            | BranchBetreeCompactBeginResult::InvalidPage => {
                self.compaction_work = None;
                proof {
                    assert(self.branch.compactors@.len() == 0) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.branch.wip_branches@.len() == 0) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.state() == old(self).state());
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree dropped stale compaction candidate");
                true
            },
            BranchBetreeCompactBeginResult::CacheFull
            | BranchBetreeCompactBeginResult::Blocked => {
                proof {
                    assert(self.state() == old(self).state());
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                false
            },
            BranchBetreeCompactBeginResult::Began { input_idx, access } => {
                let ghost access_v = access@;
                let ghost branch_lbl =
                    AtomicBranchBetreeState::Label::InternalAccess{
                        access: access_v,
                    };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(AtomicBranchBetreeState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        branch_lbl,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_access(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            branch_lbl,
                            access_v,
                            self.cache@,
                            self.branch@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_access(
                                branch_lbl,
                                access_v,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::OutputCreation,
                    input_idx: Some(input_idx),
                    output_idx: None,
                });
                proof {
                    assert(input_idx == 0);
                    assert(self.branch.compactors@.len() == 1);
                    assert(self.branch.wip_branches@.len() == 0);
                    assert(self.branch.root is Some);
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree compaction began");
                true
            },
        }
    }

    fn record_compaction_output_begin(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is OutputCreation,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
            assert(old(self).branch.compactors@.len() == 1);
            assert(old(self).branch.wip_branches@.len() == 0);
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let ghost pre_state = self.model@.value();
        match self.branch.branch_begin_streaming(
            BETREE_BRANCH_FREE_AU_THRESHOLD,
        ) {
            BranchBetreeBulkStartResult::Started { idx } => {
                let ghost empty = Map::<Address, RawPage>::empty();
                let ghost access = PageAccess::empty();
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        branch: self.branch@,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(access == PageAccess::empty());
                    assert(access.reads() == empty);
                    assert(access.writes() == empty);
                    assert(pre_state.state.branch == old(self).branch@);
                    assert(AtomicBranchBetreeState::State::next(
                        old(self).branch@,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: PageAccess::empty(),
                        },
                    ));
                    assert(AtomicBranchBetreeState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access,
                        },
                    ));
                    Cache::State::access_empty_is_noop(
                        pre_state.state.cache,
                    );
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            Set::empty(),
                            Set::empty(),
                            access,
                            pre_state.state.cache,
                            self.branch@,
                        )) by {
                        assert_sets_equal!(
                            pre_state.state.branch.control.reclaimable(
                                Set::empty(),
                            ),
                            Set::<AU>::empty(),
                            au => {}
                        );
                        assert_sets_equal!(
                            (pre_state.state.free_aus - Set::empty())
                                + pre_state.state.branch.control.reclaimable(
                                    Set::empty(),
                                ),
                            pre_state.state.free_aus,
                            au => {}
                        );
                    }
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_alloc_access(
                                Set::empty(),
                                Set::empty(),
                                access,
                                pre_state.state.cache,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::InitializeCursors,
                    input_idx: Some(input_idx),
                    output_idx: Some(idx),
                });
                proof {
                    assert(input_idx == 0);
                    assert(idx == 0);
                    assert(self.branch.compactors@.len() == 1);
                    assert(self.branch.compactors@[0]
                        == old(self).branch.compactors@[0]);
                    assert(self.branch.compactors@[0].merge is None);
                    assert(self.branch.wip_branches@.len() == 1);
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree compaction output branch started");
                true
            },
            BranchBetreeBulkStartResult::Empty
            | BranchBetreeBulkStartResult::Overflow
            | BranchBetreeBulkStartResult::InvalidCapacity
            | BranchBetreeBulkStartResult::Blocked => {
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::AbortCompactor,
                    input_idx: Some(input_idx),
                    output_idx: None,
                });
                proof {
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                true
            },
        }
    }

    fn record_compaction_initialize_cursors(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is InitializeCursors,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
            assert(old(self).compaction_work.unwrap().input_idx
                == Some(0usize));
            assert(old(self).compaction_work.unwrap().output_idx
                == Some(0usize));
            assert(old(self).branch.compactors@.len() == 1);
            assert(old(self).branch.wip_branches@.len() == 1);
            assert(old(self).branch.wip_branches@[0]
                .has_streaming_builder());
            assert(old(self).branch.wip_branches@[0]
                .streaming_builder().phase is Reading);
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let output_idx = work.output_idx.unwrap();
        let ghost sources = self
            .ready_compaction_sources_certificate(input_idx);
        self.branch.compact_initialize_cursors(
            &self.cache,
            input_idx,
            Ghost(sources),
        );
        self.compaction_work = Some(CompactionWorkItem {
            candidate,
            phase: CompactionWorkPhase::Scanning,
            input_idx: Some(input_idx),
            output_idx: Some(output_idx),
        });
        proof {
            assert(self.state() == old(self).state());
            assert(input_idx == 0);
            assert(output_idx == 0);
            assert(self.branch.compactors@.len() == 1);
            assert(self.branch.compactors@[0].merge is Some);
            assert(!self.branch.compactors@[0].merge_done);
            assert(self.branch.wip_branches@.len() == 1);
            assert(self.branch.wip_branches@[0]
                .has_streaming_builder());
            assert(self.branch.wip_branches@[0]
                .streaming_builder().phase is Reading);
            assert(read_ref_aus(compactor_views(
                self.branch.compactors@,
            )) <= self.branch.branch_likes@.dom());
            assert(self.branch.compactors@[0].cache_inv(self.cache@));
            assert(self.branch.wip_branches@[0].cache_inv(self.cache@));
            assert_seqs_equal!(
                self.branch.wip_branches@[0]
                    .streaming_builder().source_entries@,
                compact_stream_entries(
                    self.branch.compactors@[0].merge->0.output@,
                ),
                i => {}
            );
            assert(self.compaction_executor_wf()) by {
                reveal(Implementation::compaction_executor_wf);
            }
            assert(self.common_inv()) by {
                reveal(Implementation::common_inv);
            }
            assert(self.inv_api(api));
        }
        api.log("unified-cache Betree compaction cursors initialized");
        true
    }

    fn record_compaction_scan_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is Scanning,
            old(self).branch.wip_branches@[
                old(self).compaction_work.unwrap().output_idx.unwrap()
                    as int
            ].streaming_builder().pending is None,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let output_idx = work.output_idx.unwrap();
        proof {
            assert(input_idx == 0);
            assert(output_idx == 0);
            assert(self.branch.wip_branches@[output_idx as int]
                .streaming_builder().source_entries@
                == compact_stream_entries(
                    self.branch.compactors@[input_idx as int]
                        .merge->0.output@,
                ));
            assert(self.branch.wip_branches@[output_idx as int]
                .streaming_builder().local_wf());
            self.branch.wip_branches@[output_idx as int]
                .streaming_builder().pending_none_has_no_deferred();
            self.ready_query_cache_certificate();
            self.ready_journal_cache_certificate();
        }
        let ghost pre_state = self.model@.value();
        match self.branch.compact_stream_step(
            &mut self.cache,
            input_idx,
            output_idx,
        ) {
            BranchBetreeCompactStreamResult::NeedCacheLoad {
                addr,
                handle,
            } => {
                proof {
                    assert(old(self).branch.compactors@[input_idx as int]
                        .input_aus@.contains(addr@.au));
                    assert(old(self).branch.compactors@[input_idx as int]
                        .input_aus@
                        <= old(self).branch.ownership.branches
                            .active_summary_aus());
                    assert(addresses_in_aus(
                        old(self).branch.ownership.branches.active_summary_aus(),
                    ).contains(addr@));
                    assert(addr@ != spec_superblock_addr());
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        self.cache@,
                        cache_load_label(&addr),
                    );
                    assert(self.state() == old(self).state());
                    assert(self.branch.wip_branches@[0]
                        .mini_allocator.bounded(self.disk_au_count));
                    assert(self.branch.wip_branches@[0]
                        .mini_allocator.i().all_aus().disjoint(
                            self.branch.control_i().protected_aus(),
                        ));
                    assert(self.branch.wip_branches@[0]
                        .mini_allocator.i().all_aus().disjoint(
                            self.branch.ownership.betree.all_aus()
                                + self.branch.ownership.branches
                                    .all_summary_aus(),
                        ));
                    assert(self.branch.wip_branches@[0]
                        .mini_allocator.i().all_aus().disjoint(
                            self.journal.owned_aus(),
                        ));
                    assert(self.branch.wip_branches@[0]
                        .cache_inv(self.cache@));
                    assert(self.branch.compactors@[0].merge is Some);
                    assert(!self.branch.compactors@[0].merge_done);
                    assert(self.branch.compactors@[0]
                        .cache_inv(self.cache@));
                    assert(self.branch.wip_branches@[0]
                        .streaming_builder().source_entries@
                        == compact_stream_entries(
                            self.branch.compactors@[0]
                                .merge->0.output@,
                        ));
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.state().outstanding_cache_reqs
                        == Map::<ID, Address>::empty()) by {
                        assert_maps_equal!(
                            self.state().outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if self.state().outstanding_cache_reqs
                                    .contains_key(id)
                                {
                                    assert(self.outstanding_requests@
                                        .contains_key(id));
                                }
                            }
                        );
                    }
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_read_io(
                    addr,
                    handle,
                    CacheReadPurpose::CompactionExecute,
                    api,
                )
            },
            BranchBetreeCompactStreamResult::ReadAdvanced { reads } => {
                let ghost access = PageAccess {
                    betree_reads: Map::empty(),
                    branch_reads: reads@,
                    betree_writes: Map::empty(),
                    branch_writes: Map::empty(),
                };
                let ghost branch_lbl =
                    AtomicBranchBetreeState::Label::InternalAccess{access};
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(access.wf());
                    assert_maps_equal!(access.reads(), reads@, addr => {});
                    assert_maps_equal!(
                        access.writes(),
                        Map::<Address, RawPage>::empty(),
                        addr => {}
                    );
                    assert(AtomicBranchBetreeState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        branch_lbl,
                    ));
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        self.cache@,
                        Cache::Label::Access {
                            reads: access.reads(),
                            writes: access.writes(),
                        },
                    ));
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_access(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            branch_lbl,
                            access,
                            self.cache@,
                            self.branch@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_access(
                                branch_lbl,
                                access,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    assert(input_idx == 0);
                    assert(output_idx == 0);
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                true
            },
            BranchBetreeCompactStreamResult::Done => {
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::FinishingInput,
                    input_idx: Some(input_idx),
                    output_idx: Some(output_idx),
                });
                proof {
                    assert(self.state() == old(self).state());
                    assert(input_idx == 0);
                    assert(output_idx == 0);
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                true
            },
            BranchBetreeCompactStreamResult::InvalidPage => {
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::AbortCompactor,
                    input_idx: Some(input_idx),
                    output_idx: Some(output_idx),
                });
                proof {
                    assert(self.state() == old(self).state());
                    assert(input_idx == 0);
                    assert(output_idx == 0);
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                true
            },
            BranchBetreeCompactStreamResult::ItemAccepted
            | BranchBetreeCompactStreamResult::PageReady
            | BranchBetreeCompactStreamResult::Skipped => {
                proof {
                    assert(self.state() == old(self).state());
                    assert(input_idx == 0);
                    assert(output_idx == 0);
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                true
            },
            BranchBetreeCompactStreamResult::CacheFull
            | BranchBetreeCompactStreamResult::Blocked => {
                proof {
                    assert(self.state() == old(self).state());
                    assert(input_idx == 0);
                    assert(output_idx == 0);
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                false
            },
        }
    }

    fn record_compaction_stage_page(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().output_idx is Some,
            old(self).compaction_work.unwrap().phase is Scanning
                || old(self).compaction_work.unwrap().phase is FinishingInput
                || old(self).compaction_work.unwrap().phase is FinishingLevels,
            old(self).branch.wip_branches@[
                old(self).compaction_work.unwrap().output_idx.unwrap() as int
            ].builder_page_ready(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
            self.ready_journal_cache_certificate();
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let output_idx = work.output_idx.unwrap();
        proof {
            match work.phase {
                CompactionWorkPhase::Scanning
                | CompactionWorkPhase::FinishingInput
                | CompactionWorkPhase::FinishingLevels => {},
                _ => assert(false),
            }
            assert(input_idx == 0);
            assert(output_idx == 0);
            assert(self.branch.compactors@.len() == 1);
            self.branch.compactor_wf_ensures(input_idx as int);
            if self.branch.compactors@[input_idx as int].merge is None {
                assert(!self.branch.compactors@[input_idx as int]
                    .merge_done);
                assert(work.phase is Scanning);
                assert(false);
            }
            assert(self.branch.compactors@[input_idx as int].merge is Some);
            assert(self.branch.wip_branches@.len() == 1);
            self.branch.ownership.branches.ownership_sets_bounded();
            assert(self.branch.wip_branches@[output_idx as int]
                .mini_allocator.i().all_aus().disjoint(
                    self.branch.ownership.branches.active_summary_aus(),
                ));
            self.branch.compactor_input_aus_subset_active(
                input_idx as int,
            );
        }
        let ghost input_merge =
            self.branch.compactors@[input_idx as int].merge->0;
        let ghost input_aus =
            self.branch.compactors@[input_idx as int].input_aus@;
        let ghost output_aus = self.branch.wip_branches@[
            output_idx as int
        ].mini_allocator.i().all_aus();
        let ghost pre_state = self.model@.value();
        match self.branch.branch_stage_bulk_page(
            &mut self.cache,
            output_idx,
            self.disk_au_count,
            self.disk_page_count,
        ) {
            BranchBetreeBuildResult::NeedsAUs
            | BranchBetreeBuildResult::CacheFull
            | BranchBetreeBuildResult::Blocked => {
                proof {
                    assert(self.state() == old(self).state());
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                false
            },
            BranchBetreeBuildResult::InvalidPage => {
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::AbortCompactor,
                    input_idx: Some(input_idx),
                    output_idx: Some(output_idx),
                });
                proof {
                    assert(self.state() == old(self).state());
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                true
            },
            BranchBetreeBuildResult::Applied {
                idx: post_idx,
                prepared_cache,
                access,
                event,
            } => {
                let ghost prepared_cache_v = prepared_cache@;
                let ghost access_v = access@;
                let ghost event_v = event@;
                let ghost branch_event = BranchBuildEvent::StagePage {
                    addr: event_v->addr,
                };
                let ghost reserve_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: prepared_cache_v,
                        ..pre_state.state
                    },
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        ..reserve_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    if work.phase is Scanning {
                        assert(input_merge.cache_inv(
                            pre_state.state.cache,
                        ));
                        assert(input_merge.source_aus() <= input_aus);
                        assert(input_aus
                            <= old(self).branch.ownership.branches
                                .active_summary_aus());
                        assert(output_aus.disjoint(
                            old(self).branch.ownership.branches
                                .active_summary_aus(),
                        ));
                        assert(access_v.writes().dom()
                            <= addresses_in_aus(output_aus));
                        assert(access_v.writes().dom().disjoint(
                            addresses_in_aus(input_merge.source_aus()),
                        )) by {
                            assert forall |addr: Address|
                                access_v.writes().dom().contains(addr)
                                    && addresses_in_aus(
                                        input_merge.source_aus(),
                                    ).contains(addr)
                                implies false by {
                                assert(output_aus.contains(addr.au));
                                assert(input_merge.source_aus()
                                    .contains(addr.au));
                                assert(input_aus.contains(addr.au));
                                assert(old(self).branch.ownership.branches
                                    .active_summary_aus().contains(addr.au));
                            }
                        }
                        input_merge.cache_inv_preserved_by_unrelated_access(
                            pre_state.state.cache,
                            prepared_cache_v,
                            self.cache@,
                            access_v.reads(),
                            access_v.writes(),
                        );
                        assert(self.branch.compactors@[input_idx as int]
                            .cache_inv(self.cache@));
                    }
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::cache_internal(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        prepared_cache_v,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::cache_internal(
                            prepared_cache_v,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        reserve_state,
                    );
                }
                let tracked _reserve_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    reserve_state,
                    &mut model,
                );
                proof {
                    assert(post_idx == output_idx);
                    assert(event_v is StagePage);
                    assert(branch_event.cached_event(access_v) == event_v);
                    assert(AtomicBranchBetreeState::State::next(
                        reserve_state.state.branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: Set::empty(),
                            access: access_v,
                        },
                    ));
                    assert_sets_equal!(
                        (reserve_state.state.free_aus - Set::empty())
                            + reserve_state.state.branch.control.reclaimable(
                                Set::empty(),
                            ),
                        reserve_state.state.free_aus,
                        au => {}
                    );
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            reserve_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            Set::empty(),
                            Set::empty(),
                            access_v,
                            self.cache@,
                            self.branch@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_alloc_access(
                                Set::empty(),
                                Set::empty(),
                                access_v,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        reserve_state,
                        post_state,
                    );
                }
                let tracked _access_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    );
                    Cache::State::inv_next(
                        prepared_cache_v,
                        self.cache@,
                        Cache::Label::Access {
                            reads: access_v.reads(),
                            writes: access_v.writes(),
                        },
                    );
                    assert(self.compaction_executor_wf()) by {
                        reveal(Implementation::compaction_executor_wf);
                    }
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree compaction staged one output page");
                true
            },
        }
    }

    fn record_compaction_finish_input(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is FinishingInput,
            old(self).compaction_work.unwrap().input_idx is Some,
            old(self).compaction_work.unwrap().output_idx is Some,
            old(self).branch.wip_branches@[
                old(self).compaction_work.unwrap().output_idx.unwrap() as int
            ].streaming_builder().pending is None,
            old(self).branch.wip_branches@[
                old(self).compaction_work.unwrap().output_idx.unwrap() as int
            ].streaming_builder().deferred is None,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let output_idx = work.output_idx.unwrap();
        proof {
            assert(input_idx == 0);
            assert(output_idx == 0);
            self.branch.compactor_wf_ensures(input_idx as int);
            if self.branch.compactors@[input_idx as int].merge is None {
                assert(!self.branch.compactors@[input_idx as int]
                    .merge_done);
                assert(false);
            }
        }
        let next_phase = match self.branch.compact_finish_streaming_input(
            input_idx,
            output_idx,
        ) {
            StreamingFinishInputResult::Empty => {
                CompactionWorkPhase::AbortCompactor
            },
            StreamingFinishInputResult::RootReady => {
                CompactionWorkPhase::Sealing
            },
            StreamingFinishInputResult::Continue => {
                CompactionWorkPhase::FinishingLevels
            },
        };
        self.compaction_work = Some(CompactionWorkItem {
            candidate,
            phase: next_phase,
            input_idx: Some(input_idx),
            output_idx: Some(output_idx),
        });
        proof {
            assert(self.state() == old(self).state());
            assert(self.compaction_executor_wf()) by {
                reveal(Implementation::compaction_executor_wf);
            }
            assert(self.common_inv()) by {
                reveal(Implementation::common_inv);
            }
            assert(self.inv_api(api));
        }
        true
    }

    fn record_compaction_finish_level(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is FinishingLevels,
            old(self).compaction_work.unwrap().input_idx is Some,
            old(self).compaction_work.unwrap().output_idx is Some,
            old(self).branch.wip_branches@[
                old(self).compaction_work.unwrap().output_idx.unwrap() as int
            ].streaming_builder().pending is None,
            old(self).branch.wip_branches@[
                old(self).compaction_work.unwrap().output_idx.unwrap() as int
            ].streaming_builder().deferred is None,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let output_idx = work.output_idx.unwrap();
        proof {
            assert(input_idx == 0);
            assert(output_idx == 0);
            self.branch.compactor_wf_ensures(input_idx as int);
            if self.branch.compactors@[input_idx as int].merge is None {
                assert(!self.branch.compactors@[input_idx as int]
                    .merge_done);
                assert(false);
            }
        }
        let next_phase = match self.branch.compact_finish_streaming_level(
            input_idx,
            output_idx,
        ) {
            StreamingFinishLevelResult::Empty => {
                CompactionWorkPhase::AbortCompactor
            },
            StreamingFinishLevelResult::Advanced
            | StreamingFinishLevelResult::PagesReady => {
                CompactionWorkPhase::FinishingLevels
            },
            StreamingFinishLevelResult::RootReady => {
                CompactionWorkPhase::Sealing
            },
        };
        self.compaction_work = Some(CompactionWorkItem {
            candidate,
            phase: next_phase,
            input_idx: Some(input_idx),
            output_idx: Some(output_idx),
        });
        proof {
            assert(self.state() == old(self).state());
            assert(self.compaction_executor_wf()) by {
                reveal(Implementation::compaction_executor_wf);
            }
            assert(self.common_inv()) by {
                reveal(Implementation::common_inv);
            }
            assert(self.inv_api(api));
        }
        true
    }

    fn record_compaction_bulk_seal(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is Sealing,
            old(self).compaction_work.unwrap().input_idx is Some,
            old(self).compaction_work.unwrap().output_idx is Some,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
            self.ready_journal_cache_certificate();
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let output_idx = work.output_idx.unwrap();
        proof {
            self.ready_branch_allocation_certificate();
        }
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch = self.branch@;
        let ghost pre_wip_aus = self.branch.wip_branches@[
            output_idx as int
        ].mini_allocator.i().all_aus();
        match self.branch.branch_bulk_seal(
            &mut self.cache,
            output_idx,
            self.disk_au_count,
            self.disk_page_count,
        ) {
            BranchBetreeBulkSealResult::NeedsAUs
            | BranchBetreeBulkSealResult::CacheFull
            | BranchBetreeBulkSealResult::Blocked => {
                proof { assert(self.inv_api(api)); }
                false
            },
            BranchBetreeBulkSealResult::InvalidPage => {
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::AbortCompactor,
                    input_idx: Some(input_idx),
                    output_idx: Some(output_idx),
                });
                proof {
                    assert(self.compaction_executor_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                true
            },
            BranchBetreeBulkSealResult::Sealed {
                idx: post_idx,
                root,
                aux_ptr,
                prepared_cache,
                access,
                event,
                deallocs,
                branch: _,
            } => {
                let ghost prepared_cache_v = prepared_cache@;
                let ghost access_v = access@;
                let ghost event_v = event@;
                let ghost dealloc_set = iau_vec_set(deallocs@);
                let ghost branch_event = BranchBuildEvent::BulkSeal {
                    root: root@,
                    aux_ptr: iopt_addr(aux_ptr),
                };
                proof {
                    assert(post_idx == output_idx);
                    assert(event_v is BulkSeal);
                    assert(dealloc_set <= pre_wip_aus);
                    assert(pre_pool.disjoint(dealloc_set)) by {
                        assert(pre_wip_aus <= pre_branch.betree.owned_aus());
                    }
                    assert forall |i: int| 0 <= i < deallocs@.len()
                        implies {
                            &&& 0 < #[trigger] (deallocs@[i] as nat)
                            &&& (deallocs@[i] as nat)
                                < self.disk_au_count as nat
                        } by {
                        let au = deallocs@[i] as nat;
                        assert(dealloc_set.contains(au));
                        assert(old(self).branch.wip_branches@[
                            output_idx as int
                        ].mini_allocator.bounded(self.disk_au_count));
                    }
                }
                self.au_pool.free_aus(self.disk_au_count, &deallocs);
                let ghost reserve_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: prepared_cache_v,
                        ..pre_state.state
                    },
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        free_aus: self.au_pool@,
                        ..reserve_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::cache_internal(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        prepared_cache_v,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::cache_internal(
                            prepared_cache_v,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        reserve_state,
                    );
                }
                let tracked _reserve_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    reserve_state,
                    &mut model,
                );
                proof {
                    assert(branch_event.cached_event(access_v) == event_v);
                    assert(AtomicBranchBetreeState::State::next(
                        reserve_state.state.branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: dealloc_set,
                            access: access_v,
                        },
                    ));
                    assert(dealloc_set.disjoint(
                        reserve_state.state.branch.control.protected_aus(),
                    ));
                    assert_sets_equal!(
                        reserve_state.state.branch.control.reclaimable(
                            dealloc_set,
                        ),
                        dealloc_set,
                        au => {}
                    );
                    assert_sets_equal!(
                        (reserve_state.state.free_aus - Set::empty())
                            + reserve_state.state.branch.control.reclaimable(
                                dealloc_set,
                            ),
                        self.au_pool@,
                        au => {}
                    );
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            reserve_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            Set::empty(),
                            dealloc_set,
                            access_v,
                            self.cache@,
                            self.branch@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_alloc_access(
                                Set::empty(),
                                dealloc_set,
                                access_v,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        reserve_state,
                        post_state,
                    );
                }
                let tracked _access_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::Completing,
                    input_idx: Some(input_idx),
                    output_idx: Some(output_idx),
                });
                proof {
                    assert(self.branch.root == old(self).branch.root);
                    assert(self.branch.root is Some);
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        prepared_cache_v,
                        Cache::Label::Internal,
                    );
                    Cache::State::inv_next(
                        prepared_cache_v,
                        self.cache@,
                        Cache::Label::Access {
                            reads: access_v.reads(),
                            writes: access_v.writes(),
                        },
                    );
                    assert(self.compaction_executor_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree compaction output sealed");
                true
            },
        }
    }

    fn record_compaction_complete(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is Completing,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
            assert(old(self).branch.compactors@.len() == 1);
            assert(old(self).branch.wip_branches@.len() == 1);
            assert(old(self).branch.root is Some) by {
                assert(old(self).branch.wf());
            }
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let output_idx = work.output_idx.unwrap();

        if candidate.target_depth + 1 >= self.disk_au_count as usize {
            self.compaction_work = Some(CompactionWorkItem {
                candidate,
                phase: CompactionWorkPhase::AbortCompactor,
                input_idx: Some(input_idx),
                output_idx: Some(output_idx),
            });
            proof {
                assert(self.compaction_executor_wf());
                assert(self.common_inv());
                assert(self.inv_api(api));
            }
            return true;
        }

        proof {
            self.ready_branch_allocation_certificate();
            self.ready_query_cache_certificate();
            self.ready_journal_cache_certificate();
            assert(self.branch.query_cache_inv(self.cache@));
            assert(candidate.fuel == CACHE_SIZE_RECS);
            self.branch.compactor_wf_ensures(input_idx as int);
            assert(self.branch.compactors@[input_idx as int].merge is Some);
            let root = self.branch.root.unwrap();
            assert(cached_betree_query_valid(
                self.cache@,
                root@,
                candidate.route_key,
                candidate.fuel as nat,
                CACHE_SIZE_RECS as nat,
                self.branch.ownership.betree.active_aus(),
                self.branch.ownership.branches.active_summary_map(),
                self.branch.ownership.branches.active_summary_aus(),
            ));
            query_valid_implies_path_prefix_valid(
                self.cache@,
                root@,
                candidate.route_key,
                candidate.fuel as nat,
                candidate.target_depth as nat,
                CACHE_SIZE_RECS as nat,
                self.branch.ownership.betree.active_aus(),
                self.branch.ownership.branches.active_summary_map(),
                self.branch.ownership.branches.active_summary_aus(),
            );
        }

        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch = self.branch@;
        proof {
            self.branch.ownership.betree.view_domain_matches_active();
            assert(self.branch.ownership.betree.active_aus()
                =~= pre_branch.betree.betree_aus.dom());
        }
        let alloc_count = (candidate.target_depth as IAU) + 1;
        let allocation = match self.au_pool.alloc(
            self.disk_au_count,
            alloc_count,
        ) {
            Some(allocation) => allocation,
            None => {
                proof { assert(self.inv_api(api)); }
                return false;
            },
        };
        let ghost alloc_set = allocation.as_set();
        proof {
            allocation.vec_set_matches(self.disk_au_count);
            assert forall |au: AU| #[trigger] alloc_set.contains(au)
                implies 0 < au && au < self.disk_au_count as nat by {
                assert(allocation.run.as_set().contains(au));
                assert(allocation.run.contains_au(au));
            }
            assert(MiniAllocatorImpl::iau_seq_unique(allocation.aus@)) by {
                assert forall |i: int, j: int|
                    0 <= i < allocation.aus@.len()
                    && 0 <= j < allocation.aus@.len()
                    && #[trigger] allocation.aus@[i]
                        == #[trigger] allocation.aus@[j]
                    implies i == j by {
                    assert(AuAllocation::vec_matches_run(
                        allocation.aus@,
                        allocation.run,
                    ));
                    assert(allocation.aus@[i] as nat
                        == allocation.run.start as nat + i as nat);
                    assert(allocation.aus@[j] as nat
                        == allocation.run.start as nat + j as nat);
                }
            }
            assert(alloc_set <= pre_pool);
            assert(self.au_pool@ =~= pre_pool - alloc_set);
            assert(pre_branch.betree.is_fresh(alloc_set)) by {
                assert(pre_pool.disjoint(pre_branch.betree.owned_aus()));
            }
            assert(pre_branch.control.protected_aus().disjoint(alloc_set));
        }
        let rollback_aus = allocation.aus;
        let (new_node_addr, path_addrs) =
            compaction_destination_addrs(&rollback_aus);
        let ghost destination_aus = to_aus(
            iaddr_views(path_addrs@).to_set(),
        ).insert(new_node_addr@.au);
        proof {
            assert(destination_aus =~= alloc_set);
            assert(path_addrs@.len() == candidate.target_depth as nat);
            assert(pre_branch.betree.is_fresh(destination_aus));
            assert(pre_branch.betree.wip_branches[output_idx as int]
                .mini_allocator.all_aus().disjoint(destination_aus)) by {
                assert(pre_branch.betree.owned_aus().disjoint(pre_pool));
            }
        }

        match self.branch.compact_complete_with_cache(
            &mut self.cache,
            input_idx,
            output_idx,
            candidate.route_key,
            candidate.target_depth,
            candidate.fuel,
            self.disk_page_count,
            candidate.target_addr,
            candidate.start,
            candidate.end,
            new_node_addr,
            &path_addrs,
        ) {
            BranchBetreeCompactCompleteResult::NeedCacheLoad {
                addr,
                handle,
            } => {
                proof {
                    assert(self.au_pool@.disjoint(
                        iau_vec_set(rollback_aus@),
                    ));
                    assert forall |i: int| 0 <= i < rollback_aus@.len()
                        implies {
                            &&& 0 < #[trigger] (rollback_aus@[i] as nat)
                            &&& ((rollback_aus@[i] as nat)
                                < (self.disk_au_count as nat))
                        } by {
                        assert(alloc_set.contains(
                            rollback_aus@[i] as nat,
                        ));
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &rollback_aus,
                );
                proof {
                    assert(self.au_pool@ =~= pre_pool);
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        self.cache@,
                        cache_load_label(&addr),
                    );
                    assert((pre_branch.betree.betree_aus.dom()
                        + alloc_set).contains(addr@.au));
                    assert(addr@ != spec_superblock_addr());
                    assert(self.state().outstanding_cache_reqs
                        == Map::<ID, Address>::empty()) by {
                        assert_maps_equal!(
                            self.state().outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if self.state().outstanding_cache_reqs
                                    .contains_key(id)
                                {
                                    assert(self.outstanding_requests@
                                        .contains_key(id));
                                }
                            }
                        );
                    }
                    assert(self.common_inv());
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_read_io(
                    addr,
                    handle,
                    CacheReadPurpose::CompactionExecute,
                    api,
                )
            },
            BranchBetreeCompactCompleteResult::CacheFull
            | BranchBetreeCompactCompleteResult::Blocked => {
                proof {
                    assert(self.au_pool@.disjoint(
                        iau_vec_set(rollback_aus@),
                    ));
                    assert forall |i: int| 0 <= i < rollback_aus@.len()
                        implies {
                            &&& 0 < #[trigger] (rollback_aus@[i] as nat)
                            &&& (rollback_aus@[i] as nat)
                                < (self.disk_au_count as nat)
                        } by {
                        assert(alloc_set.contains(
                            rollback_aus@[i] as nat,
                        ));
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &rollback_aus,
                );
                proof {
                    assert(self.au_pool@ =~= pre_pool);
                    assert(self.inv_api(api));
                }
                false
            },
            BranchBetreeCompactCompleteResult::Stale
            | BranchBetreeCompactCompleteResult::InvalidPage => {
                proof {
                    assert(self.au_pool@.disjoint(
                        iau_vec_set(rollback_aus@),
                    ));
                    assert forall |i: int| 0 <= i < rollback_aus@.len()
                        implies {
                            &&& 0 < #[trigger] (rollback_aus@[i] as nat)
                            &&& (rollback_aus@[i] as nat)
                                < (self.disk_au_count as nat)
                        } by {
                        assert(alloc_set.contains(
                            rollback_aus@[i] as nat,
                        ));
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &rollback_aus,
                );
                self.compaction_work = Some(CompactionWorkItem {
                    candidate,
                    phase: CompactionWorkPhase::AbortCompactor,
                    input_idx: Some(input_idx),
                    output_idx: Some(output_idx),
                });
                proof {
                    assert(self.au_pool@ =~= pre_pool);
                    assert(self.compaction_executor_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree compaction target became stale");
                true
            },
            BranchBetreeCompactCompleteResult::Completed {
                new_root: _,
                mut betree_reclaimed,
                branch_reclaimed,
                prepared_cache,
                access,
                allocs,
                deallocs,
            } => {
                let ghost prepared_cache_v = prepared_cache@;
                let ghost access_v = access@;
                let ghost allocs_v = allocs@;
                let ghost deallocs_v = deallocs@;
                let ghost betree_reclaimed_set =
                    iau_seq_set(betree_reclaimed@);
                let ghost branch_reclaimed_set =
                    iau_seq_set(branch_reclaimed@);
                proof {
                    assert_sets_equal!(allocs_v, alloc_set, au => {});
                }
                append_unique_aus(
                    &mut betree_reclaimed,
                    branch_reclaimed,
                );
                let reclaimed = betree_reclaimed;
                let ghost reclaimed_set = iau_seq_set(reclaimed@);
                proof {
                    old(self).branch.ownership.betree.ownership_sets_bounded();
                    old(self).branch.ownership.branches.ownership_sets_bounded();
                    assert(pre_branch.betree.durable_aus()
                        == old(self).branch.ownership.current_durable_aus());
                    assert(deallocs_v
                        <= pre_branch.betree.durable_aus());
                    assert(deallocs_v <= old(self).branch.ownership.betree.all_aus()
                        + old(self).branch.ownership.branches.all_summary_aus());
                    assert(reclaimed_set
                        =~= betree_reclaimed_set + branch_reclaimed_set);
                    assert(reclaimed_set
                        == pre_branch.control.reclaimable(deallocs_v));
                    assert(reclaimed_set <= deallocs_v);
                    assert(self.au_pool@.disjoint(reclaimed_set)) by {
                        assert(pre_pool.disjoint(
                            pre_branch.betree.owned_aus(),
                        ));
                        assert(deallocs_v
                            <= pre_branch.betree.owned_aus());
                    }
                    assert forall |i: int| 0 <= i < reclaimed@.len()
                        implies {
                            &&& 0 < #[trigger] (reclaimed@[i] as nat)
                            &&& (reclaimed@[i] as nat)
                                < (self.disk_au_count as nat)
                        } by {
                        let au = reclaimed@[i] as nat;
                        assert(reclaimed_set.contains(au));
                        assert(deallocs_v.contains(au));
                        assert((old(self).branch.ownership.betree.all_aus()
                            + old(self).branch.ownership.branches.all_summary_aus())
                            .contains(au));
                        assert(old(self).branch_owned_aus_bounded());
                    }
                }
                self.au_pool.free_aus(
                    self.disk_au_count,
                    &reclaimed,
                );

                let ghost reserve_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: prepared_cache_v,
                        ..pre_state.state
                    },
                };
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        cache: self.cache@,
                        branch: self.branch@,
                        free_aus: self.au_pool@,
                        ..reserve_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(UnifiedCacheBetreeSystem::State::cache_internal(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        prepared_cache_v,
                    ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::cache_internal(
                            prepared_cache_v,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        reserve_state,
                    );
                }
                let tracked _reserve_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    reserve_state,
                    &mut model,
                );
                proof {
                    assert(AtomicBranchBetreeState::State::next(
                        reserve_state.state.branch,
                        self.branch@,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: allocs_v,
                            deallocs: deallocs_v,
                            access: access_v,
                        },
                    ));
                    assert_sets_equal!(
                        (reserve_state.state.free_aus - allocs_v)
                            + reserve_state.state.branch.control.reclaimable(
                                deallocs_v,
                            ),
                        self.au_pool@,
                        au => {}
                    );
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            reserve_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            allocs_v,
                            deallocs_v,
                            access_v,
                            self.cache@,
                            self.branch@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::
                            branch_internal_alloc_access(
                                allocs_v,
                                deallocs_v,
                                access_v,
                                self.cache@,
                                self.branch@,
                            ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        reserve_state,
                        post_state,
                    );
                }
                let tracked _access_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.compaction_work = None;
                proof {
                    assert(self.branch.memtable == old(self).branch.memtable);
                    assert(self.branch.control == old(self).branch.control);
                    assert(self.branch_owned_aus_bounded()) by {
                        reveal(Implementation::branch_owned_aus_bounded);
                        assert forall |au: AU| #[trigger]
                            (self.branch.ownership.betree.all_aus()
                                + self.branch.ownership.branches
                                    .all_summary_aus()).contains(au)
                            implies 0 < au
                                && au < self.disk_au_count as nat by {
                            if (old(self).branch.ownership.betree.all_aus()
                                + old(self).branch.ownership.branches
                                    .all_summary_aus()).contains(au)
                            {
                                assert(old(self).branch_owned_aus_bounded());
                            } else if alloc_set.contains(au) {
                            } else {
                                assert(old(self).branch.wip_branches@[
                                    output_idx as int
                                ].mini_allocator.i().all_aus().contains(au));
                                old(self).branch.wip_branches@[
                                    output_idx as int
                                ].mini_allocator.owned_au_bounded(
                                    self.disk_au_count,
                                    au,
                                );
                            }
                        }
                    }
                    assert(self.branch.control.metadata.root is Some ==>
                        self.branch.control.metadata.root.unwrap()@.au
                            < self.disk_au_count as nat);
                    assert(self.sync_wf()) by {
                        reveal(Implementation::sync_wf);
                    }
                    assert(self.compaction_executor_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree compaction completed");
                true
            },
        }
    }

    fn record_compaction_abort_compactor(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is AbortCompactor,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress,
    {
        proof {
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            reveal(Implementation::common_inv);
            reveal(Implementation::compaction_executor_wf);
            assert(old(self).branch.compactors@.len() == 1);
        }
        let work = self.compaction_work.unwrap();
        let candidate = work.candidate;
        let input_idx = work.input_idx.unwrap();
        let output_idx = work.output_idx;
        let ghost pre_state = self.model@.value();
        proof {
            assert(input_idx == 0);
            assert(input_idx < self.branch.compactors@.len());
        }
        match self.branch.compact_abort(input_idx) {
            BranchBetreeCompactAbortResult::Noop => {
                proof { assert(false); }
                true
            },
            BranchBetreeCompactAbortResult::Aborted { deallocs } => {
                let ghost dealloc_set = deallocs@;
                let ghost post_state = UnifiedCacheBetreeProgramModel {
                    state: UnifiedCacheBetreeSystem::State {
                        branch: self.branch@,
                        ..pre_state.state
                    },
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    let access = PageAccess::empty();
                    assert(dealloc_set.is_empty());
                    assert(pre_state.state.branch == old(self).branch@);
                    assert(post_state.state.branch == self.branch@);
                    assert(AtomicBranchBetreeState::State::next(
                        pre_state.state.branch,
                        post_state.state.branch,
                        AtomicBranchBetreeState::Label::InternalAllocAccess {
                            allocs: Set::empty(),
                            deallocs: dealloc_set,
                            access,
                        },
                    ));
                    assert(pre_state.state.client_ready());
                    assert(Set::<AU>::empty() <= pre_state.state.free_aus);
                    assert(Set::<AU>::empty().disjoint(
                        pre_state.state.branch.control.protected_aus(),
                    ));
                    Cache::State::access_empty_is_noop(pre_state.state.cache);
                    assert(pre_state.state.branch.control.reclaimable(
                        dealloc_set,
                    ).is_empty());
                    assert_sets_equal!(
                        (pre_state.state.free_aus - Set::<AU>::empty())
                            + pre_state.state.branch.control.reclaimable(
                                dealloc_set,
                            ),
                        pre_state.state.free_aus,
                        au => {}
                    );
                    assert(post_state.state.free_aus
                        =~= pre_state.state.free_aus);
                    PageAccess::empty_cached_access_is_empty();
                    assert(access.reads()
                        == Map::<Address, RawPage>::empty());
                    assert(access.writes()
                        == Map::<Address, RawPage>::empty());
                    assert(UnifiedCacheBetreeSystem::State::
                        branch_internal_alloc_access(
                            pre_state.state,
                            post_state.state,
                            UnifiedCacheBetreeSystem::Label::Internal,
                            Set::empty(),
                            dealloc_set,
                            access,
                            pre_state.state.cache,
                            self.branch@,
                        ));
                    assert(UnifiedCacheBetreeSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheBetreeSystem::Label::Internal,
                        UnifiedCacheBetreeSystem::Step::branch_internal_alloc_access(
                            Set::empty(),
                            dealloc_set,
                            access,
                            pre_state.state.cache,
                            self.branch@,
                        ),
                    )) by {
                        reveal(UnifiedCacheBetreeSystem::State::next_by);
                    }
                    UnifiedCacheBetreeProgramModel::lift_internal_step(
                        pre_state,
                        post_state,
                    );
                }
                let tracked _token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp {},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.compaction_work = match output_idx {
                    Some(output_idx) => Some(CompactionWorkItem {
                        candidate,
                        phase: CompactionWorkPhase::AbortBranch,
                        input_idx: None,
                        output_idx: Some(output_idx),
                    }),
                    None => None,
                };
                proof {
                    assert(self.branch.compactors@.len() == 0);
                    match output_idx {
                        Some(idx) => {
                            assert(idx == 0);
                            assert(self.branch.wip_branches@.len() == 1);
                            assert(self.compaction_work.unwrap().phase
                                is AbortBranch);
                        },
                        None => {
                            assert(self.branch.wip_branches@.len() == 0);
                            assert(self.compaction_work is None);
                        },
                    }
                    assert(self.compaction_executor_wf());
                    assert(self.common_inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree compactor aborted");
                true
            },
        }
    }

    fn record_compaction_abort_branch(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_work is Some,
            old(self).compaction_work.unwrap().phase is AbortBranch,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.compaction_work is None,
            progress,
    {
        let work = self.compaction_work.unwrap();
        let output_idx = work.output_idx.unwrap();
        proof {
            self.ready_branch_allocation_certificate();
        }
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch = self.branch@;
        let result = self.branch.branch_abort(output_idx);
        let deallocs = match result {
            BranchBetreeAbortResult::Aborted { deallocs } => deallocs,
        };
        let ghost dealloc_set = iau_seq_set(deallocs@);
        proof {
            assert(iau_vec_set(deallocs@) =~= dealloc_set) by {
                assert forall |au: AU|
                    #[trigger] iau_vec_set(deallocs@).contains(au)
                        <==> dealloc_set.contains(au) by {}
            }
            assert(dealloc_set
                == old(self).branch.wip_branches@[output_idx as int]
                    .mini_allocator.i().all_aus());
            assert(pre_pool.disjoint(dealloc_set)) by {
                assert(dealloc_set <= pre_branch.betree.owned_aus());
            }
            assert forall |i: int| 0 <= i < deallocs@.len()
                implies {
                    &&& 0 < #[trigger] (deallocs@[i] as nat)
                    &&& (deallocs@[i] as nat)
                        < self.disk_au_count as nat
                } by {
                let au = deallocs@[i] as nat;
                assert(dealloc_set.contains(au));
                assert(old(self).branch.wip_branches@[output_idx as int]
                    .mini_allocator.bounded(self.disk_au_count));
            }
        }
        self.au_pool.free_aus(self.disk_au_count, &deallocs);
        let ghost post_state = UnifiedCacheBetreeProgramModel {
            state: UnifiedCacheBetreeSystem::State {
                free_aus: self.au_pool@,
                branch: self.branch@,
                ..pre_state.state
            },
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
            let access = PageAccess::empty();
            assert(dealloc_set.disjoint(
                pre_state.state.branch.control.protected_aus(),
            ));
            assert_sets_equal!(
                pre_state.state.branch.control.reclaimable(dealloc_set),
                dealloc_set,
                au => {}
            );
            assert_sets_equal!(
                (pre_state.state.free_aus - Set::<AU>::empty())
                    + pre_state.state.branch.control.reclaimable(
                        dealloc_set,
                    ),
                self.au_pool@,
                au => {}
            );
            PageAccess::empty_cached_access_is_empty();
            assert(access.reads()
                == Map::<Address, RawPage>::empty());
            assert(access.writes()
                == Map::<Address, RawPage>::empty());
            Cache::State::access_empty_is_noop(pre_state.state.cache);
            assert(UnifiedCacheBetreeSystem::State::branch_internal_alloc_access(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Internal,
                Set::empty(),
                dealloc_set,
                access,
                pre_state.state.cache,
                self.branch@,
            ));
            assert(UnifiedCacheBetreeSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheBetreeSystem::Label::Internal,
                UnifiedCacheBetreeSystem::Step::branch_internal_alloc_access(
                    Set::empty(),
                    dealloc_set,
                    access,
                    pre_state.state.cache,
                    self.branch@,
                ),
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::next_by);
            }
            UnifiedCacheBetreeProgramModel::lift_internal_step(
                pre_state,
                post_state,
            );
        }
        let tracked _token = self.instance.borrow().internal(
            KVStoreTokenized::Label::InternalOp {},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);
        self.compaction_work = None;
        proof {
            assert(self.compaction_executor_wf());
            assert(self.common_inv());
            assert(self.inv_api(api));
        }
        api.log("unified-cache Betree compaction output branch aborted");
        true
    }

    fn record_compaction_picker_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).sync_phase is None,
            old(self).store_flush_phase is None,
            old(self).compaction_work is None,
            old(self).outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).compaction_candidates.entries@
                == Seq::<CompactionCandidate>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.sync_phase is None,
            self.store_flush_phase is None,
            self.sync_requests.buffered_reqs@
                == old(self).sync_requests.buffered_reqs@,
            self.sync_requests.journal_cleaning_reqs@
                == old(self).sync_requests.journal_cleaning_reqs@,
            self.sync_requests.superblocking_reqs@
                == old(self).sync_requests.superblocking_reqs@,
            self.sync_requests.sync_target_lsn
                == old(self).sync_requests.sync_target_lsn,
            !progress ==> {
                &&& self.outstanding_requests@
                    == Map::<ID, OutstandingReqInfo>::empty()
                &&& self.compaction_candidates.entries@
                    == Seq::<CompactionCandidate>::empty()
            },
    {
        if !self.compaction_picker.needs_probe(&self.branch.root) {
            return false;
        }
        proof {
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty());
            assert(self.state().outstanding_cache_reqs
                == Map::<ID, Address>::empty()) by {
                assert_maps_equal!(
                    self.state().outstanding_cache_reqs,
                    Map::<ID, Address>::empty(),
                    id => {
                        if self.state().outstanding_cache_reqs
                            .contains_key(id)
                        {
                            assert(self.outstanding_requests@
                                .contains_key(id));
                        }
                    }
                );
            }
            self.ready_query_cache_certificate();
            assert(self.branch.query_cache_inv(self.cache@));
        }
        let step = self.compaction_picker.step(
            &self.branch,
            &mut self.cache,
        );
        match step {
            CompactionPickerStepResult::Candidate { candidate } => {
                let result = self.compaction_candidates.push(candidate);
                match result {
                    CompactionEnqueueResult::Enqueued => {},
                    CompactionEnqueueResult::Noop => {
                        proof {
                            assert(candidate.wf());
                            assert(old(self).compaction_candidates.entries@
                                .len() == 0);
                            assert(old(self).compaction_candidates.capacity
                                == COMPACTION_CANDIDATE_CAPACITY);
                            assert(COMPACTION_CANDIDATE_CAPACITY > 0);
                            assert(old(self).compaction_candidates.entries@
                                == Seq::<CompactionCandidate>::empty());
                            assert(false);
                        }
                    },
                }
                proof {
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.outstanding_requests_wf());
                    assert(self.state() == old(self).state());
                    assert(self.phase_alignment());
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree queued compaction candidate");
                true
            },
            CompactionPickerStepResult::NeedCacheLoad { addr, handle } => {
                proof {
                    let owned = self.branch.ownership.betree.active_aus()
                        + self.branch.ownership.branches
                            .active_summary_aus();
                    assert(owned.contains(addr@.au));
                    assert(addresses_in_aus(owned).contains(addr@));
                    assert(addr@ != spec_superblock_addr());
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.outstanding_requests_wf());
                    assert(self.state() == old(self).state());
                    assert(self.phase_alignment());
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.cache_read_io_lag_inv());
                }
                self.issue_acquired_cache_read_io(
                    addr,
                    handle,
                    CacheReadPurpose::CompactionDiscovery,
                    api,
                )
            },
            CompactionPickerStepResult::NoCandidate => {
                proof {
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.outstanding_requests_wf());
                    assert(self.state() == old(self).state());
                    assert(self.phase_alignment());
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv());
                    assert(self.inv_api(api));
                }
                true
            },
            CompactionPickerStepResult::InvalidPage => {
                proof {
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.outstanding_requests_wf());
                    assert(self.state() == old(self).state());
                    assert(self.phase_alignment());
                    assert(self.common_inv()) by {
                        reveal(Implementation::common_inv);
                    }
                    assert(self.inv());
                    assert(self.inv_api(api));
                }
                api.log("unified-cache Betree compaction picker found invalid page");
                true
            },
            CompactionPickerStepResult::CacheFull => {
                proof {
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.outstanding_requests_wf());
                    assert(self.inv_api(api));
                }
                false
            },
            CompactionPickerStepResult::Blocked => {
                proof {
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                    assert(self.outstanding_requests_wf());
                    assert(self.inv_api(api));
                }
                false
            },
        }
    }

    pub fn ready_background_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (result: ReadyBackgroundStepResult)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        if !self.outstanding_requests.is_empty() {
            return ReadyBackgroundStepResult::Idle;
        }
        proof {
            assert(self.outstanding_requests@
                == Map::<ID, OutstandingReqInfo>::empty()) by {
                assert_maps_equal!(
                    self.outstanding_requests@,
                    Map::<ID, OutstandingReqInfo>::empty(),
                    id => {
                        if self.outstanding_requests@.contains_key(id) {
                            assert(!self.outstanding_requests@.is_empty());
                        }
                    }
                );
            }
        }

        match &self.sync_phase {
            BetreeSyncPhaseImpl::SuperblockWriteIssued { .. } => {
                proof { assert(false); }
                return ReadyBackgroundStepResult::Idle;
            },
            BetreeSyncPhaseImpl::Preparing {
                journal_ready: false,
                ..
            } => {
                if self.record_sync_journal_prepare(api) {
                    return ReadyBackgroundStepResult::Progress;
                }
                return ReadyBackgroundStepResult::Idle;
            },
            BetreeSyncPhaseImpl::Preparing {
                journal_ready: true,
                branch_ready: true,
                ..
            } => {
                if self.issue_sync_superblock_write(api) {
                    return ReadyBackgroundStepResult::Progress;
                }
                return ReadyBackgroundStepResult::Idle;
            },
            BetreeSyncPhaseImpl::Preparing {
                journal_ready: true,
                branch_ready: false,
                ..
            } => {
                if self.record_sync_branch_prepare(api) {
                    return ReadyBackgroundStepResult::Progress;
                }
                return ReadyBackgroundStepResult::Idle;
            },
            BetreeSyncPhaseImpl::None => {},
        }
        proof { assert(self.sync_phase is None); }

        if self.sync_requests.superblocking_reqs.len() > 0 {
            self.record_deliver_completed_sync_reply(api);
            return ReadyBackgroundStepResult::Progress;
        }

        if self.sync_requests.journal_cleaning_reqs.len() == 0
            && self.sync_requests.buffered_reqs.len() > 0
        {
            let next_cycle_is_store =
                self.sync_counter + 1 == STORE_SYNC_INTERVAL;
            if next_cycle_is_store && self.compaction_work.is_some() {
                let work = self.compaction_work.unwrap();
                match work.phase {
                    CompactionWorkPhase::Begin => {
                        self.compaction_work = None;
                        proof {
                            assert(self.compaction_executor_wf());
                            assert(self.common_inv());
                            assert(self.inv_api(api));
                        }
                        api.log(
                            "unified-cache Betree discarded queued compaction for store sync",
                        );
                        return ReadyBackgroundStepResult::Progress;
                    },
                    CompactionWorkPhase::AbortCompactor => {
                        self.record_compaction_abort_compactor(api);
                        return ReadyBackgroundStepResult::Progress;
                    },
                    CompactionWorkPhase::AbortBranch => {
                        self.record_compaction_abort_branch(api);
                        return ReadyBackgroundStepResult::Progress;
                    },
                    _ => {
                        self.compaction_work = Some(CompactionWorkItem {
                            phase: CompactionWorkPhase::AbortCompactor,
                            ..work
                        });
                        proof {
                            assert(self.compaction_executor_wf());
                            assert(self.common_inv());
                            assert(self.inv_api(api));
                        }
                        api.log(
                            "unified-cache Betree requested compaction abort for store sync",
                        );
                        return ReadyBackgroundStepResult::Progress;
                    },
                }
            }
            self.promote_buffered_sync_requests(api);
            return ReadyBackgroundStepResult::Progress;
        }

        match self.store_flush_phase {
            StoreFlushPhaseImpl::Pending => {
                self.record_store_flush_begin(api);
                return ReadyBackgroundStepResult::Progress;
            },
            StoreFlushPhaseImpl::Building { idx, seq_end } => {
                proof {
                    reveal(Implementation::store_flush_wf);
                    assert(idx < self.branch.wip_branches@.len());
                    assert(self.branch.wip_branches@[idx as int]
                        .bulk_builder is Some);
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty());
                }
                if self.branch.wip_branches[idx]
                    .mini_allocator.free_aus_below_threshold()
                {
                    if self.record_wip_branch_refill(idx, api) {
                        return ReadyBackgroundStepResult::Progress;
                    }
                    return ReadyBackgroundStepResult::Idle;
                }
                match self.branch.wip_branches[idx]
                    .bulk_builder.as_ref().unwrap()
                {
                    BulkBuilderImpl::Memtable { memtable } => {
                        match memtable.phase {
                            BranchBulkPhase::Leaves
                            | BranchBulkPhase::Index => {
                                if self.record_store_stage_page(idx, api) {
                                    return ReadyBackgroundStepResult::Progress;
                                }
                            },
                            BranchBulkPhase::ReadyLeafRoot
                            | BranchBulkPhase::ReadyIndexRoot => {
                                if self.record_store_bulk_seal(
                                    idx,
                                    seq_end,
                                    api,
                                ) {
                                    return ReadyBackgroundStepResult::Progress;
                                }
                            },
                            BranchBulkPhase::Sealed => {
                                if self.record_store_branch_abort(idx, api) {
                                    return ReadyBackgroundStepResult::Progress;
                                }
                            },
                        }
                    },
                    BulkBuilderImpl::Streaming { .. } => {
                        proof { assert(false); }
                    },
                }
                return ReadyBackgroundStepResult::Idle;
            },
            StoreFlushPhaseImpl::Sealed { idx, seq_end } => {
                if self.record_store_install_root(idx, seq_end, api) {
                    return ReadyBackgroundStepResult::Progress;
                }
                return ReadyBackgroundStepResult::Idle;
            },
            StoreFlushPhaseImpl::Ready { seq_end } => {
                let marshalled = self.journal.exec_marshaled_seq_end();
                if marshalled < seq_end {
                    if self.record_journal_marshall_step(api) {
                        return ReadyBackgroundStepResult::Progress;
                    }
                    return ReadyBackgroundStepResult::Idle;
                }
                proof {
                    reveal(Implementation::store_flush_wf);
                    reveal(Implementation::phase_alignment);
                    self.journal.marshalled_seq_end_le_seq_end();
                    self.journal.view_seq_end_ensures();
                    assert(marshalled as nat
                        == self.journal.marshalled_seq_end());
                    assert(self.state().journal.journal.seq_end()
                        == self.state().branch.betree.memtable.seq_end);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().branch == self.branch@);
                    assert(self.journal.seq_end() == seq_end as nat);
                    assert(self.journal.marshalled_seq_end()
                        == seq_end as nat);
                }
                if self.record_store_sync_begin(seq_end, api) {
                    return ReadyBackgroundStepResult::Progress;
                }
                return ReadyBackgroundStepResult::Idle;
            },
            StoreFlushPhaseImpl::None => {},
        }
        proof { assert(self.store_flush_phase is None); }

        let active_sync = self.sync_requests.journal_cleaning_reqs.len() > 0;
        if active_sync {
            let target = self.sync_requests.sync_target_lsn;
            let marshalled = self.journal.exec_marshaled_seq_end();
            if marshalled < target {
                if self.record_journal_marshall_step(api) {
                    return ReadyBackgroundStepResult::Progress;
                }
            } else {
                let clean = self.journal.exec_clean_watermark();
                if clean < target {
                    if self.record_journal_writeback_for_target(target, api) {
                        return ReadyBackgroundStepResult::Progress;
                    }
                } else {
                    if self.compaction_work.is_some() {
                        let work = self.compaction_work.unwrap();
                        match work.phase {
                            CompactionWorkPhase::Begin => {
                                self.compaction_work = None;
                                proof {
                                    assert(self.compaction_executor_wf());
                                    assert(self.common_inv());
                                    assert(self.inv_api(api));
                                }
                                api.log(
                                    "unified-cache Betree discarded queued compaction for journal sync",
                                );
                                return ReadyBackgroundStepResult::Progress;
                            },
                            CompactionWorkPhase::AbortCompactor => {
                                self.record_compaction_abort_compactor(api);
                                return ReadyBackgroundStepResult::Progress;
                            },
                            CompactionWorkPhase::AbortBranch => {
                                self.record_compaction_abort_branch(api);
                                return ReadyBackgroundStepResult::Progress;
                            },
                            _ => {
                                self.compaction_work = Some(CompactionWorkItem {
                                    phase: CompactionWorkPhase::AbortCompactor,
                                    ..work
                                });
                                proof {
                                    assert(self.compaction_executor_wf());
                                    assert(self.common_inv());
                                    assert(self.inv_api(api));
                                }
                                api.log(
                                    "unified-cache Betree requested compaction abort for journal sync",
                                );
                                return ReadyBackgroundStepResult::Progress;
                            },
                        }
                    }
                    if self.record_journal_sync_begin(api) {
                        return ReadyBackgroundStepResult::Progress;
                    }
                    return ReadyBackgroundStepResult::Idle;
                }
            }
        }

        if self.journal.free_aus_below_threshold() {
            if self.record_journal_refill_for_ready(api) {
                return ReadyBackgroundStepResult::Progress;
            }
        }

        if active_sync {
            return ReadyBackgroundStepResult::Idle;
        }

        if self.compaction_work.is_some() {
            let work = self.compaction_work.unwrap();
            let made_progress = match work.phase {
                CompactionWorkPhase::Begin => {
                    self.record_compaction_begin(api)
                },
                CompactionWorkPhase::OutputCreation => {
                    self.record_compaction_output_begin(api)
                },
                CompactionWorkPhase::InitializeCursors => {
                    self.record_compaction_initialize_cursors(api)
                },
                CompactionWorkPhase::Scanning
                | CompactionWorkPhase::FinishingInput
                | CompactionWorkPhase::FinishingLevels => {
                    let output_idx = work.output_idx.unwrap();
                    if self.branch.wip_branches[output_idx]
                        .mini_allocator.free_aus_below_threshold()
                    {
                        self.record_wip_branch_refill(output_idx, api)
                    } else {
                        let page_ready = match self.branch.wip_branches[
                            output_idx
                        ].bulk_builder.as_ref().unwrap() {
                            BulkBuilderImpl::Streaming { streaming } => {
                                streaming.pending.is_some()
                            },
                            BulkBuilderImpl::Memtable { .. } => {
                                proof { assert(false); }
                                false
                            },
                        };
                        if page_ready {
                            self.record_compaction_stage_page(api)
                        } else {
                            match work.phase {
                                CompactionWorkPhase::Scanning => {
                                    proof {
                                        reveal(Implementation::compaction_executor_wf);
                                        assert(output_idx == 0);
                                        assert(self.branch.wip_branches@[
                                            output_idx as int
                                        ].has_streaming_builder());
                                        assert(self.branch.wip_branches@[
                                            output_idx as int
                                        ].streaming_builder().pending is None);
                                    }
                                    self.record_compaction_scan_step(api)
                                },
                                CompactionWorkPhase::FinishingInput => {
                                    proof {
                                        reveal(Implementation::compaction_executor_wf);
                                        assert(output_idx == 0);
                                        assert(self.branch.wip_branches@[
                                            output_idx as int
                                        ].has_streaming_builder());
                                        assert(self.branch.wip_branches@[
                                            output_idx as int
                                        ].streaming_builder().pending is None);
                                        assert(self.branch.wip_branches@[
                                            output_idx as int
                                        ].streaming_builder().local_wf());
                                        self.branch.wip_branches@[
                                            output_idx as int
                                        ].streaming_builder()
                                            .pending_none_has_no_deferred();
                                    }
                                    self.record_compaction_finish_input(api)
                                },
                                CompactionWorkPhase::FinishingLevels => {
                                    proof {
                                        reveal(Implementation::compaction_executor_wf);
                                        assert(output_idx == 0);
                                        assert(self.branch.wip_branches@[
                                            output_idx as int
                                        ].has_streaming_builder());
                                        assert(self.branch.wip_branches@[
                                            output_idx as int
                                        ].streaming_builder().pending is None);
                                        assert(self.branch.wip_branches@[
                                            output_idx as int
                                        ].streaming_builder().local_wf());
                                        self.branch.wip_branches@[
                                            output_idx as int
                                        ].streaming_builder()
                                            .pending_none_has_no_deferred();
                                    }
                                    self.record_compaction_finish_level(api)
                                },
                                _ => {
                                    proof { assert(false); }
                                    false
                                },
                            }
                        }
                    }
                },
                CompactionWorkPhase::Sealing => {
                    let output_idx = work.output_idx.unwrap();
                    if self.branch.wip_branches[output_idx]
                        .mini_allocator.free_aus_below_threshold()
                    {
                        self.record_wip_branch_refill(output_idx, api)
                    } else {
                        self.record_compaction_bulk_seal(api)
                    }
                },
                CompactionWorkPhase::Completing => {
                    self.record_compaction_complete(api)
                },
                CompactionWorkPhase::AbortCompactor => {
                    self.record_compaction_abort_compactor(api)
                },
                CompactionWorkPhase::AbortBranch => {
                    self.record_compaction_abort_branch(api)
                },
            };
            if made_progress {
                return ReadyBackgroundStepResult::Progress;
            }
            return ReadyBackgroundStepResult::Idle;
        }

        if !self.compaction_candidates.is_empty() {
            let admitted = self.record_compaction_admit(api);
            if admitted {
                return ReadyBackgroundStepResult::Progress;
            }
            proof {
                assert(self.outstanding_requests@
                    == Map::<ID, OutstandingReqInfo>::empty());
            }
        } else {
            let picker_progress = self.record_compaction_picker_step(api);
            if picker_progress {
                return ReadyBackgroundStepResult::Progress;
            }
            proof {
                assert(self.outstanding_requests@
                    == Map::<ID, OutstandingReqInfo>::empty());
            }
        }

        let seq_end = self.journal.exec_seq_end();
        let marshalled = self.journal.exec_marshaled_seq_end();
        if marshalled < seq_end {
            if self.record_journal_marshall_step(api) {
                return ReadyBackgroundStepResult::Progress;
            }
        }

        let clean = self.journal.exec_clean_watermark();
        let current_marshaled = self.journal.exec_marshaled_seq_end();
        if clean < current_marshaled {
            if self.record_journal_writeback_for_target(
                current_marshaled,
                api,
            ) {
                return ReadyBackgroundStepResult::Progress;
            }
        }

        ReadyBackgroundStepResult::Idle
    }

    pub fn ready_client_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (result: ReadyClientStepResult)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        if !self.outstanding_requests.is_empty() {
            return ReadyClientStepResult::Idle;
        }
        if self.pending_client_op.is_some() {
            if self.continue_pending_client_op(api) {
                return ReadyClientStepResult::Progress;
            }
            return ReadyClientStepResult::Idle;
        }

        let received = api.receive_request(true);
        match received {
            None => ReadyClientStepResult::Idle,
            Some(UserRequestRecord { request: req, token: req_shard }) => {
                proof {
                    assert(self.outstanding_requests@
                        == Map::<ID, OutstandingReqInfo>::empty()) by {
                        assert_maps_equal!(
                            self.outstanding_requests@,
                            Map::<ID, OutstandingReqInfo>::empty(),
                            id => {
                                if self.outstanding_requests@
                                    .contains_key(id)
                                {
                                    assert(!self.outstanding_requests@
                                        .is_empty());
                                }
                            }
                        );
                    }
                }
                match req.input {
                    Input::NoopInput => {
                        self.record_execute_noop(req, req_shard, api);
                        ReadyClientStepResult::Progress
                    },
                    Input::PutInput { key, value } => {
                        self.record_execute_put(
                            req,
                            req_shard,
                            key,
                            value,
                            api,
                        );
                        ReadyClientStepResult::Progress
                    },
                    Input::QueryInput { key } => {
                        self.record_execute_query(
                            req,
                            req_shard,
                            key,
                            api,
                        );
                        ReadyClientStepResult::Progress
                    },
                    Input::SyncInput => {
                        self.record_accept_sync_request(req, req_shard, api);
                        ReadyClientStepResult::Progress
                    },
                    Input::SimulateCrash => {
                        proof { assert(self.inv_api(api)); }
                        ReadyClientStepResult::ExitRequested
                    },
                }
            },
        }
    }

    pub fn recover_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheBetreeProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is FetchingSuperblock ==>
                old(self).state().recovery_state is AwaitingSuperblock,
        ensures
            self.inv_api(api),
            !(self.recovery_phase is FetchingSuperblock),
            old(self).recovery_phase is FetchingSuperblock
                ==> self.recovery_phase is LoadingJournal,
    {
        match self.recovery_phase {
            RecoveryPhase::FetchingSuperblock => {
                self.recover_superblock_step(api)
            },
            RecoveryPhase::LoadingJournal => {
                self.recover_journal_step(api)
            },
            RecoveryPhase::LoadingBranch => {
                self.recover_branch_step(api)
            },
            RecoveryPhase::ReplayingJournal => {
                self.recover_replay_step(api)
            },
            RecoveryPhase::ReadyForUserOperation => false,
        }
    }

    fn zip_keyed_messages(
        keys: &Vec<Key>,
        messages: &Vec<Message>,
        start_lsn: u64,
    ) -> (out: Vec<KeyedMessage>)
        requires keys@.len() == messages@.len(),
        ensures
            out@.len() == keys@.len(),
            forall |index: int| #![trigger out@[index]]
                0 <= index < out@.len()
                ==> out@[index] == (KeyedMessage {
                    key: keys@[index],
                    message: messages@[index],
                }),
            MemtableImpl::history_from_seq(start_lsn as nat, out@)
                == append_puts(start_lsn as nat, keys@, messages@),
    {
        let mut out = Vec::<KeyedMessage>::new();
        let mut index = 0usize;
        while index < keys.len()
            invariant
                keys@.len() == messages@.len(),
                index <= keys.len(),
                out@.len() == index,
                forall |i: int| #![trigger out@[i]]
                    0 <= i < out@.len()
                    ==> out@[i] == (KeyedMessage {
                        key: keys@[i],
                        message: messages@[i],
                    }),
            decreases keys.len() - index,
        {
            out.push(KeyedMessage {
                key: keys[index],
                message: messages[index],
            });
            index += 1;
        }
        proof {
            assert_maps_equal!(
                MemtableImpl::history_from_seq(
                    start_lsn as nat,
                    out@,
                ).msgs,
                append_puts(
                    start_lsn as nat,
                    keys@,
                    messages@,
                ).msgs,
                lsn => {
                    if MemtableImpl::history_from_seq(
                        start_lsn as nat,
                        out@,
                    )
                        .msgs.contains_key(lsn)
                    {
                        let i = (lsn - start_lsn as nat) as int;
                        assert(out@[i] == (KeyedMessage {
                            key: keys@[i],
                            message: messages@[i],
                        }));
                    }
                }
            );
        }
        out
    }
}

impl KVStoreTrait for Implementation {
    type ProgramModel = UnifiedCacheBetreeProgramModel;
    type Proof = UnifiedCacheBetreeRefinementProof;

    closed spec fn wf_init(self) -> bool {
        Implementation::wf_init(&self)
    }

    closed spec fn instance_id(self) -> InstanceId {
        Implementation::instance_id(&self)
    }

    fn configured_disk_geometry() -> (out: IDiskGeometry) {
        IDiskGeometry {
            physical_au_count: DEFAULT_PHYSICAL_AUS,
            pages_per_au: IMPLEMENTATION_PAGES_PER_AU,
        }
    }

    fn new(geometry: IDiskGeometry) -> (out: Self) {
        Implementation::new(geometry)
    }

    fn kvstore_mkfs(
        &mut self,
        mut api: ClientAPI<Self::ProgramModel>,
    ) {
        let layout = DiskLayout::new();
        let superblock = layout.exec_mkfs(
            self.disk_au_count,
            self.disk_page_count,
        );
        api.format_storage(superblock);
        api.log("unified-cache Betree mkfs complete");
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn kvstore_main(
        &mut self,
        mut api: ClientAPI<Self::ProgramModel>,
    ) {
        self.recover_begin(&mut api);

        loop
            invariant
                self.inv_api(&api),
                self.recovery_phase is FetchingSuperblock
                    ==> self.state().recovery_state is AwaitingSuperblock,
        {
            let mut progress = false;

            match self.recovery_phase {
                RecoveryPhase::FetchingSuperblock => {},
                RecoveryPhase::LoadingJournal
                | RecoveryPhase::LoadingBranch
                | RecoveryPhase::ReplayingJournal
                | RecoveryPhase::ReadyForUserOperation => {
                    match api.receive_disk_response() {
                        None => {},
                        Some(rec) => {
                            self.handle_disk_response(rec, &mut api);
                            progress = true;
                        },
                    }
                },
            }

            match self.recovery_phase {
                RecoveryPhase::FetchingSuperblock
                | RecoveryPhase::LoadingJournal
                | RecoveryPhase::LoadingBranch
                | RecoveryPhase::ReplayingJournal => {
                    let recovery_progress = self.recover_step(&mut api);
                    progress = recovery_progress || progress;
                },
                RecoveryPhase::ReadyForUserOperation => {
                    match self.ready_client_step(&mut api) {
                        ReadyClientStepResult::Progress => {
                            progress = true;
                        },
                        ReadyClientStepResult::Idle => {},
                        ReadyClientStepResult::ExitRequested => {
                            return;
                        },
                    }

                    match self.ready_background_step(&mut api) {
                        ReadyBackgroundStepResult::Progress => {
                            progress = true;
                        },
                        ReadyBackgroundStepResult::Idle => {},
                    }
                },
            }

            if !progress {
                api.log("sleeping");
                api.sleep_a_little();
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////
// Utility proofs
///////////////////////////////////////////////////////////////////////////////

impl Implementation {
    pub proof fn model_alignment_facts(&self)
        requires self.inv(),
        ensures
            self.model@.value().state == self.state(),
            self.cache.wf(),
            self.journal.basic_wf(),
            self.branch.wf(),
            self.state().cache == self.cache@,
            self.state().journal.journal == self.journal@,
            self.state().journal.mini_allocator
                == self.journal.journal_alloc.i(),
            self.state().journal.persistent_seq_end
                == self.persistent_journal_seq_end as nat,
            self.state().branch == self.branch@,
            self.state().free_aus =~= self.au_pool@,
            self.recovery_phase is ReadyForUserOperation
                ==> self.state().client_ready(),
            self.state().client_ready()
                ==> self.recovery_phase is ReadyForUserOperation,
            self.recovery_phase is ReadyForUserOperation ==> {
                &&& self.journal.index_ready()
                &&& self.journal.index_aus_bounded(self.disk_au_count)
                &&& self.branch_owned_aus_bounded()
            },
            self.recovery_phase is LoadingBranch ==> {
                &&& !(self.state().recovery_state is Begin)
                &&& !(self.state().recovery_state is AwaitingSuperblock)
            },
            self.sync_phase is SuperblockWriteIssued
                ==> self.state().sync_phase is SuperblockWriteIssued,
    {
        reveal(Implementation::inv);
        reveal(Implementation::common_inv);
        reveal(Implementation::phase_alignment);
        reveal(Implementation::sync_wf);
    }

    proof fn singleton_updated_addr_map(
        id: ID,
        req: DiskRequest,
        addr: Address,
    )
        requires req.addr() == addr,
        ensures
            Map::new(
                |candidate| map![id => req].contains_key(candidate),
                |candidate| map![id => req][candidate].addr(),
            ) == map![id => addr],
    {
        let updated = Map::new(
            |candidate| map![id => req].contains_key(candidate),
            |candidate| map![id => req][candidate].addr(),
        );
        assert_maps_equal!(updated, map![id => addr], candidate => {
            if candidate == id {
                assert(updated[candidate] == req.addr());
            }
        });
    }

    proof fn cache_resps_singleton(
        pre_cache_reqs: Map<ID, Address>,
        id: ID,
        addr: Address,
        resp: DiskResponse,
    )
        requires pre_cache_reqs == map![id => addr],
        ensures ({
            let resp_map = map![id => resp];
            let finished = pre_cache_reqs
                .restrict(resp_map.dom())
                .invert();
            let cache_resps = Map::new(
                |candidate| finished.contains_key(candidate),
                |candidate| resp_map[finished[candidate]],
            );
            cache_resps == map![addr => resp]
        }),
    {
        let resp_map = map![id => resp];
        let restricted = pre_cache_reqs.restrict(resp_map.dom());
        assert_maps_equal!(restricted, map![id => addr], key => {
            if key == id {
                assert(resp_map.dom().contains(key));
            }
        });
        let finished = restricted.invert();
        assert_maps_equal!(finished, map![addr => id], candidate => {
            if candidate == addr {
                assert(restricted.contains_pair(id, addr));

            } else {
                assert(!restricted.contains_value(candidate));

            }
        });
        let cache_resps = Map::new(
            |candidate| finished.contains_key(candidate),
            |candidate| resp_map[finished[candidate]],
        );
        assert_maps_equal!(cache_resps, map![addr => resp], candidate => {
            if candidate == addr {
                assert(finished[candidate] == id);
            }
        });
    }

    proof fn disk_response_inv_facts(
        &self,
        api: &ClientAPI<UnifiedCacheBetreeProgramModel>,
    )
        requires self.inv_api(api),
        ensures
            self.inv(),
            self.common_inv(),
            self.cache.wf(),
            self.branch.wf(),
            self.journal.basic_wf(),
            self.outstanding_requests_wf(),
            self.outstanding_cache_reqs_match_model(),
            self.outstanding_requests_single_flight(),
            self.sync_wf(),
            self.store_flush_wf(),
            self.phase_alignment(),
            self.state().cache == self.cache@,
            forall |id: ID|
                #[trigger] self.outstanding_requests@.contains_key(id)
                ==> !(self.state().recovery_state is Begin)
                    && !(self.state().recovery_state is AwaitingSuperblock),
    {
        reveal(Implementation::inv_api);
        reveal(Implementation::inv);
        reveal(Implementation::common_inv);
    }

    proof fn common_inv_after_cache_io(
        pre: &Implementation,
        post: &Implementation,
    )
        requires
            pre.common_inv(),
            Self::same_non_cache_io_state(pre, post),
            post.model@.instance_id() == post.instance@.id(),
            post.cache.wf(),
            post.outstanding_requests_wf(),
            post.outstanding_cache_reqs_match_model(),
            post.outstanding_requests_single_flight(),
            post.sync_wf(),
            post.store_flush_wf(),
            post.phase_alignment(),
            post.compaction_executor_wf(),
            post.compaction_candidates.wf(),
            post.compaction_candidates.capacity
                == COMPACTION_CANDIDATE_CAPACITY,
            forall |i: int|
                0 <= i < post.compaction_candidates.entries@.len()
                ==> (#[trigger] post.compaction_candidates.entries@[i]).fuel
                    == CACHE_SIZE_RECS,
            post.compaction_picker.wf(),
            forall |id: ID|
                #[trigger] post.outstanding_requests@.contains_key(id)
                ==> !(post.state().recovery_state is Begin)
                    && !(post.state().recovery_state is AwaitingSuperblock),
        ensures post.common_inv(),
    {
        reveal(Implementation::common_inv);
        reveal(Implementation::outstanding_requests_wf);
        reveal(Implementation::pending_client_op_wf);
        reveal(Implementation::branch_owned_aus_bounded);
    }

    proof fn common_inv_after_journal_sync(
        pre: &Implementation,
        post: &Implementation,
    )
        requires
            pre.common_inv(),
            Self::same_journal_sync_stable_state(pre, post),
            post.model@.instance_id() == post.instance@.id(),
            post.journal.basic_wf(),
            post.journal.journal_alloc.bounded(post.disk_au_count),
            MiniAllocatorImpl::allocators_unique(
                post.journal.journal_alloc.allocators@,
            ),
            post.journal.allocator_index_aligned(),
            post.au_pool@.disjoint(post.journal.owned_aus()),
            post.state().journal.journal == post.journal@,
            post.state().journal.mini_allocator
                == post.journal.journal_alloc.i(),
            post.state().journal.persistent_seq_end
                == post.persistent_journal_seq_end as nat,
            post.outstanding_requests_wf(),
            post.outstanding_cache_reqs_match_model(),
            post.outstanding_requests_single_flight(),
            post.sync_wf(),
            post.store_flush_wf(),
            post.phase_alignment(),
            post.compaction_executor_wf(),
            forall |id: ID|
                #[trigger] post.outstanding_requests@.contains_key(id)
                ==> !(post.state().recovery_state is Begin)
                    && !(post.state().recovery_state is AwaitingSuperblock),
        ensures post.common_inv(),
    {
        reveal(Implementation::common_inv);
        reveal(Implementation::outstanding_requests_wf);
        reveal(Implementation::pending_client_op_wf);
        reveal(Implementation::branch_owned_aus_bounded);
    }

    proof fn compaction_executor_wf_frame(
        pre: &Implementation,
        post: &Implementation,
    )
        requires
            pre.compaction_executor_wf(),
            post.compaction_work == pre.compaction_work,
            post.recovery_phase == pre.recovery_phase,
            post.sync_phase == pre.sync_phase,
            post.store_flush_phase == pre.store_flush_phase,
            post.disk_au_count == pre.disk_au_count,
            post.branch == pre.branch,
            post.journal.owned_aus() == pre.journal.owned_aus(),
            match post.compaction_work {
                Some(work) if work.output_idx == Some(0usize) =>
                    post.branch.wip_branches@[0]
                        .cache_inv(post.cache@),
                _ => true,
            },
            match post.compaction_work {
                Some(work) if work.phase is Scanning =>
                    post.branch.compactors@[0]
                        .cache_inv(post.cache@),
                _ => true,
            },
        ensures post.compaction_executor_wf(),
    {
        reveal(Implementation::compaction_executor_wf);
    }
}

} // verus!
