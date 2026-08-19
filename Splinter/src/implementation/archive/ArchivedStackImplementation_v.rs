// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause

// Unified-cache implementation scaffold.
//
// The active code below rebuilds the entry shape against UnifiedCacheProgramModel.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;
use vstd::hash_map::HashMapWithView;
use vstd::modes::tracked_swap;
use vstd::multiset::Multiset;
use vstd::tokens::InstanceId;
use vstd::pervasive::unreached;

use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::disk::GenericDisk_v::{Address, AU, page_count, to_aus, to_aus_domain};
use crate::implementation::MultisetMapRelation_v::{
    multiset_map_singleton, multiset_map_singleton_ensures, multiset_to_map,
};
use crate::implementation::AbstractSuperblock_v::{
    abstract_superblock_raw_wf, superblock_matches,
};
use crate::implementation::AllocationBranchStackRefinement_v::{append_puts, append_puts_wf};
use crate::implementation::AllocationBranchStack_v::normalize_value;
use crate::implementation::AtomicBranchState_v::{AtomicBranchState, to_branch_nodes};
use crate::implementation::AtomicJournalState_v::{AtomicJournalImage, AtomicJournalState};
use crate::implementation::AuPoolImpl_v::{iau_vec_set, AuPoolImpl};
use crate::implementation::BranchStackImpl_v::{
    branch_stack_store_addrs_safe, branch_store_cache_read_aligned,
    BranchImageImpl, BranchMaintenanceResult, BranchMetadataReadKind, BranchMetadataStepResult,
    BranchQueryResult, BranchReplayAppendResult, BranchSealResult, BranchStackImpl, CommitPhase,
    BRANCH_FREE_AU_THRESHOLD,
};
use crate::implementation::CachingDiskBranch_v::{
    sealed_summary_aus_between, sealed_summary_aus_between_last_subset,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CachingDisk_v::addresses_in_aus;
use crate::implementation::CachedBranch_v::CachedBranch;
use crate::implementation::CachedJournal_v::{
    build_au_page_bounds_from_reads_au_walk_depth, CachedJournal,
};
use crate::implementation::CrashAwareCachingDiskSystemRefinement_v as CachingDiskSystemRefinement;
use crate::implementation::DiskLayout_v::{DiskLayout, spec_superblock_addr, superblock_addr};
use crate::implementation::FracCacheImpl_v::{
    cache_load_label, FetchErrorCode, FracCacheImpl, MutHandle, WritebackAcquireResult, WritebackHandle,
    PAGE_SIZE_BYTES,
};
use crate::implementation::IBranchNode_v::iau_seq_set;
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_filled_page, filled_cache_pages, project_cache_pages, projectable_entry_in_caching_disk_i,
};
use crate::implementation::JournalImpl_v::{
    cache_agrees_with_raw_disk_on_domain, journal_disk_inv, journal_disk_load_index_inv,
    BeginWritebackForTargetResult, CleanForCommitResult, FrozenJournal, MarshalReserveResult,
    load_index_labels, map_recovery_labels, IJournalSnapshot, JournalImpl,
    UnifiedRecoverIndexResult, UnifiedRecoverMapResult,
};
use crate::implementation::SuperblockTypes_v::{
    ISuperblock, ISuperblockBetreeImage, ISuperblockBranchImage,
    ISuperblockJournalImage,
};
use crate::implementation::JournalTypes_v::{journal_marshall_labels, to_journal_records};
use crate::implementation::MiniAllocatorImpl_v::MiniAllocatorImpl;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::implementation::UnifiedCacheProgramModel_v::UnifiedCacheProgramModel;
use crate::implementation::UnifiedCacheJournalRefinement_v as UnifiedCacheJournalRefinement;
use crate::implementation::UnifiedCacheSystemRefinement_v as UnifiedCacheSystemRefinement;
use crate::implementation::UnifiedCacheSystem_v::{
    AtomicSyncPhase, UnifiedCacheSystem, valid_request_reply_pair,
};
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::ImplDisk_t::{IAddress, IAU, IPage, IDiskGeometry, IDiskRequest, IDiskResponse};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{CrashTolerantAsyncMap, ID, SyncReqId};
use crate::spec::Messages_t::{Message, Value};
use crate::trusted::ClientAPI_t::{ClientAPI, DiskResponseRecord};
use crate::trusted::KVStoreTrait_t::{
    KVStoreTrait, open_system_invariant_disk_response, open_system_invariant_disk_response_singleton,
};
use crate::trusted::KVStoreTokenized_t::KVStoreTokenized;
use crate::trusted::ProgramModelTrait_t::{ProgramDiskInfo, ProgramLabel, ProgramModelTrait, ProgramUserOp};
use crate::trusted::RefinementObligation_t::RefinementObligation;
use crate::trusted::ReqReply_t::{Input, Output, Reply, Request};
use crate::trusted::SystemModel_t::SystemModel;
use crate::journal::LinkedJournal_v::{DiskView, TruncatedJournal};

verus! {

pub const DEFAULT_PHYSICAL_AUS: IAU = 100;
pub const IMPLEMENTATION_PAGES_PER_AU: IPage = 7;

pub fn bootstrap_alloc_au(disk_au_count: IAU) -> (out: IAU)
    requires
        1 < (disk_au_count as nat),
    ensures
        0 < (out as nat),
        (out as nat) < (disk_au_count as nat),
{
    1
}

pub type ModelShard = KVStoreTokenized::model<UnifiedCacheProgramModel>;
pub type RequestShard = KVStoreTokenized::requests<UnifiedCacheProgramModel>;
pub type DiskRespShard = KVStoreTokenized::disk_responses_multiset<UnifiedCacheProgramModel>;

pub struct UnifiedCacheRefinementProof;

#[derive(Debug, Copy, Clone)]
pub enum RecoveryPhase {
    FetchingSuperblock,
    LoadingJournal,
    LoadingBranch,
    ReplayingJournal,
    ReadyForUserOperation,
}

pub enum OutstandingReqInfo {
    CacheRead{addr: IAddress, load_handle: MutHandle, purpose: CacheReadPurpose},
    CacheWrite{addr: IAddress, write_handle: WritebackHandle},
    SuperblockWrite,
}

#[derive(Clone, Copy, Debug)]
pub enum CacheReadPurpose {
    Generic,
    JournalIndex,
    SyncJournalRoot,
    BranchMetadata { kind: BranchMetadataReadKind },
}

pub enum PendingUserOp {
    Put{req: Request, req_shard: Tracked<RequestShard>, key: Key, value: Value},
    Query{req: Request, req_shard: Tracked<RequestShard>, key: Key},
}

pub const BRANCH_SYNC_INTERVAL: u64 = 3;

#[derive(Clone, Copy, Debug)]
pub enum SyncFlavor {
    JournalOnly,
    BranchAndEmptyJournal,
}

pub enum PendingBranchSync {
    SealPending,
    Persisting {
        target_root_count: usize,
        summary_aus: Vec<IAU>,
    },
    Ready,
}

pub struct SyncRequestBuffer {
    pub buffered_reqs: Vec<SyncReqId>,
    pub journal_cleaning_reqs: Vec<SyncReqId>,
    pub superblocking_reqs: Vec<SyncReqId>,
    pub sync_target_lsn: u64,
}

impl SyncRequestBuffer {
    fn vec_contains_id(ids: &Vec<SyncReqId>, id: SyncReqId) -> (out: bool)
        ensures
            out <==> ids@.contains(id),
    {
        let mut i = 0usize;
        while i < ids.len()
            invariant
                i <= ids.len(),
                forall |j: int| 0 <= j < i ==> ids@[j] != id,
            decreases ids.len() - i,
        {
            if ids[i] == id {
                return true;
            }
            i += 1;
        }
        false
    }

    pub fn contains_id(&self, id: SyncReqId) -> (out: bool)
        ensures
            out <==> self.all_ids().to_set().contains(id),
    {
        let in_cleaning = Self::vec_contains_id(&self.journal_cleaning_reqs, id);
        let in_superblocking = Self::vec_contains_id(&self.superblocking_reqs, id);
        let in_buffered = Self::vec_contains_id(&self.buffered_reqs, id);
        let out = in_cleaning || in_superblocking || in_buffered;
        proof {
            if out {
                if in_cleaning {
                    assert(self.journal_cleaning_reqs@.contains(id));
                    let i = choose |i: int| 0 <= i < self.journal_cleaning_reqs@.len()
                        && self.journal_cleaning_reqs@[i] == id;
                    assert(self.all_ids()[i] == id);
                    assert(self.all_ids().contains(id));
                } else if in_superblocking {
                    assert(self.superblocking_reqs@.contains(id));
                    let i = choose |i: int| 0 <= i < self.superblocking_reqs@.len()
                        && self.superblocking_reqs@[i] == id;
                    let j = self.journal_cleaning_reqs@.len() as int + i;
                    assert(self.all_ids()[j] == id);
                    assert(self.all_ids().contains(id));
                } else {
                    assert(self.buffered_reqs@.contains(id));
                    let i = choose |i: int| 0 <= i < self.buffered_reqs@.len()
                        && self.buffered_reqs@[i] == id;
                    let j = self.journal_cleaning_reqs@.len() as int
                        + self.superblocking_reqs@.len() as int + i;
                    assert(self.all_ids()[j] == id);
                    assert(self.all_ids().contains(id));
                }
                assert(self.all_ids().to_set().contains(id));
            }
        }
        out
    }

    pub open spec fn all_ids(&self) -> Seq<SyncReqId>
    {
        self.journal_cleaning_reqs@ + self.superblocking_reqs@ + self.buffered_reqs@
    }

    pub open spec fn ids_unique(&self) -> bool
    {
        forall |i: int, j: int| {
            &&& 0 <= i < self.all_ids().len()
            &&& 0 <= j < self.all_ids().len()
            &&& self.all_ids()[i] == self.all_ids()[j]
        } ==> i == j
    }

    pub fn new_empty() -> (out: Self)
        ensures
            out.all_ids() == Seq::<SyncReqId>::empty(),
            out.ids_unique(),
            out.sync_target_lsn == 0,
    {
        SyncRequestBuffer {
            buffered_reqs: Vec::new(),
            journal_cleaning_reqs: Vec::new(),
            superblocking_reqs: Vec::new(),
            sync_target_lsn: 0,
        }
    }

    pub fn promote_buffered(&mut self, target_lsn: u64)
        requires
            old(self).journal_cleaning_reqs@.len() == 0,
            old(self).superblocking_reqs@.len() == 0,
        ensures
            self.buffered_reqs@.len() == 0,
            self.journal_cleaning_reqs@ == old(self).buffered_reqs@,
            self.superblocking_reqs@.len() == 0,
            self.sync_target_lsn == target_lsn,
            self.all_ids() == old(self).all_ids(),
            old(self).ids_unique() ==> self.ids_unique(),
    {
        self.sync_target_lsn = target_lsn;
        core::mem::swap(&mut self.buffered_reqs, &mut self.journal_cleaning_reqs);
        proof {
            if old(self).ids_unique() {
                assert(self.ids_unique()) by {
                    assert forall |i: int, j: int| {
                        &&& 0 <= i < self.all_ids().len()
                        &&& 0 <= j < self.all_ids().len()
                        &&& self.all_ids()[i] == self.all_ids()[j]
                    } implies i == j by {
                        assert(self.all_ids() == old(self).all_ids());
                    }
                }
            }
        }
    }

    pub fn raise_cleaning_target(&mut self, target_lsn: u64)
        requires
            old(self).journal_cleaning_reqs@.len() > 0,
            old(self).sync_target_lsn <= target_lsn,
            old(self).ids_unique(),
        ensures
            self.buffered_reqs@ == old(self).buffered_reqs@,
            self.journal_cleaning_reqs@ == old(self).journal_cleaning_reqs@,
            self.superblocking_reqs@ == old(self).superblocking_reqs@,
            self.sync_target_lsn == target_lsn,
            self.all_ids() == old(self).all_ids(),
            self.ids_unique(),
    {
        self.sync_target_lsn = target_lsn;
    }

    pub fn push_buffered(&mut self, id: SyncReqId)
        requires
            old(self).ids_unique(),
            !old(self).all_ids().to_set().contains(id),
        ensures
            self.buffered_reqs@ == old(self).buffered_reqs@.push(id),
            self.journal_cleaning_reqs@ == old(self).journal_cleaning_reqs@,
            self.superblocking_reqs@ == old(self).superblocking_reqs@,
            self.sync_target_lsn == old(self).sync_target_lsn,
            self.all_ids() == old(self).all_ids().push(id),
            self.all_ids().to_set() =~= old(self).all_ids().to_set().insert(id),
            self.ids_unique(),
    {
        self.buffered_reqs.push(id);
        proof {
            assert(self.all_ids() == old(self).all_ids().push(id));
            assert forall |x: SyncReqId| #[trigger] self.all_ids().to_set().contains(x)
                <==> old(self).all_ids().to_set().insert(id).contains(x) by {
                if self.all_ids().to_set().contains(x) {
                    let i = choose |i: int| 0 <= i < self.all_ids().len()
                        && self.all_ids()[i] == x;
                    if i < old(self).all_ids().len() {
                        assert(old(self).all_ids().to_set().contains(x));
                    } else {
                        assert(i == old(self).all_ids().len());
                        assert(x == id);
                    }
                } else if old(self).all_ids().to_set().insert(id).contains(x) {
                    if x == id {
                        assert(self.all_ids()[old(self).all_ids().len() as int] == id);
                    } else {
                        assert(old(self).all_ids().to_set().contains(x));
                        let i = choose |i: int| 0 <= i < old(self).all_ids().len()
                            && old(self).all_ids()[i] == x;
                        assert(self.all_ids()[i] == x);
                    }
                    assert(false);
                }
            }
            assert forall |i: int, j: int| {
                &&& 0 <= i < self.all_ids().len()
                &&& 0 <= j < self.all_ids().len()
                &&& self.all_ids()[i] == self.all_ids()[j]
            } implies i == j by {
                let old_len = old(self).all_ids().len();
                if i < old_len && j < old_len {
                    assert(old(self).all_ids()[i] == old(self).all_ids()[j]);
                    assert(i == j);
                } else if i == old_len && j == old_len {
                } else if i == old_len {
                    assert(self.all_ids()[i] == id);
                    assert(j < old_len);
                    assert(old(self).all_ids()[j] == id);
                    assert(old(self).all_ids().to_set().contains(id));
                    assert(false);
                } else {
                    assert(j == old_len);
                    assert(self.all_ids()[j] == id);
                    assert(i < old_len);
                    assert(old(self).all_ids()[i] == id);
                    assert(old(self).all_ids().to_set().contains(id));
                    assert(false);
                }
            }
        }
    }

    pub fn move_cleaning_to_superblocking(&mut self)
        requires
            old(self).superblocking_reqs@.len() == 0,
        ensures
            self.buffered_reqs@ == old(self).buffered_reqs@,
            self.journal_cleaning_reqs@.len() == 0,
            self.superblocking_reqs@ == old(self).journal_cleaning_reqs@,
            self.sync_target_lsn == old(self).sync_target_lsn,
            self.all_ids() == old(self).all_ids(),
            old(self).ids_unique() ==> self.ids_unique(),
    {
        core::mem::swap(&mut self.journal_cleaning_reqs, &mut self.superblocking_reqs);
    }

    pub fn pop_superblocking(&mut self) -> (out: SyncReqId)
        requires
            old(self).superblocking_reqs@.len() > 0,
            old(self).ids_unique(),
        ensures
            self.buffered_reqs@ == old(self).buffered_reqs@,
            self.journal_cleaning_reqs@ == old(self).journal_cleaning_reqs@,
            self.superblocking_reqs@.push(out) == old(self).superblocking_reqs@,
            self.sync_target_lsn == old(self).sync_target_lsn,
            old(self).all_ids().to_set().contains(out),
            self.all_ids().to_set() =~= old(self).all_ids().to_set().remove(out),
            self.ids_unique(),
    {
        let out = self.superblocking_reqs.pop().unwrap();
        proof {
            let ghost old_ids = old(self).all_ids();
            let ghost new_ids = self.all_ids();
            let ghost old_super = old(self).superblocking_reqs@;
            let ghost new_super = self.superblocking_reqs@;
            assert(new_super.push(out) == old_super);
            let popped_idx = old(self).journal_cleaning_reqs@.len() as int
                + new_super.len() as int;
            assert(0 <= popped_idx < old_ids.len());
            assert(old_ids[popped_idx] == out);
            assert(old_ids.to_set().contains(out));

            assert forall |x: SyncReqId| #[trigger] new_ids.to_set().contains(x)
                implies old_ids.to_set().remove(out).contains(x) by {
                let i = choose |i: int| 0 <= i < new_ids.len() && new_ids[i] == x;
                if x == out {
                    if i < self.journal_cleaning_reqs@.len() {
                        assert(old_ids[i] == x);
                        assert(i != popped_idx);
                    } else if i < self.journal_cleaning_reqs@.len()
                        + self.superblocking_reqs@.len() {
                        assert(old_ids[i] == x);
                        assert(i != popped_idx);
                    } else {
                        let old_i = i + 1;
                        assert(old_i < old_ids.len());
                        assert(old_ids[old_i] == x);
                        assert(old_i != popped_idx);
                    }
                    assert(old(self).ids_unique());
                    assert(false);
                }
                if i < self.journal_cleaning_reqs@.len() {
                    assert(old_ids[i] == x);
                } else if i < self.journal_cleaning_reqs@.len()
                    + self.superblocking_reqs@.len() {
                    assert(old_ids[i] == x);
                } else {
                    let old_i = i + 1;
                    assert(old_i < old_ids.len());
                    assert(old_ids[old_i] == x);
                }
            }
            assert forall |x: SyncReqId| #[trigger] old_ids.to_set().remove(out).contains(x)
                implies new_ids.to_set().contains(x) by {
                let i = choose |i: int| 0 <= i < old_ids.len() && old_ids[i] == x;
                assert(x != out);
                if i < old(self).journal_cleaning_reqs@.len() {
                    assert(new_ids[i] == x);
                } else if i < old(self).journal_cleaning_reqs@.len()
                    + old_super.len() {
                    let super_i = i - old(self).journal_cleaning_reqs@.len();
                    if super_i == new_super.len() {
                        assert(old_ids[i] == out);
                        assert(false);
                    } else {
                        assert(super_i < new_super.len());
                        assert(new_ids[i] == x);
                    }
                } else {
                    let new_i = i - 1;
                    assert(0 <= new_i < new_ids.len());
                    assert(new_ids[new_i] == x);
                }
            }
            assert forall |i: int, j: int| {
                &&& 0 <= i < new_ids.len()
                &&& 0 <= j < new_ids.len()
                &&& new_ids[i] == new_ids[j]
            } implies i == j by {
                let old_i = if i < self.journal_cleaning_reqs@.len()
                    + self.superblocking_reqs@.len() { i } else { i + 1 };
                let old_j = if j < self.journal_cleaning_reqs@.len()
                    + self.superblocking_reqs@.len() { j } else { j + 1 };
                assert(0 <= old_i < old_ids.len());
                assert(0 <= old_j < old_ids.len());
                assert(old_ids[old_i] == new_ids[i]);
                assert(old_ids[old_j] == new_ids[j]);
                assert(old_i == old_j);
                assert(i == j);
            }
        }
        out
    }
}

pub struct InFlightSync {
    pub flavor: SyncFlavor,
    pub image: ISuperblock,
    pub req_id: ID,
    pub discarded_aus: Vec<IAU>,
}

pub struct Implementation {
    pub disk_au_count: IAU,
    pub disk_page_count: IPage,
    pub recovery_phase: RecoveryPhase,
    pub cache: FracCacheImpl,
    pub journal: JournalImpl,
    pub branch: BranchStackImpl,
    pub au_pool: AuPoolImpl,
    pub persistent_journal_seq_end: u64,
    pub sync_counter: u64,
    pub sync_requests: SyncRequestBuffer,
    pub pending_branch_sync: Option<PendingBranchSync>,
    pub in_flight_sync: Option<InFlightSync>,
    pub outstanding_requests: HashMapWithView<ID, OutstandingReqInfo>,
    pub pending_user_op: Option<PendingUserOp>,
    // Legacy implementation used a separate retry hint. Queue state is now the retry source.
    // pub should_retry_sync_launch: bool,

    pub model: Tracked<ModelShard>,
    pub instance: Tracked<KVStoreTokenized::Instance<UnifiedCacheProgramModel>>,
}

impl Implementation {
    pub closed spec fn state(&self) -> UnifiedCacheSystem::State
    {
        self.model@.value().state
    }

    pub closed spec fn instance_id(&self) -> InstanceId
    {
        self.instance@.id()
    }

    pub closed spec fn inv(&self) -> bool
    {
        &&& self.model@.instance_id() == self.instance@.id()
        &&& 1 < (self.disk_au_count as nat)
        &&& (self.disk_page_count as nat) == page_count()
        &&& 0 < (self.disk_page_count as nat)
        &&& self.cache.wf()
        &&& self.journal.basic_wf()
        &&& self.branch.wf()
        &&& self.au_pool.canonical_wf(self.disk_au_count)
        &&& self.state().cache == self.cache@
        &&& self.state().branch == self.branch@
        &&& self.state().free_aus =~= self.au_pool@
        &&& !(self.recovery_phase is FetchingSuperblock) ==>
            self.state().journal.persistent_seq_end == self.persistent_journal_seq_end as nat
        &&& self.outstanding_requests_wf()
        &&& self.outstanding_cache_reqs_match_model()
        &&& self.outstanding_requests_single_flight()
        &&& self.pending_user_op_wf()
        &&& self.sync_wf()
        &&& !(self.recovery_phase is FetchingSuperblock) ==>
            self.persistent_component_alignment()
        &&& (!(self.recovery_phase is ReadyForUserOperation) ==> self.recovery_sync_empty())
        &&& (!(self.recovery_phase is ReadyForUserOperation) ==>
            self.pending_user_op is None)
        &&& self.outstanding_requests@.dom().len() > 0 ==> {
            &&& !(self.state().recovery_state is Begin)
            &&& !(self.state().recovery_state is AwaitingSuperblock)
        }
        &&& self.recovery_phase is LoadingJournal ==> {
            &&& self.state().recovery_state is SuperblockAvailable
            &&& self.state().journal.journal == self.journal@
            &&& self.state().journal.mini_allocator == self.journal.journal_alloc.i()
            &&& self.state().journal.mini_allocator == MiniAllocator::empty()
            &&& self.journal.snapshot_geometry_bounded(self.disk_au_count)
            &&& self.branch.metadata_recovery_wf()
            &&& self.branch.image.roots_bounded(self.disk_au_count)
            &&& self.branch.active_branch is None
        }
        &&& self.recovery_phase is LoadingBranch ==> {
            &&& self.state().recovery_state is SuperblockAvailable
            &&& self.state().journal_metadata_loaded()
            &&& self.state().journal.journal == self.journal@
            &&& self.state().journal.mini_allocator == self.journal.journal_alloc.i()
            &&& self.state().journal.mini_allocator == MiniAllocator::empty()
            &&& self.journal.wf()
            &&& self.journal.index_ready()
            &&& self.journal.index_aus_bounded(self.disk_au_count)
            &&& self.branch.metadata_recovery_wf()
            &&& self.branch.image.roots_bounded(self.disk_au_count)
            &&& self.branch.active_branch is None
        }
        &&& self.recovery_phase is FetchingSuperblock ==> {
            self.branch.is_awaiting_superblock()
        }
        &&& self.recovery_phase is ReplayingJournal ==> {
            &&& self.state().recovery_state is MetadataLoadComplete
            &&& self.state().journal_metadata_loaded()
            &&& self.state().branch_metadata_loaded()
            &&& self.state().journal.journal == self.journal@
            &&& self.state().journal.mini_allocator == self.journal.journal_alloc.i()
            &&& self.state().journal.mini_allocator == MiniAllocator::empty()
            &&& self.journal.wf()
            &&& self.journal.index_ready()
            &&& self.journal.index_aus_bounded(self.disk_au_count)
            &&& self.branch.runtime_wf(self.disk_au_count)
            &&& self.au_pool@.disjoint(self.branch.owned_aus())
        }
        &&& self.recovery_phase is ReadyForUserOperation ==> {
            &&& self.state().recovery_state is RecoveryComplete
            &&& self.state().journal_metadata_loaded()
            &&& self.state().branch_metadata_loaded()
            &&& self.state().journal.journal == self.journal@
            &&& self.state().journal.mini_allocator == self.journal.journal_alloc.i()
            &&& self.journal.ready_wf(self.disk_au_count)
            &&& self.live_component_alignment()
            &&& self.branch.runtime_wf(self.disk_au_count)
            &&& self.au_pool@.disjoint(self.journal.owned_aus())
            &&& self.au_pool@.disjoint(self.branch.owned_aus())
        }
    }

    pub closed spec fn sync_wf(&self) -> bool
    {
        let ids = self.sync_requests.all_ids();
        &&& self.sync_requests.ids_unique()
        &&& ids.to_set() =~= self.state().sync_req_map.dom()
        &&& !(self.recovery_phase is ReadyForUserOperation) ==> {
            &&& ids.len() == 0
            &&& self.pending_branch_sync is None
            &&& self.in_flight_sync is None
        }
        &&& self.pending_branch_sync is Some ==> {
            &&& self.in_flight_sync is None
            &&& self.sync_requests.journal_cleaning_reqs@.len() > 0
            &&& self.sync_requests.sync_target_lsn as nat == self.state().branch.seq_end()
            &&& match self.pending_branch_sync.unwrap() {
                PendingBranchSync::SealPending => {
                    self.branch.persisted_root_count == self.branch.image.sealed_roots.len()
                },
                PendingBranchSync::Persisting{target_root_count, summary_aus} => {
                    &&& target_root_count == self.branch.persisted_root_count + 1
                    &&& target_root_count == self.branch.image.sealed_roots.len()
                    &&& self.branch.active_branch is None
                    &&& forall |i: int| 0 <= i < summary_aus@.len()
                        ==> 0 < #[trigger] (summary_aus@[i] as nat)
                            < (self.disk_au_count as nat)
                    &&& self.state().branch.branch_summary.contains_key(
                        self.state().branch.image.sealed_roots[
                            (target_root_count - 1) as int
                        ].au,
                    )
                    &&& iau_vec_set(summary_aus@) =~= self.state().branch.branch_summary[
                        self.state().branch.image.sealed_roots[
                            (target_root_count - 1) as int
                        ].au
                    ]
                },
                PendingBranchSync::Ready => {
                    &&& self.branch.active_branch is None
                    &&& self.branch.persisted_root_count == self.branch.image.sealed_roots.len()
                },
            }
        }
        &&& self.in_flight_sync is Some ==> self.pending_branch_sync is None
        &&& forall |i: int| 0 <= i < self.sync_requests.buffered_reqs@.len()
            ==> #[trigger] self.state().sync_req_map[
                self.sync_requests.buffered_reqs@[i]
            ] <= self.state().branch.seq_end()
        &&& forall |i: int| 0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
            ==> #[trigger] self.state().sync_req_map[
                self.sync_requests.journal_cleaning_reqs@[i]
            ] <= self.sync_requests.sync_target_lsn as nat
        &&& match self.in_flight_sync {
            None => {
                &&& self.state().sync_phase is None
                &&& forall |i: int| 0 <= i < self.sync_requests.superblocking_reqs@.len()
                    ==> #[trigger] self.state().sync_req_map[
                        self.sync_requests.superblocking_reqs@[i]
                    ] <= self.state().journal.persistent_seq_end
            },
            Some(in_flight) => {
                &&& in_flight.image@@.wf()
                &&& forall |i: int| 0 <= i < in_flight.discarded_aus@.len()
                    ==> 0 < #[trigger] (in_flight.discarded_aus@[i] as nat)
                        < (self.disk_au_count as nat)
                &&& match in_flight.flavor {
                    SyncFlavor::JournalOnly => {
                        &&& in_flight.discarded_aus@.len() == 0
                        &&& in_flight.image@@.journal_snapshot.boundary_lsn
                            == self.journal.seq_start()
                    },
                    SyncFlavor::BranchAndEmptyJournal => {
                        &&& in_flight.image@@.journal_snapshot.freshest_rec() is None
                        &&& in_flight.image@@.journal_snapshot.boundary_lsn
                            == in_flight.image@@.branch_seq_end
                        &&& in_flight.image@@.journal_seq_end
                            == in_flight.image@@.branch_seq_end
                        &&& in_flight.image@@.journal_seq_end
                            == self.journal.seq_end()
                        &&& in_flight.image@@.journal_seq_end
                            == self.journal.marshalled_seq_end()
                        &&& iau_vec_set(in_flight.discarded_aus@) =~=
                            self.state().journal.loaded_index_aus()
                    },
                }
                &&& self.state().sync_phase == AtomicSyncPhase::SuperblockWriteIssued{
                    req_id: in_flight.req_id,
                    image: in_flight.image@@,
                }
                &&& self.state().journal.in_flight == Some(AtomicJournalImage{
                    snapshot: in_flight.image@@.journal_snapshot,
                    seq_end: in_flight.image@@.journal_seq_end,
                })
                &&& self.state().journal.prepared
                &&& self.state().branch.in_flight == Some(
                    crate::implementation::AtomicBranchState_v::AtomicBranchImage{
                        sealed_roots: in_flight.image@@.branch_roots,
                        seq_end: in_flight.image@@.branch_seq_end,
                    },
                )
                &&& self.state().branch.prepared
                &&& self.sync_requests.journal_cleaning_reqs@.len() == 0
                &&& self.sync_requests.superblocking_reqs@.len() > 0
                &&& self.outstanding_requests@.contains_key(in_flight.req_id)
                &&& self.outstanding_requests@[in_flight.req_id] is SuperblockWrite
                &&& forall |i: int| 0 <= i < self.sync_requests.superblocking_reqs@.len()
                    ==> #[trigger] self.state().sync_req_map[
                        self.sync_requests.superblocking_reqs@[i]
                    ] <= in_flight.image@@.journal_seq_end
            },
        }
    }

    pub closed spec fn sync_requests_empty(&self) -> bool
    {
        &&& self.sync_requests.buffered_reqs@.len() == 0
        &&& self.sync_requests.journal_cleaning_reqs@.len() == 0
        &&& self.sync_requests.superblocking_reqs@.len() == 0
        &&& self.sync_requests.all_ids() == Seq::<SyncReqId>::empty()
        &&& self.sync_requests.ids_unique()
    }

    pub closed spec fn recovery_sync_empty(&self) -> bool
    {
        &&& self.sync_requests_empty()
        &&& self.pending_branch_sync is None
        &&& self.in_flight_sync is None
        &&& self.state().sync_phase is None
        &&& self.state().sync_req_map == Map::<SyncReqId, nat>::empty()
    }

    pub closed spec fn persistent_component_alignment(&self) -> bool
    {
        self.branch.persistent_seq_end as nat == self.journal.seq_start()
    }

    pub closed spec fn live_component_alignment(&self) -> bool
    {
        self.branch@.seq_end() == self.journal.seq_end()
    }

    pub closed spec fn pending_user_op_wf(&self) -> bool
    {
        match self.pending_user_op {
            None => true,
            Some(PendingUserOp::Put{req, req_shard, key, value}) => {
                &&& req.input == (Input::PutInput{key, value})
                &&& req_shard@.instance_id() == self.instance_id()
                &&& req_shard@.element() == req
            },
            Some(PendingUserOp::Query{req, req_shard, key}) => {
                &&& req.input == (Input::QueryInput{key})
                &&& req_shard@.instance_id() == self.instance_id()
                &&& req_shard@.element() == req
            },
        }
    }

    pub closed spec fn wf_init(&self) -> bool
    {
        &&& self.inv()
        &&& self.recovery_phase is FetchingSuperblock
        &&& self.state().recovery_state is Begin
        &&& self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()
    }

    pub closed spec fn inv_api(&self, api: &ClientAPI<UnifiedCacheProgramModel>) -> bool
    {
        &&& self.inv()
        &&& self.instance_id() == api.instance_id()
    }

    closed spec fn cache_read_io_lag_inv(&self) -> bool
    {
        &&& self.model@.instance_id() == self.instance@.id()
        &&& 1 < (self.disk_au_count as nat)
        &&& (self.disk_page_count as nat) == page_count()
        &&& 0 < (self.disk_page_count as nat)
        &&& self.cache.wf()
        &&& self.journal.basic_wf()
        &&& self.branch.wf()
        &&& self.au_pool.canonical_wf(self.disk_au_count)
        &&& self.state().branch == self.branch@
        &&& self.state().free_aus =~= self.au_pool@
        &&& !(self.recovery_phase is FetchingSuperblock) ==>
            self.state().journal.persistent_seq_end == self.persistent_journal_seq_end as nat
        &&& self.outstanding_requests_wf()
        &&& self.outstanding_requests_single_flight()
        &&& self.pending_user_op_wf()
        &&& self.sync_wf()
        &&& !(self.recovery_phase is FetchingSuperblock) ==>
            self.persistent_component_alignment()
        &&& (!(self.recovery_phase is ReadyForUserOperation) ==> self.recovery_sync_empty())
        &&& (!(self.recovery_phase is ReadyForUserOperation) ==>
            self.pending_user_op is None)
        &&& self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()
        &&& self.state().outstanding_cache_reqs == Map::<ID, Address>::empty()
        &&& self.recovery_phase is LoadingJournal ==> {
            &&& self.state().recovery_state is SuperblockAvailable
            &&& self.state().journal.journal == self.journal@
            &&& self.state().journal.mini_allocator == self.journal.journal_alloc.i()
            &&& self.state().journal.mini_allocator == MiniAllocator::empty()
            &&& self.journal.snapshot_geometry_bounded(self.disk_au_count)
            &&& self.branch.metadata_recovery_wf()
            &&& self.branch.image.roots_bounded(self.disk_au_count)
            &&& self.branch.active_branch is None
        }
        &&& self.recovery_phase is LoadingBranch ==> {
            &&& self.state().recovery_state is SuperblockAvailable
            &&& self.state().journal_metadata_loaded()
            &&& self.state().journal.journal == self.journal@
            &&& self.state().journal.mini_allocator == self.journal.journal_alloc.i()
            &&& self.state().journal.mini_allocator == MiniAllocator::empty()
            &&& self.journal.wf()
            &&& self.journal.index_ready()
            &&& self.journal.index_aus_bounded(self.disk_au_count)
            &&& self.branch.metadata_recovery_wf()
            &&& self.branch.image.roots_bounded(self.disk_au_count)
            &&& self.branch.active_branch is None
        }
        &&& self.recovery_phase is FetchingSuperblock ==> {
            self.branch.is_awaiting_superblock()
        }
        &&& self.recovery_phase is ReplayingJournal ==> {
            &&& self.state().recovery_state is MetadataLoadComplete
            &&& self.state().journal_metadata_loaded()
            &&& self.state().branch_metadata_loaded()
            &&& self.state().journal.journal == self.journal@
            &&& self.state().journal.mini_allocator == self.journal.journal_alloc.i()
            &&& self.state().journal.mini_allocator == MiniAllocator::empty()
            &&& self.journal.wf()
            &&& self.journal.index_ready()
            &&& self.journal.index_aus_bounded(self.disk_au_count)
            &&& self.branch.runtime_wf(self.disk_au_count)
            &&& self.au_pool@.disjoint(self.branch.owned_aus())
        }
        &&& self.recovery_phase is ReadyForUserOperation ==> {
            &&& self.state().recovery_state is RecoveryComplete
            &&& self.state().journal_metadata_loaded()
            &&& self.state().branch_metadata_loaded()
            &&& self.state().journal.journal == self.journal@
            &&& self.state().journal.mini_allocator == self.journal.journal_alloc.i()
            &&& self.journal.ready_wf(self.disk_au_count)
            &&& self.live_component_alignment()
            &&& self.branch.runtime_wf(self.disk_au_count)
            &&& self.au_pool@.disjoint(self.journal.owned_aus())
            &&& self.au_pool@.disjoint(self.branch.owned_aus())
        }
    }

    proof fn unified_system_inv_journal_pages_parsable(self) -> (journal_raw_disk: Map<Address, RawPage>)
        requires
            self.inv(),
            self.state().journal.journal == self.journal@,
            !(self.state().recovery_state is Begin),
            !(self.state().recovery_state is AwaitingSuperblock),
        ensures
            cache_agrees_with_raw_disk_on_domain(self.cache@, journal_raw_disk),
            self.state().journal.wf(),
            self.journal@.status is Some ==> forall |au: AU| {
                &&& #[trigger] self.journal@.status.unwrap().lsn_au_index.values().contains(au)
                &&& self.state().journal.mini_allocator.allocs.contains_key(au)
            } ==> self.state().journal.mini_allocator.allocated_aus().contains(au),
            self.state().client_ready() && self.journal@.status is Some ==> forall |au: AU|
                #[trigger] self.journal@.status.unwrap().lsn_au_index.values().contains(au)
                ==> 0 < au,
            self.state().client_ready() ==> self.state().free_aus.disjoint(
                self.state().journal.loaded_index_aus(),
            ),
            self.state().client_ready() ==> self.state().journal.loaded_index_aus().disjoint(
                self.state().branch.mini_allocator.all_aus(),
            ),
            self.state().client_ready() ==> {
                &&& self.state().persistent_image is Some
                &&& self.state().persistent_image.unwrap().wf()
                &&& self.state().branch.persistent_image.sealed_roots
                    == self.state().persistent_image.unwrap().branch_roots
                &&& self.state().branch.persistent_image.seq_end
                    == self.state().persistent_image.unwrap().branch_seq_end
                &&& self.state().journal.persistent_seq_end
                    == self.state().persistent_image.unwrap().journal_seq_end
            },
            self.state().sync_phase is None ==> {
                &&& self.state().branch.in_flight is None
                &&& self.state().journal.in_flight is None
            },
            self.journal@.status is Some && self.journal@.snapshot.freshest_rec() is Some ==> {
                let root = self.journal@.snapshot.freshest_rec().unwrap();
                &&& journal_raw_disk.contains_key(root)
                &&& to_journal_records(journal_raw_disk)[root].message_seq.seq_end
                    == self.journal.marshalled_seq_end()
                &&& self.state().client_ready() ==> {
                    &&& root.wf()
                    &&& root != spec_superblock_addr()
                }
            },
            self.journal@.snapshot.freshest_rec() is Some ==>
                journal_disk_inv(
                    DiskView{
                        boundary_lsn: self.journal@.snapshot.boundary_lsn,
                        entries: to_journal_records(journal_raw_disk),
                    },
                    self.journal@.snapshot.freshest_rec()),
            self.journal@.status is None && self.journal@.snapshot.freshest_rec() is Some ==>
                journal_disk_load_index_inv(
                    DiskView{
                        boundary_lsn: self.journal@.snapshot.boundary_lsn,
                        entries: to_journal_records(journal_raw_disk),
                    },
                    self.journal@.snapshot.freshest_rec(),
                    self.journal@.snapshot.first()),
    {
        let tracked empty_disk_responses: Tracked<DiskRespShard> =
            Tracked(DiskRespShard::empty(self.instance_id()));
        let model = open_system_invariant_disk_response::<
            UnifiedCacheProgramModel,
            UnifiedCacheRefinementProof,
        >(self.model, empty_disk_responses);
        let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
        let branch_src = crate::implementation::UnifiedCacheBranchRefinement_v::unified_cache_branch_source(model);
        let system = UnifiedCacheSystemRefinement::unified_cache_system_i(model);
        let journal_cdj = journal_src.journal_caching_disk_state_i();
        let journal_raw_disk =
            journal_cdj.disk.visible().restrict(journal_cdj.journal_tj().disk_view.entries.dom());

        assert(UnifiedCacheRefinementProof::inv(model));
        assert(model.program == self.model@.value());
        assert(UnifiedCacheSystemRefinement::inv(model));
        UnifiedCacheSystemRefinement::inv_implies_branch_source_inv(model);
        UnifiedCacheSystemRefinement::inv_implies_journal_source_inv(model);
        assert(crate::implementation::UnifiedCacheBranchRefinement_v::inv(branch_src));
        assert(branch_src.inv());
        assert(journal_src.inv());
        if self.state().client_ready() {
            UnifiedCacheSystemRefinement::inv_implies_ready_seq_end_alignment(model);
            assert(self.state().allocation_metadata_loaded());
            UnifiedCacheSystemRefinement::allocation_metadata_loaded_facts(model);
            assert(self.state().persistent_image is Some);
            assert(branch_src.superblock_loaded());
            assert(journal_src.superblock_loaded());
            assert(branch_src.persistent_superblock_image_i()
                == self.state().persistent_image.unwrap());
            assert(journal_src.persistent_superblock_image_i()
                == self.state().persistent_image.unwrap());
            assert(self.state().persistent_image.unwrap().wf());
            UnifiedCacheSystemRefinement::journal_projection_aus_subset_system_journal_owned(model);
            UnifiedCacheSystemRefinement::branch_projection_aus_subset_system_branch_owned(model);
            assert(system.allocation_wf());
            assert(system.free_aus == self.state().free_aus);
            assert(self.state().journal.loaded_index_aus()
                <= journal_src.journal_projection_aus());
            assert(self.state().free_aus.disjoint(
                self.state().journal.loaded_index_aus(),
            ));
            assert(self.state().journal.loaded_index_aus().disjoint(
                self.state().branch.mini_allocator.all_aus(),
            )) by {
                assert(branch_src.branch_projection_aus()
                    <= system.branch_owned_aus());
                assert(self.state().branch.mini_allocator.all_aus()
                    <= branch_src.branch_projection_aus());
                assert(journal_src.journal_projection_aus()
                    <= system.journal_owned_aus());
                assert(system.component_disjoint());
            }
        }
        if self.state().sync_phase is None {
            assert(branch_src.in_flight is None);
            assert(journal_src.in_flight is None);
            assert(self.state().branch.in_flight is None);
            assert(self.state().journal.in_flight is None);
        }
        UnifiedCacheSystemRefinement::post_superblock_journal_source_facts(model);
        assert(UnifiedCacheJournalRefinement::inv(journal_src));
        assert(journal_src.inv());
        assert(journal_src.semantic_inv());
        assert(journal_cdj.refinement_inv());
        assert(journal_cdj.semantic_inv());
        assert(journal_cdj.inv());
        assert(journal_cdj.journal == self.journal@);
        assert(self.state().journal.wf()) by {
            assert(self.state().journal.journal.wf());
            assert(self.state().journal.mini_allocator.wf());
        }
        assert(journal_cdj.mini_allocator == self.state().journal.mini_allocator);
        assert(self.journal@.status is Some ==> forall |au: AU| {
            &&& #[trigger] self.journal@.status.unwrap().lsn_au_index.values().contains(au)
            &&& self.state().journal.mini_allocator.allocs.contains_key(au)
        } ==> self.state().journal.mini_allocator.allocated_aus().contains(au)) by {
            assert(journal_cdj.indexed_aus_not_all_pages_free());
        }
        if self.state().client_ready() && self.journal@.status is Some {
            reveal(crate::implementation::CachingDiskJournal_v::CachingDiskJournal::State::allocation_view_semantic_inv);
            let tj = journal_cdj.journal_tj();
            let first = journal_cdj.allocation_first();
            assert(tj.disk_view.pointer_is_upstream(tj.freshest_rec, first));
            tj.build_lsn_au_index_from_first_ensures(first);
            let index = tj.build_lsn_au_index_from_first(first);
            assert(index == self.journal@.status.unwrap().lsn_au_index);
            assert forall |au: AU|
                #[trigger] self.journal@.status.unwrap().lsn_au_index.values().contains(au)
                implies 0 < au by {
                let lsn = choose |lsn: LSN|
                    index.contains_key(lsn) && index[lsn] == au;
                let addr = tj.disk_view.instantiate_index_keys_exist_valid_entries(index, lsn);
                assert(addr.wf());
                assert(addr.au == au);
                assert(journal_src.journal_projection_aus().contains(au));
                assert(system.journal_owned_aus().contains(au));
                assert(system.component_disjoint());
                assert(!crate::implementation::CrashAwareCachingDiskSystem_v::CrashAwareCachingDiskSystem::State::reserved_aus().contains(au));
                if au == 0 {
                    assert(crate::implementation::CrashAwareCachingDiskSystem_v::CrashAwareCachingDiskSystem::State::reserved_aus().contains(au));
                    assert(false);
                }
            }
        }
        journal_cdj.disk.visible_submap_readable();
        reveal(crate::implementation::CachingDiskJournal_v::CachingDiskJournal::State::allocation_view_semantic_inv);
        journal_cdj.journal_disk_view().path_build_tight_is_sub_disk(
            journal_cdj.journal_tj().freshest_rec,
        );
        assert(to_journal_records(journal_raw_disk) == journal_cdj.journal_tj().disk_view.entries) by {
            assert_maps_equal!(
                to_journal_records(journal_raw_disk),
                journal_cdj.journal_tj().disk_view.entries,
                addr => {
                    if to_journal_records(journal_raw_disk).contains_key(addr) {
                        assert(journal_raw_disk.contains_key(addr));
                        assert(journal_cdj.journal_tj().disk_view.entries.contains_key(addr));
                        assert(journal_cdj.journal_disk_view().entries.contains_key(addr));
                        assert(journal_cdj.disk.visible().contains_key(addr));
                        assert(journal_cdj.journal_tj().disk_view.is_sub_disk(journal_cdj.journal_disk_view()));
                        assert(journal_cdj.journal_tj().disk_view.entries[addr]
                            == journal_cdj.journal_disk_view().entries[addr]);
                        assert(journal_raw_disk[addr] == journal_cdj.disk.visible()[addr]);
                    }
                    if journal_cdj.journal_tj().disk_view.entries.contains_key(addr) {
                        assert(journal_cdj.journal_disk_view().entries.contains_key(addr));
                        assert(journal_cdj.disk.visible().contains_key(addr));
                        assert(journal_cdj.journal_tj().disk_view.is_sub_disk(journal_cdj.journal_disk_view()));
                        assert(journal_cdj.journal_tj().disk_view.entries[addr]
                            == journal_cdj.journal_disk_view().entries[addr]);
                        assert(journal_raw_disk.contains_key(addr));
                        assert(journal_raw_disk[addr] == journal_cdj.disk.visible()[addr]);
                    }
                }
            );
        }

        assert(cache_agrees_with_raw_disk_on_domain(self.cache@, journal_raw_disk)) by {
            assert forall |addr: Address, data: RawPage| #[trigger] self.cache@.valid_read(addr, data)
                && journal_raw_disk.contains_key(addr)
                implies journal_raw_disk[addr] == data by {
                let aus = journal_src.journal_projection_aus();
                assert(journal_raw_disk.contains_key(addr));
                assert(journal_cdj.journal_tj().disk_view.entries.contains_key(addr));
                assert(journal_cdj.journal_disk_view().entries.contains_key(addr));
                assert(journal_cdj.disk.visible().contains_key(addr));
                assert(journal_cdj.journal_disk_view().entries[addr]
                    == to_journal_records(journal_cdj.disk.visible())[addr]);
                if journal_cdj.disk.visible_cache().contains_key(addr) {
                    assert(journal_cdj.disk.cache.contains_key(addr));
                } else {
                    assert(journal_cdj.disk.persistent.contains_key(addr));
                    if journal_cdj.disk.cache.contains_key(addr) {
                        assert(journal_cdj.disk.status.contains_key(addr));
                        assert(journal_cdj.disk.status[addr]
                            == crate::implementation::CachingDisk_v::PageStatus::Clean);
                    }
                }
                assert(addresses_in_aus(aus).contains(addr)) by {
                    if journal_cdj.disk.cache.contains_key(addr) {
                        assert(project_cache_pages(journal_src.cache, aus).contains_key(addr));
                    } else {
                        assert(journal_cdj.disk.persistent.contains_key(addr));
                    }
                }
                assert(crate::implementation::CachingDiskAdapterRefinement_v::cache_filled_addr(
                    journal_src.cache,
                    addr,
                )) by {
                    assert(self.cache@.valid_read(addr, data));
                    assert(journal_src.cache == self.cache@);
                    journal_src.cache.build_lookup_map_ensures();
                    assert(journal_src.cache.build_lookup_map_props(journal_src.cache.lookup_map));
                    assert(journal_src.cache.lookup_map.contains_key(addr));
                    assert(journal_src.cache.entries.contains_key(journal_src.cache.lookup_map[addr]));
                    assert(journal_src.cache.entries[journal_src.cache.lookup_map[addr]] is Filled);
                }
                assert(filled_cache_pages(journal_src.cache).contains_key(addr));
                assert(cache_filled_page(journal_src.cache, addr) == data) by {
                    assert(journal_src.cache == self.cache@);
                    assert(self.cache@.valid_read(addr, data));
                }
                assert(project_cache_pages(journal_src.cache, aus).contains_key(addr));
                projectable_entry_in_caching_disk_i(journal_src.cache, journal_src.disk, aus, addr);
                assert(journal_cdj.disk.cache.contains_key(addr));
                assert(journal_cdj.disk.cache[addr] == data);
                journal_cdj.disk.visible_submap_readable();
                assert(journal_cdj.disk.readable().contains_key(addr));
                assert(journal_cdj.disk.readable()[addr] == journal_cdj.disk.visible()[addr]);
                assert(journal_cdj.disk.readable()[addr] == data);
                assert(journal_raw_disk[addr] == journal_cdj.disk.visible()[addr]);
            }
        }
        if self.journal@.status is Some && self.journal@.snapshot.freshest_rec() is Some {
            let root = self.journal@.snapshot.freshest_rec().unwrap();
            journal_cdj.loaded_i_view_facts();
            reveal(crate::implementation::CachingDiskJournal_v::CachingDiskJournal::State::allocation_view_semantic_inv);
            assert(journal_cdj.journal_tj().freshest_rec == Some(root));
            assert(journal_cdj.journal_tj().disk_view.entries.contains_key(root));
            assert(journal_cdj.journal_tj().disk_view.entries[root].message_seq.seq_end
                == journal_cdj.allocation_unmarshalled_tail().seq_start);
            self.journal.view_ensures();
            assert(self.journal.index_ready());
            self.journal.view_marshaled_seq_end_ensures();
            assert(journal_cdj.allocation_unmarshalled_tail()
                == crate::implementation::CachingDiskJournal_v::cj_unmarshalled_tail(
                    journal_cdj.journal,
                ));
            assert(journal_cdj.allocation_unmarshalled_tail().seq_start
                == journal_cdj.journal.marshalled_seq_end());
            assert(journal_cdj.journal.marshalled_seq_end()
                == self.journal@.marshalled_seq_end());
            assert(journal_cdj.allocation_unmarshalled_tail().seq_start
                == self.journal.marshalled_seq_end());
            assert(journal_cdj.journal_tj().disk_view.entries
                == to_journal_records(journal_raw_disk));
            assert(journal_raw_disk.contains_key(root));
            assert(root.wf()) by {
                assert(journal_cdj.journal_tj().disk_view.wf_addrs());
            }
            if self.state().client_ready() {
                let aus = journal_src.journal_projection_aus();
                assert(addresses_in_aus(aus).contains(root)) by {
                    assert(journal_cdj.journal_tj().disk_view.entries.contains_key(root));
                    assert(journal_cdj.journal_disk_view().entries.contains_key(root));
                    assert(journal_cdj.disk.visible().contains_key(root));
                    if journal_cdj.disk.visible_cache().contains_key(root) {
                        assert(project_cache_pages(journal_src.cache, aus).contains_key(root));
                    } else {
                        assert(journal_cdj.disk.persistent.contains_key(root));
                    }
                }
                assert(aus.contains(root.au));
                assert(system.journal_owned_aus().contains(root.au));
                assert(system.component_disjoint());
                assert(!system.journal_owned_aus().contains(spec_superblock_addr().au)) by {
                    if system.journal_owned_aus().contains(spec_superblock_addr().au) {
                        assert(crate::implementation::CrashAwareCachingDiskSystem_v::CrashAwareCachingDiskSystem::State::reserved_aus()
                            .contains(spec_superblock_addr().au));
                        assert(false);
                    }
                }
                assert(root.au != spec_superblock_addr().au);
                assert(root != spec_superblock_addr());
            }
        }
        assert(journal_cdj.journal_tj().disk_view.acyclic());
        assert(journal_cdj.journal_tj().disk_view.block_in_bounds(
            journal_cdj.journal_tj().freshest_rec,
        ));
        assert(journal_cdj.journal_tj().disk_view.decodable(
            journal_cdj.journal_tj().freshest_rec,
        ));
        journal_cdj.journal_tj().disk_view.decodable_implies_path_decodable(
            journal_cdj.journal_tj().freshest_rec,
        );
        journal_cdj.journal_tj().disk_view.path_build_tight_idempotent(
            journal_cdj.journal_tj().freshest_rec,
        );
        assert(self.journal@.snapshot.freshest_rec() is Some ==>
            journal_disk_inv(
                DiskView{
                    boundary_lsn: self.journal@.snapshot.boundary_lsn,
                    entries: to_journal_records(journal_raw_disk),
                },
                self.journal@.snapshot.freshest_rec()));
        if self.journal@.status is None && self.journal@.snapshot.freshest_rec() is Some {
            let image = journal_cdj.backing_journal_image();
            assert(journal_cdj.journal.status is None);
            assert(journal_cdj.unloaded_backing_image_valid());
            assert(image.valid_image());
            image.valid_image_implies_tight_valid_image();
            assert(image.tj.disk_view == journal_cdj.journal_disk_view());
            assert(image.tj.freshest_rec == self.journal@.snapshot.freshest_rec());
            assert(image.first == self.journal@.snapshot.first());
            assert(image.tight_tj() == journal_cdj.journal_tj());
            assert(journal_cdj.journal_tj().disk_view.pointer_is_upstream(
                journal_cdj.journal_tj().freshest_rec,
                self.journal@.snapshot.first(),
            ));
            journal_cdj.journal_disk_view().path_build_tight_idempotent(
                journal_cdj.journal_tj().freshest_rec,
            );
            assert(journal_cdj.journal_tj().disk_view.path_build_tight(
                journal_cdj.journal_tj().freshest_rec,
            ) == journal_cdj.journal_tj().disk_view);
        }
        assert(self.journal@.status is None && self.journal@.snapshot.freshest_rec() is Some ==>
            journal_disk_load_index_inv(
                DiskView{
                    boundary_lsn: self.journal@.snapshot.boundary_lsn,
                    entries: to_journal_records(journal_raw_disk),
                },
                self.journal@.snapshot.freshest_rec(),
                self.journal@.snapshot.first()));
        journal_raw_disk
    }

    pub closed spec fn outstanding_cache_reqs_match_model(&self) -> bool
    {
        &&& forall |id: ID| #[trigger] self.state().outstanding_cache_reqs.contains_key(id) ==> {
            &&& self.outstanding_requests@.contains_key(id)
            &&& !(self.outstanding_requests@[id] is SuperblockWrite)
        }
        &&& self.in_flight_sync is None ==>
            self.state().outstanding_cache_reqs.dom() == self.outstanding_requests@.dom()
        &&& self.state().outstanding_cache_reqs.is_injective()
        &&& forall |id: ID| #[trigger] self.outstanding_requests@.contains_key(id) ==> {
            match self.outstanding_requests@[id] {
                OutstandingReqInfo::CacheRead{addr, ..}
                | OutstandingReqInfo::CacheWrite{addr, ..} => {
                    &&& self.state().outstanding_cache_reqs.contains_key(id)
                    &&& self.state().outstanding_cache_reqs[id] == addr@
                },
                OutstandingReqInfo::SuperblockWrite => {
                    !self.state().outstanding_cache_reqs.contains_key(id)
                },
            }
        }
    }

    pub closed spec fn outstanding_requests_wf(&self) -> bool
    {
        forall |id: ID| #[trigger] self.outstanding_requests@.contains_key(id) ==> {
            match self.outstanding_requests@[id] {
                OutstandingReqInfo::CacheRead{addr, load_handle, ..} => {
                    &&& self.cache.entry_fetched(&addr)
                    &&& self.cache.valid_load_handle(&addr, load_handle)
                },
                OutstandingReqInfo::CacheWrite{addr, write_handle} => {
                    &&& self.cache.entry_fetched(&addr)
                    &&& self.cache.valid_writeback_handle(&addr, write_handle)
                },
                OutstandingReqInfo::SuperblockWrite => true,
            }
        }
    }

    pub closed spec fn outstanding_requests_single_flight(&self) -> bool
    {
        forall |id1: ID, id2: ID| {
            &&& #[trigger] self.outstanding_requests@.contains_key(id1)
            &&& #[trigger] self.outstanding_requests@.contains_key(id2)
        } ==> id1 == id2
    }

    fn issue_acquired_cache_read_io(
        &mut self,
        addr: IAddress,
        load_handle: MutHandle,
        purpose: CacheReadPurpose,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (started: bool)
        requires
            old(self).model@.instance_id() == old(self).instance@.id(),
            old(self).instance_id() == old(api).instance_id(),
            old(self).cache_read_io_lag_inv(),
            !(old(self).state().recovery_state is Begin),
            !(old(self).state().recovery_state is AwaitingSuperblock),
            addr@ != spec_superblock_addr(),
            old(self).cache.wf(),
            old(self).cache.entry_fetched(&addr),
            old(self).cache.valid_load_handle(&addr, load_handle),
            Cache::State::next(old(self).state().cache, old(self).cache@, cache_load_label(&addr)),
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).state().outstanding_cache_reqs == Map::<ID, Address>::empty(),
        ensures
            started,
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_live_component_alignment = self.live_component_alignment();
        proof {
            if self.recovery_phase is ReadyForUserOperation {
                reveal(Implementation::cache_read_io_lag_inv);
                assert(pre_live_component_alignment);
            }
        }
        let ghost pre_outstanding = self.outstanding_requests@;
        let ghost pre_cache = self.cache;
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
        }

        let req_id_perm = Tracked(api.send_disk_request_predict_id());
        let disk_req = IDiskRequest::ReadReq{from: addr};
        let ghost req_map = map![req_id_perm@ => disk_req@];
        let ghost updated = map![req_id_perm@ => addr@];
        let ghost disk_request_tuples =
            multiset_map_singleton(req_id_perm@, disk_req@);
        let ghost disk_response_tuples = Multiset::empty();
        let ghost post_state = UnifiedCacheProgramModel{
            state: UnifiedCacheSystem::State{
                cache: self.cache@,
                outstanding_cache_reqs:
                    pre_state.state.outstanding_cache_reqs.union_prefer_right(updated),
                ..pre_state.state
            }
        };

        proof {
            multiset_map_singleton_ensures(req_id_perm@, disk_req@);
            assert(multiset_to_map(disk_request_tuples) == req_map);
            Self::singleton_updated_addr_map(req_id_perm@, disk_req@, addr@);
            assert(updated.is_injective());
            assert(!updated.contains_value(spec_superblock_addr()));
            Self::singleton_req_map_values(req_id_perm@, disk_req@);
            assert(req_map.values() == set![disk_req@]);
            assert(Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()}
                == cache_load_label(&addr));
            assert(UnifiedCacheSystem::State::cache_io_begin(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Disk,
                req_map,
                self.cache@,
                disk_request_tuples,
                disk_response_tuples,
            )) by {
            }
            assert(UnifiedCacheSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Disk,
                UnifiedCacheSystem::Step::cache_io_begin(
                    req_map,
                    self.cache@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            let info = ProgramDiskInfo{
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheSystem::Step::cache_io_begin(
                    req_map,
                    self.cache@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
                info,
            ));
            UnifiedCacheProgramModel::lift_disk_step(pre_state, post_state, info);
        }

        let tracked empty_disk_responses = DiskRespShard::empty(self.instance_id());
        let tracked new_disk_req_token = self.instance.borrow().disk_transitions(
            KVStoreTokenized::Label::DiskOp{
                disk_request_tuples,
                disk_response_tuples,
            },
            post_state,
            &mut model,
            empty_disk_responses,
        );
        self.model = Tracked(model);

        let id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));
        self.outstanding_requests.insert(id, OutstandingReqInfo::CacheRead{
            addr,
            load_handle,
            purpose,
        });
        proof {
            assert(self.outstanding_requests_wf()) by {
                assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                    implies {
                        match self.outstanding_requests@[id2] {
                            OutstandingReqInfo::CacheRead{addr, load_handle, ..} => {
                                &&& self.cache.entry_fetched(&addr)
                                &&& self.cache.valid_load_handle(&addr, load_handle)
                            },
                            OutstandingReqInfo::CacheWrite{addr, write_handle} => {
                                &&& self.cache.entry_fetched(&addr)
                                &&& self.cache.valid_writeback_handle(&addr, write_handle)
                            },
                            OutstandingReqInfo::SuperblockWrite => true,
                        }
                    } by {
                    if id2 == id {
                    } else {
                        assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty());
                        assert(!pre_outstanding.contains_key(id2));
                        assert(false);
                    }
                }
            }
            assert(self.outstanding_requests@.dom() =~= set![id]);
            assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty());
            }
            assert(self.state().outstanding_cache_reqs == map![id => addr@]) by {
                assert(post_state.state.outstanding_cache_reqs
                    == pre_state.state.outstanding_cache_reqs.union_prefer_right(updated));
                assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                assert(updated == map![req_id_perm@ => addr@]);
                assert(id == req_id_perm@);
                assert_maps_equal!(self.state().outstanding_cache_reqs, map![id => addr@], k => {
                    if k == id {
                        assert(updated.contains_key(k));
                    } else {
                        assert(!updated.contains_key(k));
                    }
                });
            }
            assert(self.cache@ == pre_cache@);
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
            assert(self.pending_user_op == old(self).pending_user_op);
            assert(self.instance_id() == old(self).instance_id());
            reveal(Implementation::pending_user_op_wf);
            assert(self.pending_user_op_wf());
            if old(self).recovery_phase is ReadyForUserOperation {
                assert(old(self).live_component_alignment()
                    == pre_live_component_alignment);
                assert(old(self).live_component_alignment());
                Self::live_component_alignment_preserved(old(self), self);
            }
            if !(self.recovery_phase is ReadyForUserOperation) {
                assert(!(old(self).recovery_phase is ReadyForUserOperation));
                assert(old(self).recovery_sync_empty()) by {
                    reveal(Implementation::inv_api);
                    reveal(Implementation::inv);
                }
            }
            Self::sync_wf_preserved_without_sync_change(old(self), self);
            assert(self.inv_api(api));
        }
        true
    }

    fn record_journal_load_index_complete(
        &mut self,
        reads: Ghost<Map<Address, crate::spec::AsyncDisk_t::RawPage>>,
        discovered_aus: Vec<IAU>,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).model@.instance_id() == old(self).instance@.id(),
            old(self).instance_id() == old(api).instance_id(),
            old(self).recovery_phase is LoadingJournal,
            old(self).state().recovery_state is SuperblockAvailable,
            old(self).state().cache == old(self).cache@,
            old(self).state().branch == old(self).branch@,
            old(self).state().free_aus =~= old(self).au_pool@,
            old(self).state().journal.mini_allocator == old(self).journal.journal_alloc.i(),
            old(self).state().journal.mini_allocator == MiniAllocator::empty(),
            old(self).state().outstanding_cache_reqs == Map::<ID, Address>::empty(),
            old(self).cache.wf(),
            old(self).journal.wf(),
            old(self).journal.index_ready(),
            old(self).journal.index_aus_bounded(old(self).disk_au_count),
            old(self).journal.no_unmarshalled_entries(),
            old(self).branch.wf(),
            old(self).branch.metadata_recovery_wf(),
            old(self).branch.image.roots_bounded(old(self).disk_au_count),
            old(self).branch.active_branch is None,
            old(self).persistent_component_alignment(),
            old(self).state().journal.persistent_seq_end
                == old(self).persistent_journal_seq_end as nat,
            1 < (old(self).disk_au_count as nat),
            (old(self).disk_page_count as nat) == page_count(),
            0 < (old(self).disk_page_count as nat),
            old(self).au_pool.canonical_wf(old(self).disk_au_count),
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).pending_user_op is None,
            old(self).sync_wf(),
            old(self).recovery_sync_empty(),
            iau_vec_set(discovered_aus@) =~= crate::disk::GenericDisk_v::to_aus(reads@.dom()),
            Cache::State::next(
                old(self).state().cache,
                old(self).cache@,
                load_index_labels(reads@).0,
            ),
            CachedJournal::State::next(
                old(self).state().journal.journal,
                old(self).journal@,
                load_index_labels(reads@).1,
            ),
            exists |au_depth: nat, page_depth: nat| CachedJournal::State::load_index(
                old(self).state().journal.journal,
                old(self).journal@,
                load_index_labels(reads@).1,
                au_depth,
                page_depth,
            ),
        ensures
            progress,
            self.inv_api(api),
            self.recovery_phase is LoadingBranch,
    {
        let ghost pre_state = self.model@.value();
        let ghost discovered = iau_vec_set(discovered_aus@);
        self.au_pool.remove_aus(self.disk_au_count, discovered_aus);
        let ghost new_atomic_journal = AtomicJournalState::State{
            journal: self.journal@,
            ..pre_state.state.journal
        };
        let ghost post_state = UnifiedCacheProgramModel{
            state: UnifiedCacheSystem::State{
                cache: self.cache@,
                free_aus: pre_state.state.free_aus - discovered,
                journal: new_atomic_journal,
                ..pre_state.state
            }
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
        }
        proof {
            let (cache_lbl, cached_journal_lbl) = load_index_labels(reads@);
            let atomic_lbl = AtomicJournalState::Label::LoadIndex{
                reads: to_journal_records(reads@),
                discovered_aus: discovered,
            };
            assert(cached_journal_lbl == CachedJournal::Label::LoadIndex{
                reads: to_journal_records(reads@),
                discovered_aus: discovered,
            });
            reveal(CachedJournal::State::next);
            let cached_step = choose |step|
                CachedJournal::State::next_by(
                    old(self).state().journal.journal,
                    old(self).journal@,
                    cached_journal_lbl,
                    step,
                );
            match cached_step {
                CachedJournal::Step::load_index(au_depth, page_depth) => {
                    reveal(CachedJournal::State::next_by);
                    assert(CachedJournal::State::load_index(
                        old(self).state().journal.journal,
                        old(self).journal@,
                        cached_journal_lbl,
                        au_depth,
                        page_depth,
                    ));
                    assert(AtomicJournalState::State::load_index(
                        pre_state.state.journal,
                        new_atomic_journal,
                        atomic_lbl,
                        self.journal@,
                        au_depth,
                        page_depth,
                    )) by {
                    }
                    assert(AtomicJournalState::State::next_by(
                        pre_state.state.journal,
                        new_atomic_journal,
                        atomic_lbl,
                        AtomicJournalState::Step::load_index(self.journal@, au_depth, page_depth),
                    )) by {
                        reveal(AtomicJournalState::State::next_by);
                    }
                    assert(AtomicJournalState::State::next(
                        pre_state.state.journal,
                        new_atomic_journal,
                        atomic_lbl,
                    )) by {
                        reveal(AtomicJournalState::State::next);
                    }
                    assert(UnifiedCacheSystem::State::journal_load_index(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        reads@,
                        reads@,
                        discovered,
                        self.cache@,
                        new_atomic_journal,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::journal_load_index(
                            reads@,
                            reads@,
                            discovered,
                            self.cache@,
                            new_atomic_journal,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                },
                _ => {
                    reveal(CachedJournal::State::next_by);
                    assert(false);
                },
            }
        }
        let tracked _internal_token = self.instance.borrow().internal(
            KVStoreTokenized::Label::InternalOp{},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);
        self.recovery_phase = RecoveryPhase::LoadingBranch;
        proof {
            assert(self.journal == old(self).journal);
            old(self).journal.wf_implies_basic_wf();
            assert(old(self).journal.basic_wf());
            assert(self.journal.basic_wf());
            assert(self.state().journal.mini_allocator
                == self.journal.journal_alloc.i()) by {
                assert(new_atomic_journal.mini_allocator
                    == pre_state.state.journal.mini_allocator);
                assert(pre_state.state.journal.mini_allocator
                    == old(self).journal.journal_alloc.i());
                assert(self.journal.journal_alloc.i()
                    == old(self).journal.journal_alloc.i());
            }
            assert(self.state().branch == self.branch@) by {
                assert(pre_state.state.branch == old(self).branch@);
                assert(self.branch == old(self).branch);
            }
            assert(self.outstanding_cache_reqs_match_model()) by {
                assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
            }
            assert(self.branch.metadata_recovery_wf()) by {
                assert(self.branch == old(self).branch);
            }
	            assert(self.branch.image.roots_bounded(self.disk_au_count)) by {
	                assert(self.branch == old(self).branch);
	                assert(old(self).branch.image.roots_bounded(
	                    old(self).disk_au_count,
	                ));
	            }
	            assert(self.branch.active_branch is None) by {
	                assert(old(self).branch.active_branch is None);
	                assert(self.branch == old(self).branch);
	            }
	            reveal(Implementation::inv_api);
	            reveal(Implementation::inv);
	            assert((old(self).disk_page_count as nat) == page_count());
	            assert(0 < (old(self).disk_page_count as nat));
	            assert(self.disk_au_count == old(self).disk_au_count);
	            assert(self.disk_page_count == old(self).disk_page_count);
	            assert(self.journal.index_aus_bounded(self.disk_au_count)) by {
	                assert(self.journal == old(self).journal);
	                assert(old(self).journal.index_aus_bounded(
	                    old(self).disk_au_count,
	                ));
	            }
	            assert((self.disk_page_count as nat) == page_count());
		            assert(0 < (self.disk_page_count as nat));
		            assert(self.instance_id() == api.instance_id());
		            assert(old(self).pending_user_op is None);
		            assert(self.pending_user_op == old(self).pending_user_op);
			            assert(self.pending_user_op is None);
			            reveal(Implementation::pending_user_op_wf);
			            assert(self.pending_user_op_wf());
			            assert(self.persistent_component_alignment()) by {
			                reveal(Implementation::persistent_component_alignment);
			                assert(self.branch == old(self).branch);
			                assert(self.journal == old(self).journal);
			                assert(old(self).persistent_component_alignment());
			            }
			            assert(self.state().journal.persistent_seq_end
			                == self.persistent_journal_seq_end as nat) by {
			                assert(post_state.state.journal.persistent_seq_end
			                    == pre_state.state.journal.persistent_seq_end);
			            }
			            if !(self.recovery_phase is ReadyForUserOperation) {
			                assert(!(old(self).recovery_phase is ReadyForUserOperation));
			                assert(old(self).recovery_sync_empty()) by {
			                    reveal(Implementation::inv_api);
			                    reveal(Implementation::inv);
			                }
			            }
			            Self::sync_wf_preserved_without_sync_change(old(self), self);
			            assert(self.inv_api(api));
		        }
        true
    }

    fn record_branch_refill_for_replay(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReplayingJournal,
            old(self).state().recovery_state is MetadataLoadComplete,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.state().journal.journal == old(self).state().journal.journal,
            self.state().branch.seq_end() == old(self).state().branch.seq_end(),
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch_active = self.branch.active_branch;
        let ghost pre_branch_mini_allocator_i = self.branch.mini_allocator.i();
        let ghost pre_branch_allocation_ready = self.branch.mini_allocator.allocation_ready();
        proof {
            if pre_branch_active is None && !pre_branch_allocation_ready {
                self.branch.mini_allocator.not_allocation_ready_implies_allocated_aus_empty();
                assert(pre_branch_mini_allocator_i.allocated_aus() == Set::<AU>::empty());
            }
            if pre_branch_active is None && pre_branch_allocation_ready {
                reveal(Implementation::inv_api);
                reveal(Implementation::inv);
                assert(pre_branch_mini_allocator_i.allocated_aus() == Set::<AU>::empty());
            }
        }
        match self.branch.background_refill_aus(&mut self.au_pool, self.disk_au_count) {
            None => {
                proof {
                    assert(self.branch.active_branch == pre_branch_active);
                    assert(self.branch.mini_allocator.i() == pre_branch_mini_allocator_i);
                    if self.branch.active_branch is None && self.branch.mini_allocator.allocation_ready() {
                        assert(pre_branch_active is None);
                        assert(pre_branch_mini_allocator_i.allocated_aus() == Set::<AU>::empty());
                        assert(self.branch.mini_allocator.i().allocated_aus() == Set::<AU>::empty());
                    }
                    assert(self.inv_api(api));
                }
                false
            },
            Some(allocation) => {
                let ghost aus = allocation.as_set();
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        free_aus: pre_state.state.free_aus - aus,
                        branch: self.branch@,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(pre_state.state.allocation_metadata_loaded()) by {
                        assert(pre_state.state.recovery_state is MetadataLoadComplete);
                        assert(pre_state.state.journal_metadata_loaded());
                        assert(pre_state.state.branch_metadata_loaded());
                    }
                    assert(aus <= pre_state.state.free_aus) by {
                        assert(aus <= pre_pool);
                        assert(pre_state.state.free_aus =~= pre_pool);
                    }
                    assert(AtomicBranchState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchState::Label::FillAUs{aus},
                    )) by {
                        assert(pre_state.state.branch == old(self).branch@);
                    }
                    AtomicBranchState::State::fill_aus_effect(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchState::Label::FillAUs{aus},
                    );
                    assert(UnifiedCacheSystem::State::branch_fill_aus(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        aus,
                        self.branch@,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::branch_fill_aus(aus, self.branch@),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    assert(self.state().branch.seq_end() == old(self).state().branch.seq_end()) by {
                        assert(post_state.state.branch.seq_end() == pre_state.state.branch.seq_end());
                    }
                    assert(self.branch.active_branch == pre_branch_active);
                    assert(self.inv_api(api));
                }
                api.log("unified-cache branch au refill");
                true
            },
        }
    }

    fn record_journal_refill_for_ready(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).state().recovery_state is RecoveryComplete,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        match self.journal.background_refill_aus(&mut self.au_pool, self.disk_au_count) {
            None => {
                proof {
                    self.journal.same_view_preserves_ready_wf(old(self).journal);
                    assert(self.journal.journal_alloc.i() == old(self).journal.journal_alloc.i());
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i()) by {
                        assert(pre_state.state.journal.mini_allocator
                            == old(self).journal.journal_alloc.i());
                    }
                    assert(self.persistent_component_alignment()) by {
                        reveal(Implementation::persistent_component_alignment);
                        assert(self.journal.snapshot == old(self).journal.snapshot);
                        assert(self.journal.seq_start() == old(self).journal.seq_start());
                        assert(self.branch == old(self).branch);
                        assert(old(self).persistent_component_alignment());
                    }
                    assert(self.branch@.seq_end() == old(self).branch@.seq_end());
                    assert(self.journal.seq_end() == old(self).journal.seq_end()) by {
                        assert(self.journal@ == old(self).journal@);
                    }
                    Self::live_component_alignment_preserved(old(self), self);
                    assert(self.inv_api(api));
                }
                false
            },
            Some(allocation) => {
                let ghost aus = allocation.as_set();
                let ghost new_journal = AtomicJournalState::State{
                    mini_allocator: self.journal.journal_alloc.i(),
                    ..pre_state.state.journal
                };
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        free_aus: self.au_pool@,
                        journal: new_journal,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(pre_state.state.allocation_metadata_loaded()) by {
                        assert(pre_state.state.recovery_state is RecoveryComplete);
                        assert(pre_state.state.journal_metadata_loaded());
                        assert(pre_state.state.branch_metadata_loaded());
                    }
                    assert(aus <= pre_state.state.free_aus) by {
                        assert(aus <= pre_pool);
                        assert(pre_state.state.free_aus =~= pre_pool);
                    }
                    assert(pre_state.state.journal.mini_allocator
                        == old(self).journal.journal_alloc.i());
                    assert(self.journal.journal_alloc.i()
                        == old(self).journal.journal_alloc.i().add_aus(aus));
                    assert(new_journal.mini_allocator
                        == pre_state.state.journal.mini_allocator.add_aus(aus));
                    assert(new_journal.journal == pre_state.state.journal.journal) by {
                        assert(self.journal@ == old(self).journal@);
                        assert(pre_state.state.journal.journal == old(self).journal@);
                    }
                    assert(AtomicJournalState::State::next(
                        pre_state.state.journal,
                        new_journal,
                        AtomicJournalState::Label::FillAUs{aus},
                    )) by {
                        assert(AtomicJournalState::State::fill_aus(
                            pre_state.state.journal,
                            new_journal,
                            AtomicJournalState::Label::FillAUs{aus},
                        )) by {
                        }
                        assert(AtomicJournalState::State::next_by(
                            pre_state.state.journal,
                            new_journal,
                            AtomicJournalState::Label::FillAUs{aus},
                            AtomicJournalState::Step::fill_aus(),
                        )) by {
                            reveal(AtomicJournalState::State::next_by);
                        }
                        reveal(AtomicJournalState::State::next);
                    }
                    AtomicJournalState::State::fill_aus_effect(
                        pre_state.state.journal,
                        new_journal,
                        AtomicJournalState::Label::FillAUs{aus},
                    );
                    assert(UnifiedCacheSystem::State::journal_fill_aus(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        aus,
                        new_journal,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::journal_fill_aus(aus, new_journal),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    self.journal.same_view_preserves_ready_wf(old(self).journal);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i());
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().free_aus =~= self.au_pool@);
                    assert(self.persistent_component_alignment()) by {
                        reveal(Implementation::persistent_component_alignment);
                        assert(self.journal.snapshot == old(self).journal.snapshot);
                        assert(self.journal.seq_start() == old(self).journal.seq_start());
                        assert(self.branch == old(self).branch);
                        assert(old(self).persistent_component_alignment());
                    }
                    assert(self.branch@.seq_end() == old(self).branch@.seq_end());
                    assert(self.journal.seq_end() == old(self).journal.seq_end()) by {
                        assert(self.journal@ == old(self).journal@);
                    }
                    Self::live_component_alignment_preserved(old(self), self);
                    assert(self.inv_api(api));
                }
                api.log("unified-cache journal au refill");
                true
            },
        }
    }

    fn record_branch_refill_for_ready(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).state().recovery_state is RecoveryComplete,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.state().journal.journal == old(self).state().journal.journal,
            self.state().branch.seq_end() == old(self).state().branch.seq_end(),
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_pool = self.au_pool@;
        let ghost pre_branch_active = self.branch.active_branch;
        let ghost pre_branch_mini_allocator_i = self.branch.mini_allocator.i();
        match self.branch.background_refill_aus(&mut self.au_pool, self.disk_au_count) {
            None => {
                proof {
                    assert(self.branch.active_branch == pre_branch_active);
                    assert(self.branch.mini_allocator.i() == pre_branch_mini_allocator_i);
                    assert(self.inv_api(api));
                }
                false
            },
            Some(allocation) => {
                let ghost aus = allocation.as_set();
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        free_aus: pre_state.state.free_aus - aus,
                        branch: self.branch@,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(pre_state.state.allocation_metadata_loaded()) by {
                        assert(pre_state.state.recovery_state is RecoveryComplete);
                        assert(pre_state.state.journal_metadata_loaded());
                        assert(pre_state.state.branch_metadata_loaded());
                    }
                    assert(aus <= pre_state.state.free_aus) by {
                        assert(aus <= pre_pool);
                        assert(pre_state.state.free_aus =~= pre_pool);
                    }
                    assert(AtomicBranchState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchState::Label::FillAUs{aus},
                    )) by {
                        assert(pre_state.state.branch == old(self).branch@);
                    }
                    AtomicBranchState::State::fill_aus_effect(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchState::Label::FillAUs{aus},
                    );
                    assert(UnifiedCacheSystem::State::branch_fill_aus(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        aus,
                        self.branch@,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::branch_fill_aus(aus, self.branch@),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    assert(self.state().branch.seq_end() == old(self).state().branch.seq_end()) by {
                        assert(post_state.state.branch.seq_end() == pre_state.state.branch.seq_end());
                    }
                    assert(self.branch.active_branch == pre_branch_active);
                    assert(self.inv_api(api));
                }
                api.log("unified-cache branch au refill");
                true
            },
        }
    }

    fn record_branch_maintenance_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).state().recovery_state is RecoveryComplete,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).pending_branch_sync is None,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        match self.branch.grow_active_leaf_with_cache(
            &mut self.cache,
            self.disk_au_count,
            self.disk_page_count,
        ) {
            BranchMaintenanceResult::Grew{new_root_addr, reads, writes} => {
                let ghost pre_state = self.model@.value();
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        branch: self.branch@,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }
                proof {
                    assert(pre_state.state.cache == old(self).cache@);
                    assert(pre_state.state.branch == old(self).branch@);
                    assert(pre_state.state.recovery_state is RecoveryComplete);
                    assert(pre_state.state.client_ready());
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        self.cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    ));
                    assert(AtomicBranchState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchState::Label::Grow{
                            new_root_addr: new_root_addr@,
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    ));
                    AtomicBranchState::State::grow_effect(
                        pre_state.state.branch,
                        self.branch@,
                        AtomicBranchState::Label::Grow{
                            new_root_addr: new_root_addr@,
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    );
                    assert(UnifiedCacheSystem::State::branch_grow(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        new_root_addr@,
                        reads@,
                        writes@,
                        self.cache@,
                        self.branch@,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::branch_grow(
                            new_root_addr@,
                            reads@,
                            writes@,
                            self.cache@,
                            self.branch@,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    assert(self.branch.active_branch is Some);
                    assert(!(self.branch.active_branch is None)) by {
                        assert(self.branch.active_branch is Some);
                    }
                    if self.branch.active_branch is None {
                        assert(false);
                    }
                    assert(self.branch.active_branch is None
                        && self.branch.mini_allocator.allocation_ready()
                        ==> self.branch.mini_allocator.i().allocated_aus() == Set::<AU>::empty()) by {
                        assert(!(self.branch.active_branch is None));
                    }
                    assert(self.state().branch.seq_end()
                        >= old(self).state().branch.seq_end());
                    Self::sync_wf_preserved_without_sync_change(old(self), self);
                    reveal(Implementation::inv_api);
                    reveal(Implementation::inv);
                    assert(self.inv_api(api));
                }
                api.log("unified-cache branch grow maintenance");
                true
            },
            BranchMaintenanceResult::GrewAfterPrepare{new_root_addr, reads, writes} => {
                let ghost pre_state = self.model@.value();
                let ghost prepared_cache = choose |prepared_cache: Cache::State| {
                    &&& Cache::State::next(
                        old(self).cache@,
                        prepared_cache,
                        Cache::Label::Internal,
                    )
                    &&& Cache::State::next(
                        prepared_cache,
                        self.cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    )
                };
                let ghost prepared_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: prepared_cache,
                        ..pre_state.state
                    }
                };
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        branch: self.branch@,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }
                proof {
                    assert(pre_state.state.cache == old(self).cache@);
                    assert(pre_state.state.branch == old(self).branch@);
                    assert(pre_state.state.recovery_state is RecoveryComplete);
                    assert(pre_state.state.client_ready());
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        prepared_cache,
                        Cache::Label::Internal,
                    ));
                    assert(UnifiedCacheSystem::State::cache_internal(
                        pre_state.state,
                        prepared_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        prepared_cache,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        prepared_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::cache_internal(prepared_cache),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, prepared_state);
                    assert(prepared_state.state.client_ready());
                    assert(Cache::State::next(
                        prepared_state.state.cache,
                        self.cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    ));
                    assert(AtomicBranchState::State::next(
                        prepared_state.state.branch,
                        self.branch@,
                        AtomicBranchState::Label::Grow{
                            new_root_addr: new_root_addr@,
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    ));
                    AtomicBranchState::State::grow_effect(
                        prepared_state.state.branch,
                        self.branch@,
                        AtomicBranchState::Label::Grow{
                            new_root_addr: new_root_addr@,
                            read_nodes: to_branch_nodes(reads@),
                            write_nodes: to_branch_nodes(writes@),
                        },
                    );
                    assert(UnifiedCacheSystem::State::branch_grow(
                        prepared_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        new_root_addr@,
                        reads@,
                        writes@,
                        self.cache@,
                        self.branch@,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        prepared_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::branch_grow(
                            new_root_addr@,
                            reads@,
                            writes@,
                            self.cache@,
                            self.branch@,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(prepared_state, post_state);
                }
                let tracked _cache_internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    prepared_state,
                    &mut model,
                );
                let tracked _branch_grow_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    assert(self.branch.active_branch is Some);
                    assert(!(self.branch.active_branch is None)) by {
                        assert(self.branch.active_branch is Some);
                    }
                    if self.branch.active_branch is None {
                        assert(false);
                    }
                    assert(self.branch.active_branch is None
                        && self.branch.mini_allocator.allocation_ready()
                        ==> self.branch.mini_allocator.i().allocated_aus() == Set::<AU>::empty()) by {
                        assert(!(self.branch.active_branch is None));
                    }
                    assert(self.state().branch.seq_end()
                        >= old(self).state().branch.seq_end());
                    Self::sync_wf_preserved_without_sync_change(old(self), self);
                    reveal(Implementation::inv_api);
                    reveal(Implementation::inv);
                    assert(self.inv_api(api));
                }
                api.log("unified-cache branch grow maintenance");
                true
            },
            BranchMaintenanceResult::NeedsAUs => {
                api.log("unified-cache branch maintenance needs aus");
                false
            },
            BranchMaintenanceResult::CacheFull => {
                api.log("unified-cache branch maintenance cache full");
                false
            },
            BranchMaintenanceResult::Noop
            | BranchMaintenanceResult::Blocked => {
                false
            },
        }
    }

    fn record_branch_seal_for_sync(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).pending_branch_sync is Some,
            old(self).pending_branch_sync.unwrap() is SealPending,
            old(self).branch.active_branch is Some,
            old(self).branch.commit_phase is Idle,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost pre_state = self.model@.value();
        proof {
            let tracked empty_disk_responses_for_inv: Tracked<DiskRespShard> =
                Tracked(DiskRespShard::empty(self.instance_id()));
            let system_model = open_system_invariant_disk_response::<
                UnifiedCacheProgramModel,
                UnifiedCacheRefinementProof,
            >(self.model, empty_disk_responses_for_inv);
            assert(system_model.program == pre_state);
            assert(UnifiedCacheSystemRefinement::inv(system_model));
            UnifiedCacheSystemRefinement::inv_implies_cache_inv(system_model);
            assert(pre_state.state.cache == self.cache@);
            assert(self.cache@.inv());
        }

        match self.branch.seal_active_branch_with_cache(
            &mut self.cache,
            self.disk_au_count,
            self.disk_page_count,
        ) {
            BranchSealResult::Sealed{root, aux_ptr, summary_aus, reads, writes} => {
                let ghost summary = iau_vec_set(summary_aus@);
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        branch: self.branch@,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(pre_state.state.client_ready());
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        self.cache@,
                        Cache::Label::Access{reads: reads@, writes: writes@},
                    ));
                    let branch_lbl = AtomicBranchState::Label::Seal{
                        aux_ptr: crate::implementation::IBranchNode_v::iopt_addr(aux_ptr),
                        summary,
                        read_nodes: to_branch_nodes(reads@),
                        write_nodes: to_branch_nodes(writes@),
                    };
                    assert(AtomicBranchState::State::next(
                        pre_state.state.branch,
                        self.branch@,
                        branch_lbl,
                    ));
                    AtomicBranchState::State::seal_effect(
                        pre_state.state.branch,
                        self.branch@,
                        branch_lbl,
                    );
                    assert(UnifiedCacheSystem::State::branch_seal(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        crate::implementation::IBranchNode_v::iopt_addr(aux_ptr),
                        summary,
                        reads@,
                        writes@,
                        self.cache@,
                        self.branch@,
                    ));
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::branch_seal(
                            crate::implementation::IBranchNode_v::iopt_addr(aux_ptr),
                            summary,
                            reads@,
                            writes@,
                            self.cache@,
                            self.branch@,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                }
                let tracked _seal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                let target_root_count = self.branch.image.sealed_roots.len();
                let ghost sealed_summary_seq = summary_aus@;
                self.pending_branch_sync = Some(PendingBranchSync::Persisting{
                    target_root_count,
                    summary_aus,
                });
                api.log("unified-cache branch sealed for sync");
                proof {
                    old(self).branch.mini_allocator.allocated_aus_bounded(
                        old(self).disk_au_count,
                    );
                    assert forall |i: int| 0 <= i < sealed_summary_seq.len()
                        implies 0 < #[trigger] (sealed_summary_seq[i] as nat)
                            < (self.disk_au_count as nat) by {
                        assert(summary.contains(sealed_summary_seq[i] as nat));
                    }
                    assert(target_root_count == old(self).branch.image.sealed_roots.len() + 1);
                    assert(old(self).branch.persisted_root_count
                        == old(self).branch.image.sealed_roots.len());
                    assert(self.branch.persisted_root_count
                        == old(self).branch.persisted_root_count);
                    assert(target_root_count == self.branch.persisted_root_count + 1);
                    assert(self.state().branch.branch_summary[root@.au] == summary);
                    assert(self.state().branch.image.sealed_roots[
                        (target_root_count - 1) as int
                    ] == root@);
                    assert(self.branch.mini_allocator.i().allocated_aus()
                        == Set::<AU>::empty());
                    assert(self.in_flight_sync is None);
                    assert(self.branch.active_branch is None);
                    assert(self.branch.image.roots_wf()) by {
                        assert forall |i: int| 0 <= i < self.branch.image.sealed_roots@.len()
                            implies #[trigger] self.branch.image.sealed_roots@[i]@.wf() by {
                            if i < old(self).branch.image.sealed_roots@.len() {
                                assert(self.branch.image.sealed_roots@[i]
                                    == old(self).branch.image.sealed_roots@[i]);
                            } else {
                                assert(i == old(self).branch.image.sealed_roots@.len());
                                assert(self.branch.image.sealed_roots@[i]@ == root@);
                                assert(old(self).branch.active_store@.entries.dom().contains(root@));
                                assert(root@.wf());
                            }
                        }
                    }
                    assert(branch_stack_store_addrs_safe(&self.branch.active_store)) by {
                        assert forall |addr: Address| #[trigger]
                            self.branch.active_store@.entries.dom().contains(addr)
                            implies {
                                &&& addr.wf()
                                &&& addr != spec_superblock_addr()
                            } by {
                            assert(self.branch.active_store@.entries
                                == Map::<Address, crate::allocation_layer::BranchTypes_v::BranchNode>::empty());
                            assert(false);
                        }
                    }
                    assert(self.live_component_alignment()) by {
                        reveal(Implementation::live_component_alignment);
                        assert(self.state().branch.seq_end() == pre_state.state.branch.seq_end());
                        assert(self.state().journal == pre_state.state.journal);
                    }
                    assert(self.persistent_component_alignment()) by {
                        reveal(Implementation::persistent_component_alignment);
                        assert(self.branch.persistent_seq_end == old(self).branch.persistent_seq_end);
                        assert(self.journal == old(self).journal);
                    }
                    assert(self.au_pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(
                            self.branch.mini_allocator.allocators@,
                        ),
                    )) by {
                        assert(MiniAllocatorImpl::allocators_au_set(
                            self.branch.mini_allocator.allocators@,
                        ) <= MiniAllocatorImpl::allocators_au_set(
                            old(self).branch.mini_allocator.allocators@,
                        ));
                    }
                    reveal(Implementation::sync_wf);
                    assert(self.sync_wf());
                    assert(self.state().cache == self.cache@);
                    assert(self.state().branch == self.branch@);
                    assert(self.state().free_aus =~= self.au_pool@);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i());
                    assert(self.journal.wf());
                    assert(self.journal.index_ready());
                    assert(self.journal.journal_alloc.bounded(self.disk_au_count));
                    assert(MiniAllocatorImpl::allocators_unique(
                        self.journal.journal_alloc.allocators@,
                    ));
                    assert(self.au_pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(
                            self.journal.journal_alloc.allocators@,
                        ),
                    ));
                    assert(MiniAllocatorImpl::allocators_unique(
                        self.branch.mini_allocator.allocators@,
                    ));
                    assert(self.branch.mini_allocator.bounded(self.disk_au_count));
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                    assert(self.pending_user_op_wf());
                    assert(self.model@.instance_id() == self.instance@.id());
                    assert(self.instance_id() == api.instance_id());
                    assert(self.cache.wf());
                    assert(self.journal.basic_wf());
                    assert(self.branch.wf());
                    assert(self.au_pool.wf(self.disk_au_count));
                    assert(self.au_pool.canonical_wf(self.disk_au_count));
                    assert(self.state().journal.persistent_seq_end
                        == self.persistent_journal_seq_end as nat);
                    assert(self.recovery_phase is ReadyForUserOperation);
                    assert(self.state().recovery_state is RecoveryComplete);
                    assert(self.state().journal_metadata_loaded());
                    assert(self.state().branch_metadata_loaded());
                    assert(self.branch.metadata_loaded());
                    assert(1 < (self.disk_au_count as nat));
                    assert((self.disk_page_count as nat) == page_count());
                    assert(0 < (self.disk_page_count as nat));
                    assert(self.outstanding_requests@.dom().len() == 0);
                    assert(!(self.recovery_phase is FetchingSuperblock));
                    assert(!(self.recovery_phase is LoadingJournal));
                    assert(!(self.recovery_phase is LoadingBranch));
                    assert(!(self.recovery_phase is ReplayingJournal));
                    reveal(Implementation::inv_api);
                    reveal(Implementation::inv);
                    assert(self.inv_api(api));
                }
                true
            },
            BranchSealResult::SealedAfterPrepare{
                root,
                aux_ptr,
                summary_aus,
                reads,
                writes,
                prepared_cache,
            } => {
                let ghost summary = iau_vec_set(summary_aus@);
                let ghost prepared_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: prepared_cache@,
                        ..pre_state.state
                    }
                };
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        branch: self.branch@,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        prepared_cache@,
                        Cache::Label::Internal,
                    ));
                    assert(UnifiedCacheSystem::State::cache_internal(
                        pre_state.state,
                        prepared_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        prepared_cache@,
                    ));
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        prepared_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::cache_internal(prepared_cache@),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, prepared_state);
                    assert(prepared_state.state.client_ready());
                    let branch_lbl = AtomicBranchState::Label::Seal{
                        aux_ptr: crate::implementation::IBranchNode_v::iopt_addr(aux_ptr),
                        summary,
                        read_nodes: to_branch_nodes(reads@),
                        write_nodes: to_branch_nodes(writes@),
                    };
                    assert(AtomicBranchState::State::next(
                        prepared_state.state.branch,
                        self.branch@,
                        branch_lbl,
                    ));
                    AtomicBranchState::State::seal_effect(
                        prepared_state.state.branch,
                        self.branch@,
                        branch_lbl,
                    );
                    assert(UnifiedCacheSystem::State::branch_seal(
                        prepared_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        crate::implementation::IBranchNode_v::iopt_addr(aux_ptr),
                        summary,
                        reads@,
                        writes@,
                        self.cache@,
                        self.branch@,
                    ));
                    assert(UnifiedCacheSystem::State::next_by(
                        prepared_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::branch_seal(
                            crate::implementation::IBranchNode_v::iopt_addr(aux_ptr),
                            summary,
                            reads@,
                            writes@,
                            self.cache@,
                            self.branch@,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(prepared_state, post_state);
                }
                let tracked _cache_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    prepared_state,
                    &mut model,
                );
                let tracked _seal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                let target_root_count = self.branch.image.sealed_roots.len();
                let ghost sealed_summary_seq = summary_aus@;
                self.pending_branch_sync = Some(PendingBranchSync::Persisting{
                    target_root_count,
                    summary_aus,
                });
                api.log("unified-cache branch sealed for sync");
                proof {
                    old(self).branch.mini_allocator.allocated_aus_bounded(
                        old(self).disk_au_count,
                    );
                    assert forall |i: int| 0 <= i < sealed_summary_seq.len()
                        implies 0 < #[trigger] (sealed_summary_seq[i] as nat)
                            < (self.disk_au_count as nat) by {
                        assert(summary.contains(sealed_summary_seq[i] as nat));
                    }
                    assert(target_root_count == old(self).branch.image.sealed_roots.len() + 1);
                    assert(old(self).branch.persisted_root_count
                        == old(self).branch.image.sealed_roots.len());
                    assert(self.branch.persisted_root_count
                        == old(self).branch.persisted_root_count);
                    assert(target_root_count == self.branch.persisted_root_count + 1);
                    assert(self.state().branch.branch_summary[root@.au] == summary);
                    assert(self.state().branch.image.sealed_roots[
                        (target_root_count - 1) as int
                    ] == root@);
                    assert(self.branch.mini_allocator.i().allocated_aus()
                        == Set::<AU>::empty());
                    assert(self.in_flight_sync is None);
                    assert(self.branch.active_branch is None);
                    assert(self.branch.image.roots_wf()) by {
                        assert forall |i: int| 0 <= i < self.branch.image.sealed_roots@.len()
                            implies #[trigger] self.branch.image.sealed_roots@[i]@.wf() by {
                            if i < old(self).branch.image.sealed_roots@.len() {
                                assert(self.branch.image.sealed_roots@[i]
                                    == old(self).branch.image.sealed_roots@[i]);
                            } else {
                                assert(i == old(self).branch.image.sealed_roots@.len());
                                assert(self.branch.image.sealed_roots@[i]@ == root@);
                                assert(old(self).branch.active_store@.entries.dom().contains(root@));
                                assert(root@.wf());
                            }
                        }
                    }
                    assert(branch_stack_store_addrs_safe(&self.branch.active_store)) by {
                        assert forall |addr: Address| #[trigger]
                            self.branch.active_store@.entries.dom().contains(addr)
                            implies {
                                &&& addr.wf()
                                &&& addr != spec_superblock_addr()
                            } by {
                            assert(self.branch.active_store@.entries
                                == Map::<Address, crate::allocation_layer::BranchTypes_v::BranchNode>::empty());
                            assert(false);
                        }
                    }
                    assert(self.live_component_alignment()) by {
                        reveal(Implementation::live_component_alignment);
                        assert(self.state().branch.seq_end() == pre_state.state.branch.seq_end());
                        assert(self.state().journal == pre_state.state.journal);
                    }
                    assert(self.persistent_component_alignment()) by {
                        reveal(Implementation::persistent_component_alignment);
                        assert(self.branch.persistent_seq_end == old(self).branch.persistent_seq_end);
                        assert(self.journal == old(self).journal);
                    }
                    assert(self.au_pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(
                            self.branch.mini_allocator.allocators@,
                        ),
                    )) by {
                        assert(MiniAllocatorImpl::allocators_au_set(
                            self.branch.mini_allocator.allocators@,
                        ) <= MiniAllocatorImpl::allocators_au_set(
                            old(self).branch.mini_allocator.allocators@,
                        ));
                    }
                    reveal(Implementation::sync_wf);
                    assert(self.sync_wf());
                    assert(self.state().cache == self.cache@);
                    assert(self.state().branch == self.branch@);
                    assert(self.state().free_aus =~= self.au_pool@);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i());
                    assert(self.journal.wf());
                    assert(self.journal.index_ready());
                    assert(self.journal.journal_alloc.bounded(self.disk_au_count));
                    assert(MiniAllocatorImpl::allocators_unique(
                        self.journal.journal_alloc.allocators@,
                    ));
                    assert(self.au_pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(
                            self.journal.journal_alloc.allocators@,
                        ),
                    ));
                    assert(MiniAllocatorImpl::allocators_unique(
                        self.branch.mini_allocator.allocators@,
                    ));
                    assert(self.branch.mini_allocator.bounded(self.disk_au_count));
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                    assert(self.pending_user_op_wf());
                    assert(self.model@.instance_id() == self.instance@.id());
                    assert(self.instance_id() == api.instance_id());
                    assert(self.cache.wf());
                    assert(self.journal.basic_wf());
                    assert(self.branch.wf());
                    assert(self.au_pool.wf(self.disk_au_count));
                    assert(self.au_pool.canonical_wf(self.disk_au_count));
                    assert(self.state().journal.persistent_seq_end
                        == self.persistent_journal_seq_end as nat);
                    assert(self.recovery_phase is ReadyForUserOperation);
                    assert(self.state().recovery_state is RecoveryComplete);
                    assert(self.state().journal_metadata_loaded());
                    assert(self.state().branch_metadata_loaded());
                    assert(self.branch.metadata_loaded());
                    assert(1 < (self.disk_au_count as nat));
                    assert((self.disk_page_count as nat) == page_count());
                    assert(0 < (self.disk_page_count as nat));
                    assert(self.outstanding_requests@.dom().len() == 0);
                    assert(!(self.recovery_phase is FetchingSuperblock));
                    assert(!(self.recovery_phase is LoadingJournal));
                    assert(!(self.recovery_phase is LoadingBranch));
                    assert(!(self.recovery_phase is ReplayingJournal));
                    reveal(Implementation::inv_api);
                    reveal(Implementation::inv);
                    assert(self.inv_api(api));
                }
                true
            },
            BranchSealResult::NeedsAUs => {
                api.log("unified-cache branch sync needs aus");
                false
            },
            BranchSealResult::CacheFull => {
                api.log("unified-cache branch sync cache full");
                false
            },
            BranchSealResult::Blocked => false,
        }
    }

    fn poll_branch_sync_preparation(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).pending_branch_sync is Some,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            !progress ==> self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        match &self.pending_branch_sync {
            Some(PendingBranchSync::SealPending) => {
                if self.branch.active_branch.is_none() {
                    self.pending_branch_sync = Some(PendingBranchSync::Ready);
                    proof {
                        reveal(Implementation::sync_wf);
                        assert(self.sync_wf());
                        reveal(Implementation::inv_api);
                        reveal(Implementation::inv);
                        assert(self.inv_api(api));
                    }
                    return true;
                }
                match self.branch.commit_phase {
                    CommitPhase::Idle => {},
                    CommitPhase::InFlight{..} => {
                        proof { assert(self.inv_api(api)); }
                        return false;
                    },
                }
                proof {
                    assert(self.branch.active_branch is Some);
                }
                return self.record_branch_seal_for_sync(api);
            },
            Some(PendingBranchSync::Ready) => return false,
            Some(PendingBranchSync::Persisting{..}) => {},
            None => return false,
        }

        let (target_root_count, summary_aus) = match &self.pending_branch_sync {
            Some(PendingBranchSync::Persisting{target_root_count, summary_aus}) => {
                (*target_root_count, summary_aus.clone())
            },
            _ => return unreached::<bool>(),
        };
        let ghost summary_seq = summary_aus@;
        proof {
            reveal(Implementation::sync_wf);
            assert(target_root_count == self.branch.persisted_root_count + 1);
            assert(target_root_count == self.branch.image.sealed_roots.len());
            assert(self.branch.active_branch is None);
            assert forall |i: int| 0 <= i < summary_aus@.len()
                implies 0 < #[trigger] (summary_aus@[i] as nat)
                    < (self.disk_au_count as nat) by {
            }
            assert(iau_vec_set(summary_aus@) =~= self.state().branch.branch_summary[
                self.state().branch.image.sealed_roots[
                    (target_root_count - 1) as int
                ].au
            ]);
        }
        let mut au_idx = 0usize;
        while au_idx < summary_aus.len()
            invariant
                self.inv_api(api),
                self.recovery_phase is ReadyForUserOperation,
                self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
                self.pending_branch_sync is Some,
                self.pending_branch_sync.unwrap() is Persisting,
                summary_aus@ == summary_seq,
                au_idx <= summary_aus.len(),
                target_root_count == self.branch.persisted_root_count + 1,
                target_root_count == self.branch.image.sealed_roots.len(),
                self.branch.active_branch is None,
                self.branch@.seq_end() == old(self).branch@.seq_end(),
                self.journal.seq_end() == old(self).journal.seq_end(),
                iau_vec_set(summary_aus@) =~= self.state().branch.branch_summary[
                    self.state().branch.image.sealed_roots[
                        (target_root_count - 1) as int
                    ].au
                ],
                forall |i: int| 0 <= i < summary_aus@.len()
                    ==> 0 < #[trigger] (summary_aus@[i] as nat)
                        < (self.disk_au_count as nat),
            decreases summary_aus.len() - au_idx,
        {
            let mut page: IPage = 0;
            while page < self.disk_page_count
                invariant
                    self.inv_api(api),
                    self.recovery_phase is ReadyForUserOperation,
                    self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
                    self.pending_branch_sync is Some,
                    self.pending_branch_sync.unwrap() is Persisting,
                    summary_aus@ == summary_seq,
                    au_idx < summary_aus.len(),
                    page <= self.disk_page_count,
                    target_root_count == self.branch.persisted_root_count + 1,
                    target_root_count == self.branch.image.sealed_roots.len(),
                    self.branch.active_branch is None,
                    self.branch@.seq_end() == old(self).branch@.seq_end(),
                    self.journal.seq_end() == old(self).journal.seq_end(),
                    iau_vec_set(summary_aus@) =~= self.state().branch.branch_summary[
                        self.state().branch.image.sealed_roots[
                            (target_root_count - 1) as int
                        ].au
                    ],
                    forall |i: int| 0 <= i < summary_aus@.len()
                        ==> 0 < #[trigger] (summary_aus@[i] as nat)
                            < (self.disk_au_count as nat),
                decreases self.disk_page_count - page,
            {
                let addr = IAddress{au: summary_aus[au_idx], page};
                proof {
                    assert(addr@.wf());
                    assert(addr@.au != spec_superblock_addr().au);
                    assert(addr@ != spec_superblock_addr());
                }
                if self.issue_cache_writeback_io(addr, api) {
                    return true;
                }
                page += 1;
            }
            au_idx += 1;
        }

        if !self.cache.evictable_aus(&summary_aus) {
            proof {
                assert(self.inv_api(api));
            }
            return false;
        }

        let ghost pre_state = self.model@.value();
        let ghost observed_aus = sealed_summary_aus_between(
            pre_state.state.branch.image.sealed_roots,
            pre_state.state.branch.branch_summary,
            pre_state.state.branch.persisted_root_count,
            target_root_count as nat,
        );
        proof {
            assert(target_root_count == self.branch.persisted_root_count + 1);
            assert(target_root_count == self.branch.image.sealed_roots.len());
            assert(target_root_count > 0);
            assert(pre_state.state.branch == self.branch@);
            sealed_summary_aus_between_last_subset(
                pre_state.state.branch.image.sealed_roots,
                pre_state.state.branch.branch_summary,
                target_root_count as nat,
            );
            assert(observed_aus <= pre_state.state.branch.branch_summary[
                pre_state.state.branch.image.sealed_roots[
                    (target_root_count - 1) as int
                ].au
            ]);
            assert(iau_vec_set(summary_aus@) =~= pre_state.state.branch.branch_summary[
                pre_state.state.branch.image.sealed_roots[
                    (target_root_count - 1) as int
                ].au
            ]);
            assert(observed_aus <= iau_vec_set(summary_aus@));
            Cache::State::evictable_check_subset(
                self.cache@,
                iau_vec_set(summary_aus@),
                observed_aus,
            );
        }

        let observe_result = self.branch.observe_persisted_roots(target_root_count);
        match observe_result {
            Ok(()) => {},
            Err(_) => {
                proof { assert(false); }
                return unreached::<bool>();
            },
        }
        let ghost post_state = UnifiedCacheProgramModel{
            state: UnifiedCacheSystem::State{
                branch: self.branch@,
                ..pre_state.state
            }
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
            let branch_lbl = AtomicBranchState::Label::ObservePersistedRoots{
                target_count: target_root_count as nat,
            };
            assert(AtomicBranchState::State::next(
                pre_state.state.branch,
                self.branch@,
                branch_lbl,
            ));
            AtomicBranchState::State::observe_persisted_roots_effect(
                pre_state.state.branch,
                self.branch@,
                branch_lbl,
            );
            assert(UnifiedCacheSystem::State::observe_persisted_branch_roots(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Internal,
                target_root_count as nat,
                observed_aus,
                self.cache@,
                self.branch@,
            ));
            assert(UnifiedCacheSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Internal,
                UnifiedCacheSystem::Step::observe_persisted_branch_roots(
                    target_root_count as nat,
                    observed_aus,
                    self.cache@,
                    self.branch@,
                ),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
        }
        let tracked _observe_token = self.instance.borrow().internal(
            KVStoreTokenized::Label::InternalOp{},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);
        self.pending_branch_sync = Some(PendingBranchSync::Ready);
        api.log("unified-cache branch pages persisted");
        proof {
            assert(self.branch.persisted_root_count == self.branch.image.sealed_roots.len());
            assert(self.branch.active_branch is None);
            Self::live_component_alignment_preserved(old(self), self);
            reveal(Implementation::sync_wf);
            assert(self.sync_wf());
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            assert(self.inv_api(api));
        }
        true
    }

    fn record_execute_noop(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            req.input is NoopInput,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let reply = Reply{output: Output::NoopOutput, id: req.id};
        let ghost post_state = self.model@.value();
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
            let map_req = req.mapspec_req();
            let map_reply = reply.mapspec_reply();
            assert(valid_request_reply_pair(map_req, map_reply));
            assert(UnifiedCacheSystem::State::execute_noop(
                post_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
            )) by {
            }
            assert(UnifiedCacheSystem::State::next_by(
                post_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
                UnifiedCacheSystem::Step::execute_noop(),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            assert(UnifiedCacheSystem::State::next(
                post_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
            )) by {
                reveal(UnifiedCacheSystem::State::next);
            }
            assert(ProgramModelTrait::next(
                post_state,
                post_state,
                ProgramLabel::UserIO{
                    op: ProgramUserOp::Execute{req: map_req, reply: map_reply},
                },
            ));
        }
        let tracked new_reply_token = self.instance.borrow().execute_transition(
            KVStoreTokenized::Label::ExecuteOp{req, reply},
            post_state,
            &mut model,
            req_shard.get(),
        );
        self.model = Tracked(model);
        api.send_reply(reply, Tracked(new_reply_token), true);
    }

    fn record_accept_sync_request(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            req.input is SyncInput,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        if self.sync_requests.contains_id(req.id) {
            api.log("duplicate sync request ignored");
            return;
        }

        let ghost old_ids = self.sync_requests.all_ids();
        let ghost pre_state = self.model@.value();
        let ghost post_state = UnifiedCacheProgramModel{
            state: UnifiedCacheSystem::State{
                sync_req_map: pre_state.state.sync_req_map.insert(
                    req.id,
                    pre_state.state.branch.seq_end(),
                ),
                ..pre_state.state
            }
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();

        proof {
            assert(!old_ids.to_set().contains(req.id));
            assert(old_ids.to_set() =~= pre_state.state.sync_req_map.dom());
            assert(!pre_state.state.sync_req_map.contains_key(req.id));
            assert(pre_state.state.client_ready());
            assert(UnifiedCacheSystem::State::accept_sync_request(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::AcceptSyncRequest{sync_req_id: req.id},
            )) by {
            }
            assert(UnifiedCacheSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::AcceptSyncRequest{sync_req_id: req.id},
                UnifiedCacheSystem::Step::accept_sync_request(),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            assert(UnifiedCacheSystem::State::next(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::AcceptSyncRequest{sync_req_id: req.id},
            )) by {
                reveal(UnifiedCacheSystem::State::next);
            }
            assert(ProgramModelTrait::next(
                pre_state,
                post_state,
                ProgramLabel::UserIO{
                    op: ProgramUserOp::AcceptSyncRequest{sync_req_id: req.id},
                },
            ));
            tracked_swap(self.model.borrow_mut(), &mut model);
        }

        let tracked _accepted = self.instance.borrow().accept_sync_request(
            KVStoreTokenized::Label::RequestSyncOp{sync_req_id: req.id},
            post_state,
            &mut model,
            req_shard.get(),
        );
        self.model = Tracked(model);
        self.sync_requests.push_buffered(req.id);

        proof {
            assert(old(self).in_flight_sync is None) by {
                if old(self).in_flight_sync is Some {
                    let in_flight = old(self).in_flight_sync.unwrap();
                    assert(old(self).outstanding_requests@.contains_key(in_flight.req_id));
                    assert(false);
                }
            }
            assert(self.in_flight_sync is None);
            assert(self.state().sync_phase is None);
            assert(self.sync_requests.ids_unique());
            assert(self.sync_requests.all_ids().to_set()
                =~= self.state().sync_req_map.dom()) by {
                assert(self.sync_requests.all_ids().to_set()
                    =~= old_ids.to_set().insert(req.id));
                assert(self.state().sync_req_map
                    == pre_state.state.sync_req_map.insert(
                        req.id,
                        pre_state.state.branch.seq_end(),
                    ));
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
                assert(self.state().sync_req_map[id] == pre_state.state.sync_req_map[id]);
                assert(old(self).state().sync_req_map[id]
                    <= old(self).sync_requests.sync_target_lsn as nat);
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.superblocking_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.superblocking_reqs@[i]
                ] <= self.state().journal.persistent_seq_end by {
                let id = self.sync_requests.superblocking_reqs@[i];
                assert(id != req.id) by {
                    if id == req.id {
                        assert(self.sync_requests.superblocking_reqs@
                            == old(self).sync_requests.superblocking_reqs@);
                        let j = old(self).sync_requests.journal_cleaning_reqs@.len() as int + i;
                        assert(0 <= j < old_ids.len());
                        assert(old_ids[j] == id);
                        assert(old_ids.contains(id));
                        assert(old_ids.to_set().contains(req.id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id] == pre_state.state.sync_req_map[id]);
                assert(old(self).state().sync_req_map[id]
                    <= old(self).state().journal.persistent_seq_end);
            }
            reveal(Implementation::sync_wf);
            assert(self.sync_wf());
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            assert(self.inv_api(api));
        }
        api.log("unified-cache sync request buffered");
    }

    fn choose_preferred_sync_flavor(sync_counter: &mut u64) -> (out: SyncFlavor)
    {
        if *sync_counter >= BRANCH_SYNC_INTERVAL - 1 {
            *sync_counter = 0;
            SyncFlavor::BranchAndEmptyJournal
        } else {
            *sync_counter = *sync_counter + 1;
            SyncFlavor::JournalOnly
        }
    }

    fn record_deliver_completed_sync_reply(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).in_flight_sync is None,
            old(self).sync_requests.superblocking_reqs@.len() > 0,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            progress,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_sync = self.sync_requests;
        let sync_req_id = self.sync_requests.pop_superblocking();
        let ghost post_state = UnifiedCacheProgramModel{
            state: UnifiedCacheSystem::State{
                sync_req_map: pre_state.state.sync_req_map.remove(sync_req_id),
                ..pre_state.state
            }
        };
        let tracked mut model = KVStoreTokenized::model::arbitrary();

        proof {
            reveal(Implementation::sync_wf);
            assert(pre_state.state.client_ready());
            assert(pre_sync.all_ids().to_set().contains(sync_req_id));
            assert(pre_state.state.sync_req_map.contains_key(sync_req_id));
            assert(pre_state.state.sync_req_map[sync_req_id]
                <= pre_state.state.journal.persistent_seq_end) by {
                let i = (pre_sync.superblocking_reqs@.len() - 1) as int;
                assert(0 <= i < pre_sync.superblocking_reqs@.len());
                assert(pre_sync.superblocking_reqs@[i] == sync_req_id);
                assert(pre_state.state.sync_req_map[
                    pre_sync.superblocking_reqs@[i]
                ] <= pre_state.state.journal.persistent_seq_end);
            }
            assert(UnifiedCacheSystem::State::deliver_sync_reply(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::DeliverSyncReply{sync_req_id},
            )) by {
            }
            assert(UnifiedCacheSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::DeliverSyncReply{sync_req_id},
                UnifiedCacheSystem::Step::deliver_sync_reply(),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            assert(UnifiedCacheSystem::State::next(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::DeliverSyncReply{sync_req_id},
            )) by {
                reveal(UnifiedCacheSystem::State::next);
            }
            assert(ProgramModelTrait::next(
                pre_state,
                post_state,
                ProgramLabel::UserIO{
                    op: ProgramUserOp::DeliverSyncReply{sync_req_id},
                },
            ));
            tracked_swap(self.model.borrow_mut(), &mut model);
        }

        let tracked reply_token = self.instance.borrow().deliver_sync_reply(
            KVStoreTokenized::Label::ReplySyncOp{sync_req_id},
            post_state,
            &mut model,
        );
        self.model = Tracked(model);
        let reply = Reply{id: sync_req_id, output: Output::SyncOutput};

        proof {
            assert(!self.sync_requests.all_ids().to_set().contains(sync_req_id)) by {
                assert(self.sync_requests.all_ids().to_set()
                    =~= pre_sync.all_ids().to_set().remove(sync_req_id));
            }
            assert(self.in_flight_sync is None);
            assert(self.state().sync_phase is None);
            assert(self.sync_requests.ids_unique());
            assert(self.sync_requests.all_ids().to_set()
                =~= self.state().sync_req_map.dom()) by {
                assert(self.sync_requests.all_ids().to_set()
                    =~= pre_sync.all_ids().to_set().remove(sync_req_id));
                assert(self.state().sync_req_map.dom()
                    =~= pre_state.state.sync_req_map.dom().remove(sync_req_id));
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.buffered_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.buffered_reqs@[i]
                ] <= self.state().branch.seq_end() by {
                let id = self.sync_requests.buffered_reqs@[i];
                assert(id != sync_req_id) by {
                    if id == sync_req_id {
                        let j = self.sync_requests.journal_cleaning_reqs@.len() as int
                            + self.sync_requests.superblocking_reqs@.len() as int + i;
                        assert(0 <= j < self.sync_requests.all_ids().len());
                        assert(self.sync_requests.all_ids()[j] == sync_req_id);
                        assert(self.sync_requests.all_ids().to_set().contains(sync_req_id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id] == pre_state.state.sync_req_map[id]);
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.journal_cleaning_reqs@[i]
                ] <= self.sync_requests.sync_target_lsn as nat by {
                let id = self.sync_requests.journal_cleaning_reqs@[i];
                assert(id != sync_req_id) by {
                    if id == sync_req_id {
                        assert(self.sync_requests.all_ids()[i] == sync_req_id);
                        assert(self.sync_requests.all_ids().to_set().contains(sync_req_id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id] == pre_state.state.sync_req_map[id]);
            }
            assert forall |i: int|
                0 <= i < self.sync_requests.superblocking_reqs@.len()
                implies #[trigger] self.state().sync_req_map[
                    self.sync_requests.superblocking_reqs@[i]
                ] <= self.state().journal.persistent_seq_end by {
                let id = self.sync_requests.superblocking_reqs@[i];
                assert(id != sync_req_id) by {
                    if id == sync_req_id {
                        let j = self.sync_requests.journal_cleaning_reqs@.len() as int + i;
                        assert(0 <= j < self.sync_requests.all_ids().len());
                        assert(self.sync_requests.all_ids()[j] == sync_req_id);
                        assert(self.sync_requests.all_ids().to_set().contains(sync_req_id));
                        assert(false);
                    }
                }
                assert(self.state().sync_req_map[id] == pre_state.state.sync_req_map[id]);
                let old_i = i;
                assert(pre_sync.superblocking_reqs@[old_i]
                    == self.sync_requests.superblocking_reqs@[i]);
                assert(pre_state.state.sync_req_map[
                    pre_sync.superblocking_reqs@[old_i]
                ] <= pre_state.state.journal.persistent_seq_end);
            }
            reveal(Implementation::sync_wf);
            assert(self.sync_wf());
            reveal(Implementation::inv_api);
            reveal(Implementation::inv);
            assert(self.inv_api(api));
        }

        api.send_reply(reply, Tracked(reply_token), true);
        api.log("unified-cache sync reply delivered");
        true
    }

    fn launch_frozen_sync(
        &mut self,
        flavor: SyncFlavor,
        frozen: FrozenJournal,
        journal_reads: Ghost<Map<Address, RawPage>>,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            old(self).sync_requests.journal_cleaning_reqs@.len() > 0,
            old(self).sync_requests.superblocking_reqs@.len() == 0,
            old(self).in_flight_sync is None,
            old(self).state().sync_phase is None,
            old(self).state().journal.in_flight is None,
            old(self).branch.commit_phase is Idle,
            old(self).journal.clean_watermark() == old(self).journal.marshalled_seq_end(),
            frozen.wf(),
            frozen.geometry_bounded(old(self).disk_au_count),
            frozen.seq_end as nat <= old(self).journal.clean_watermark(),
            old(self).state().journal.persistent_seq_end <= frozen.seq_end as nat,
            old(self).sync_requests.sync_target_lsn <= frozen.seq_end,
            match flavor {
                SyncFlavor::JournalOnly => {
                    &&& old(self).pending_branch_sync is None
                    &&& frozen.seq_start() as nat == old(self).journal.seq_start()
                    &&& frozen.seq_end as nat == old(self).journal.clean_watermark()
                },
                SyncFlavor::BranchAndEmptyJournal => {
                    &&& old(self).pending_branch_sync is Some
                    &&& old(self).pending_branch_sync.unwrap() is Ready
                    &&& old(self).branch.active_branch is None
                    &&& old(self).branch.persisted_root_count
                        == old(self).branch.image.sealed_roots.len()
                    &&& frozen.snapshot.freshest_rec is None
                    &&& frozen.seq_start() as nat == old(self).branch@.seq_end()
                    &&& frozen.seq_end as nat == old(self).branch@.seq_end()
                    &&& journal_reads@ == Map::<Address, RawPage>::empty()
                },
            },
            Cache::State::next(
                old(self).state().cache,
                old(self).cache@,
                Cache::Label::Access{reads: journal_reads@, writes: Map::empty()},
            ),
            CachedJournal::State::next(
                old(self).journal@,
                old(self).journal@,
                CachedJournal::Label::FreezeForCommit{
                    frozen: frozen.snapshot@,
                    reads: to_journal_records(journal_reads@),
                },
            ),
            frozen.snapshot@.freshest_rec() is Some ==> {
                let root = frozen.snapshot@.freshest_rec().unwrap();
                &&& journal_reads@.contains_key(root)
                &&& to_journal_records(journal_reads@)[root].message_seq.seq_end
                    == frozen.seq_end as nat
            },
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            !progress ==> self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost _journal_sync_disk = self.unified_system_inv_journal_pages_parsable();
        let discarded_aus = match flavor {
            SyncFlavor::JournalOnly => Vec::<IAU>::new(),
            SyncFlavor::BranchAndEmptyJournal => self.journal.indexed_aus(),
        };
        let ghost discarded_aus_seq = discarded_aus@;
        let ghost pre_state = self.model@.value();
        let ghost pre_branch = self.branch@;
        let ghost pre_journal = self.journal@;
        let roots = match flavor {
            SyncFlavor::JournalOnly => self.branch.persistent_roots(),
            SyncFlavor::BranchAndEmptyJournal => self.branch.all_roots(),
        };
        let prefix_len = roots.len();
        let branch_seq_end = match flavor {
            SyncFlavor::JournalOnly => self.branch.persistent_seq_end,
            SyncFlavor::BranchAndEmptyJournal => self.branch.seq_end,
        };
        let image = ISuperblock {
            geometry: crate::implementation::SuperblockTypes_v::ISuperblockGeometry {
                pages_per_au: self.disk_page_count,
                formatted_au_count: self.disk_au_count,
            },
            payload: crate::implementation::SuperblockTypes_v::ISuperblockPayload {
                journal: ISuperblockJournalImage {
                    snapshot: frozen.snapshot,
                    seq_end: frozen.seq_end,
                },
                branch: ISuperblockBranchImage {
                    roots,
                    betree: ISuperblockBetreeImage {
                        root: None,
                        seq_end: branch_seq_end as u64,
                    },
                },
            },
        };
        let layout = DiskLayout::new();
        if !layout.can_marshall(&image) {
            proof {
                assert(self.inv_api(api));
            }
            return false;
        }

        let start_result = self.branch.commit_start(prefix_len, branch_seq_end);
        match start_result {
            Ok(()) => {},
            Err(_) => {
                proof {
                    match flavor {
                        SyncFlavor::JournalOnly => {
                            assert(prefix_len == old(self).branch.persistent_prefix_len) by {
                                assert(roots@ == old(self).branch.image.sealed_roots@.take(
                                    old(self).branch.persistent_prefix_len as int,
                                ));
                            }
                            assert(branch_seq_end == old(self).branch.persistent_seq_end);
                        },
                        SyncFlavor::BranchAndEmptyJournal => {
                            assert(prefix_len == old(self).branch.image.sealed_roots.len());
                            assert(branch_seq_end == old(self).branch.seq_end);
                            assert(old(self).branch.active_branch is None);
                        },
                    }
                    assert(false);
                }
                unreached()
            },
        }
        let ghost started_branch = self.branch@;

        let ghost abstract_image = image@@;
        let ghost journal_lbl = AtomicJournalState::Label::CommitStart {
            snapshot: abstract_image.journal_snapshot,
            seq_end: abstract_image.journal_seq_end,
            reads: to_journal_records(journal_reads@),
        };
        let ghost started_journal = AtomicJournalState::State {
            in_flight: Some(AtomicJournalImage {
                snapshot: abstract_image.journal_snapshot,
                seq_end: abstract_image.journal_seq_end,
            }),
            prepared: false,
            ..pre_state.state.journal
        };
        let ghost begin_program = UnifiedCacheProgramModel {
            state: UnifiedCacheSystem::State {
                cache: self.cache@,
                journal: started_journal,
                branch: started_branch,
                sync_phase: AtomicSyncPhase::Started{image: abstract_image},
                ..pre_state.state
            }
        };
        let ghost empty_disk_requests = Multiset::empty();
        let ghost empty_disk_responses = Multiset::empty();
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
            assert(abstract_image.wf()) by {
                assert(abstract_image.branch_seq_end
                    == abstract_image.journal_snapshot.boundary_lsn) by {
                    match flavor {
                        SyncFlavor::JournalOnly => {
                            assert(old(self).persistent_component_alignment());
                            assert(branch_seq_end as nat == old(self).journal.seq_start());
                            assert(frozen.seq_start() as nat == old(self).journal.seq_start());
                        },
                        SyncFlavor::BranchAndEmptyJournal => {
                            assert(branch_seq_end as nat == old(self).branch@.seq_end());
                            assert(frozen.seq_start() as nat == old(self).branch@.seq_end());
                        },
                    }
                }
                assert forall |i: int| 0 <= i < abstract_image.branch_roots.len()
                    implies #[trigger] abstract_image.branch_roots[i].wf() by {
                    match flavor {
                        SyncFlavor::JournalOnly => {
                            assert(abstract_image.branch_roots
                                == pre_branch.image.sealed_roots.take(
                                    old(self).branch.persistent_prefix_len as int,
                                ));
                            assert(abstract_image.branch_roots
                                == pre_branch.persistent_image.sealed_roots);
                            assert(pre_state.state.persistent_image is Some);
                            assert(pre_branch.persistent_image.sealed_roots
                                == pre_state.state.persistent_image.unwrap().branch_roots);
                            assert(pre_state.state.persistent_image.unwrap().wf());
                        },
                        SyncFlavor::BranchAndEmptyJournal => {
                            assert(abstract_image.branch_roots == pre_branch.image.sealed_roots);
                            assert(old(self).branch.image.roots_wf());
                        },
                    }
                }
            }
            assert(pre_state.state.sync_image_metadata_valid(abstract_image)) by {
                assert(pre_state.state.branch == pre_branch);
                match flavor {
                    SyncFlavor::JournalOnly => {
                        assert(abstract_image.branch_roots
                            == pre_branch.image.sealed_roots.take(
                                old(self).branch.persistent_prefix_len as int,
                            ));
                        assert(old(self).branch.persistent_prefix_len
                            <= old(self).branch.persisted_root_count);
                    },
                    SyncFlavor::BranchAndEmptyJournal => {
                        assert(abstract_image.branch_roots == pre_branch.image.sealed_roots);
                        assert(old(self).branch.persisted_root_count
                            == old(self).branch.image.sealed_roots.len());
                        assert(pre_branch.image.sealed_roots.take(
                            pre_branch.image.sealed_roots.len() as int,
                        ) == pre_branch.image.sealed_roots);
                    },
                }
                assert(abstract_image.journal_seq_end
                    <= pre_state.state.journal.journal.seq_end()) by {
                    assert(abstract_image.journal_seq_end
                        <= old(self).journal.marshalled_seq_end());
                    old(self).journal.marshalled_seq_end_le_seq_end();
                    assert(old(self).journal.marshalled_seq_end()
                        <= old(self).journal.seq_end());
                    old(self).journal.view_seq_end_ensures();
                }
            }
            assert(AtomicJournalState::State::commit_start(
                pre_state.state.journal,
                started_journal,
                journal_lbl,
            )) by {
                assert(pre_state.state.journal.in_flight is None);
                assert(pre_state.state.journal.persistent_seq_end
                    <= abstract_image.journal_seq_end);
                assert(abstract_image.journal_snapshot.boundary_lsn
                    <= abstract_image.journal_seq_end);
                assert(abstract_image.journal_seq_end
                    == crate::implementation::AtomicJournalState_v::journal_snapshot_seq_end_from_reads(
                        abstract_image.journal_snapshot,
                        to_journal_records(journal_reads@),
                    )) by {
                    if abstract_image.journal_snapshot.freshest_rec() is Some {
                        let root = abstract_image.journal_snapshot.freshest_rec().unwrap();
                        assert(to_journal_records(journal_reads@)[root].message_seq.seq_end
                            == abstract_image.journal_seq_end);
                    } else {
                        assert(abstract_image.journal_seq_end
                            == abstract_image.journal_snapshot.boundary_lsn);
                    }
                }
                assert(pre_state.state.journal.journal == pre_journal);
                if abstract_image.journal_snapshot.freshest_rec() is None {
                    assert(abstract_image.journal_seq_end
                        == abstract_image.journal_snapshot.boundary_lsn);
                }
            }
            assert(AtomicJournalState::State::next_by(
                pre_state.state.journal,
                started_journal,
                journal_lbl,
                AtomicJournalState::Step::commit_start(),
            )) by {
                reveal(AtomicJournalState::State::next_by);
            }
            assert(AtomicJournalState::State::next(
                pre_state.state.journal,
                started_journal,
                journal_lbl,
            )) by {
                reveal(AtomicJournalState::State::next);
            }
            assert(AtomicBranchState::State::next(
                pre_state.state.branch,
                started_branch,
                crate::implementation::AtomicBranchState_v::AtomicBranchState::Label::CommitStart {
                    branch_image: crate::implementation::AtomicBranchState_v::AtomicBranchImage {
                        sealed_roots: abstract_image.branch_roots,
                        seq_end: abstract_image.branch_seq_end,
                    },
                },
            ));
            assert(UnifiedCacheSystem::State::execute_sync_begin(
                pre_state.state,
                begin_program.state,
                UnifiedCacheSystem::Label::Disk,
                abstract_image,
                journal_reads@,
                self.cache@,
                started_journal,
                started_branch,
                empty_disk_requests,
                empty_disk_responses,
            )) by {
            }
            assert(UnifiedCacheSystem::State::next_by(
                pre_state.state,
                begin_program.state,
                UnifiedCacheSystem::Label::Disk,
                UnifiedCacheSystem::Step::execute_sync_begin(
                    abstract_image,
                    journal_reads@,
                    self.cache@,
                    started_journal,
                    started_branch,
                    empty_disk_requests,
                    empty_disk_responses,
                ),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            let info = ProgramDiskInfo{reqs: empty_disk_requests, resps: empty_disk_responses};
            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheSystem::Step::execute_sync_begin(
                    abstract_image,
                    journal_reads@,
                    self.cache@,
                    started_journal,
                    started_branch,
                    empty_disk_requests,
                    empty_disk_responses,
                ),
                info,
            ));
            UnifiedCacheProgramModel::lift_disk_step(pre_state, begin_program, info);
        }
        let tracked empty_response_shard = DiskRespShard::empty(self.instance_id());
        let tracked _empty_request_shard = self.instance.borrow().disk_transitions(
            KVStoreTokenized::Label::DiskOp {
                disk_request_tuples: empty_disk_requests,
                disk_response_tuples: empty_disk_responses,
            },
            begin_program,
            &mut model,
            empty_response_shard,
        );

        proof {
            assert(self.branch.load_state is MetadataLoaded);
            assert(self.branch.commit_phase is InFlight);
            assert(!self.branch.commit_phase->prepared);
            assert(self.branch.commit_phase->prefix_len <= self.branch.persisted_root_count) by {
                assert(self.branch.commit_phase->prefix_len == prefix_len);
                match flavor {
                    SyncFlavor::JournalOnly => {
                        assert(prefix_len == old(self).branch.persistent_prefix_len);
                        assert(old(self).branch.persistent_prefix_len
                            <= old(self).branch.persisted_root_count);
                    },
                    SyncFlavor::BranchAndEmptyJournal => {
                        assert(prefix_len == old(self).branch.image.sealed_roots.len());
                        assert(old(self).branch.persisted_root_count
                            == old(self).branch.image.sealed_roots.len());
                    },
                }
                assert(self.branch.persisted_root_count == old(self).branch.persisted_root_count);
            }
        }
        let prepared_result = self.branch.commit_prepared();
        match prepared_result {
            Ok(()) => {},
            Err(_) => {
                proof { assert(false); }
                unreached()
            },
        }
        let ghost prepared_branch = self.branch@;
        let ghost prepared_journal = AtomicJournalState::State {
            prepared: true,
            ..started_journal
        };

        proof {
            assert(image@.geometry.wf()) by {
                assert(image@.geometry.pages_per_au
                    == self.disk_page_count as nat);
                assert(self.disk_page_count as nat == page_count());
                assert(image@.geometry.formatted_au_count
                    == self.disk_au_count as nat);
                assert(1 < self.disk_au_count as nat);
            }
            assert(image@.payload.wf()) by {
                assert(image@.payload@ == abstract_image);
                assert(abstract_image.wf());
            }
            assert(image@.addresses_bounded()) by {
                assert(image@.payload.journal.snapshot == frozen.snapshot@);
                assert(frozen.geometry_bounded(self.disk_au_count));
                assert forall |i: int|
                    0 <= i < image@.payload.branch.roots.len()
                    implies #[trigger] image@.payload.branch.roots[i].au
                        < self.disk_au_count as nat by {
                    match flavor {
                        SyncFlavor::JournalOnly => {
                            assert(image@.payload.branch.roots
                                == self.branch.image@.sealed_roots.take(
                                    self.branch.persistent_prefix_len as int,
                                ));
                            assert(self.branch.image.roots_bounded(
                                self.disk_au_count,
                            ));
                        },
                        SyncFlavor::BranchAndEmptyJournal => {
                            assert(image@.payload.branch.roots
                                == self.branch.image@.sealed_roots);
                            assert(self.branch.image.roots_bounded(
                                self.disk_au_count,
                            ));
                        },
                    }
                }
            }
            assert(image@.wf());
        }
        let raw_page = layout.marshall(&image);
        let req_id_perm = Tracked(api.send_disk_request_predict_id());
        let disk_req = IDiskRequest::WriteReq {
            to: superblock_addr(),
            data: raw_page,
        };
        let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
        let ghost disk_response_tuples = Multiset::empty();
        let ghost prepared_program = UnifiedCacheProgramModel {
            state: UnifiedCacheSystem::State {
                journal: prepared_journal,
                branch: prepared_branch,
                sync_phase: AtomicSyncPhase::SuperblockWriteIssued {
                    req_id: req_id_perm@,
                    image: abstract_image,
                },
                ..begin_program.state
            }
        };
        proof {
            assert(AtomicJournalState::State::commit_prepared(
                started_journal,
                prepared_journal,
                AtomicJournalState::Label::CommitPrepared,
            )) by {
                assert(started_journal.in_flight is Some);
                assert(started_journal.journal.status is Some);
                assert(abstract_image.journal_seq_end
                    <= started_journal.journal.clean_watermark()) by {
                    assert(started_journal.journal == pre_journal);
                    assert(abstract_image.journal_seq_end
                        <= old(self).journal.clean_watermark());
                    old(self).journal.view_clean_watermark_ensures();
                    assert(pre_journal.clean_watermark()
                        == old(self).journal.clean_watermark());
                }
            }
            assert(AtomicJournalState::State::next_by(
                started_journal,
                prepared_journal,
                AtomicJournalState::Label::CommitPrepared,
                AtomicJournalState::Step::commit_prepared(),
            )) by {
                reveal(AtomicJournalState::State::next_by);
            }
            assert(AtomicJournalState::State::next(
                started_journal,
                prepared_journal,
                AtomicJournalState::Label::CommitPrepared,
            )) by {
                reveal(AtomicJournalState::State::next);
            }
            assert(AtomicBranchState::State::next(
                started_branch,
                prepared_branch,
                crate::implementation::AtomicBranchState_v::AtomicBranchState::Label::CommitPrepared,
            ));
            assert(image@@.wf());
            assert(superblock_matches(disk_req@->data, abstract_image));
            multiset_map_singleton_ensures(req_id_perm@, disk_req@);
            assert(disk_request_tuples
                == Multiset::singleton((req_id_perm@, disk_req@))) by {
                assert(disk_request_tuples
                    == Multiset::empty().insert((req_id_perm@, disk_req@)));
            }
            assert(UnifiedCacheSystem::State::execute_sync_prepared(
                begin_program.state,
                prepared_program.state,
                UnifiedCacheSystem::Label::Disk,
                req_id_perm@,
                disk_req@,
                prepared_journal,
                prepared_branch,
                disk_request_tuples,
                disk_response_tuples,
            )) by {
            }
            assert(UnifiedCacheSystem::State::next_by(
                begin_program.state,
                prepared_program.state,
                UnifiedCacheSystem::Label::Disk,
                UnifiedCacheSystem::Step::execute_sync_prepared(
                    req_id_perm@,
                    disk_req@,
                    prepared_journal,
                    prepared_branch,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            let info = ProgramDiskInfo{reqs: disk_request_tuples, resps: disk_response_tuples};
            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                begin_program.state,
                UnifiedCacheSystem::Step::execute_sync_prepared(
                    req_id_perm@,
                    disk_req@,
                    prepared_journal,
                    prepared_branch,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
                info,
            ));
            UnifiedCacheProgramModel::lift_disk_step(begin_program, prepared_program, info);
        }
        let tracked empty_response_shard = DiskRespShard::empty(self.instance_id());
        let tracked request_shard = self.instance.borrow().disk_transitions(
            KVStoreTokenized::Label::DiskOp {
                disk_request_tuples,
                disk_response_tuples,
            },
            prepared_program,
            &mut model,
            empty_response_shard,
        );
        self.model = Tracked(model);

        let id = api.send_disk_request(disk_req, req_id_perm, Tracked(request_shard));
        self.sync_requests.move_cleaning_to_superblocking();
        self.pending_branch_sync = None;
        self.outstanding_requests.insert(id, OutstandingReqInfo::SuperblockWrite);
        self.in_flight_sync = Some(InFlightSync {
            flavor,
            image,
            req_id: id,
            discarded_aus,
        });
        proof {
            assert(id == req_id_perm@);
            assert(self.pending_branch_sync is None);
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model()) by {
                reveal(Implementation::outstanding_cache_reqs_match_model);
                assert(self.state().outstanding_cache_reqs
                    == Map::<ID, Address>::empty());
            }
            assert(self.outstanding_requests_single_flight());
            assert(self.persistent_component_alignment()) by {
                reveal(Implementation::persistent_component_alignment);
                assert(self.branch.persistent_seq_end == old(self).branch.persistent_seq_end);
                assert(self.journal == old(self).journal);
                assert(old(self).persistent_component_alignment());
            }
            assert(self.sync_wf()) by {
                reveal(Implementation::sync_wf);
                assert forall |i: int| 0 <= i < discarded_aus_seq.len()
                    implies 0 < #[trigger] (discarded_aus_seq[i] as nat)
                        < (self.disk_au_count as nat) by {
                    match flavor {
                        SyncFlavor::JournalOnly => assert(false),
                        SyncFlavor::BranchAndEmptyJournal => {
                            assert(iau_vec_set(discarded_aus_seq).contains(
                                discarded_aus_seq[i] as nat,
                            ));
                            assert(old(self).journal@.status.unwrap().lsn_au_index.values().contains(
                                discarded_aus_seq[i] as nat,
                            ));
                        },
                    }
                }
                match flavor {
                    SyncFlavor::JournalOnly => {
                        assert(discarded_aus_seq.len() == 0);
                    },
                    SyncFlavor::BranchAndEmptyJournal => {
                        assert(iau_vec_set(discarded_aus_seq) =~=
                            old(self).journal@.status.unwrap().lsn_au_index.values());
                        assert(self.state().journal.journal == old(self).state().journal.journal);
                        assert(self.state().journal.loaded_index_aus()
                            == old(self).state().journal.loaded_index_aus());
                        assert(old(self).state().journal.journal == old(self).journal@);
                        assert(frozen.seq_end as nat == old(self).branch@.seq_end());
                        assert(old(self).live_component_alignment());
                        assert(frozen.seq_end as nat == old(self).journal.seq_end());
                        old(self).journal.clean_watermark_le_marshaled_seq_end();
                        old(self).journal.marshalled_seq_end_le_seq_end();
                        assert(old(self).journal.marshalled_seq_end()
                            == frozen.seq_end as nat);
                        assert(self.journal == old(self).journal);
                    },
                }
                assert(self.sync_requests.all_ids() == old(self).sync_requests.all_ids());
                assert(self.sync_requests.all_ids().to_set()
                    =~= self.state().sync_req_map.dom());
                assert(self.state().sync_req_map == old(self).state().sync_req_map);
                assert(self.state().branch.seq_end() == old(self).state().branch.seq_end()) by {
                    let start_lbl = AtomicBranchState::Label::CommitStart {
                        branch_image: crate::implementation::AtomicBranchState_v::AtomicBranchImage {
                            sealed_roots: abstract_image.branch_roots,
                            seq_end: abstract_image.branch_seq_end,
                        },
                    };
                    AtomicBranchState::State::commit_start_effect(
                        pre_branch,
                        started_branch,
                        start_lbl,
                    );
                    AtomicBranchState::State::commit_prepared_effect(
                        started_branch,
                        prepared_branch,
                        AtomicBranchState::Label::CommitPrepared,
                    );
                    assert(self.state().branch == prepared_branch);
                    assert(prepared_branch.seq_end == started_branch.seq_end);
                    assert(started_branch.seq_end == pre_branch.seq_end);
                    assert(pre_state.state.branch == pre_branch);
                }
                assert forall |i: int| 0 <= i < self.sync_requests.buffered_reqs@.len()
                    implies #[trigger] self.state().sync_req_map[
                        self.sync_requests.buffered_reqs@[i]
                    ] <= self.state().branch.seq_end() by {
                    assert(self.sync_requests.buffered_reqs@
                        == old(self).sync_requests.buffered_reqs@);
                    assert(old(self).state().sync_req_map[
                        old(self).sync_requests.buffered_reqs@[i]
                    ] <= old(self).state().branch.seq_end());
                }
                assert forall |i: int| 0 <= i < self.sync_requests.superblocking_reqs@.len()
                    implies #[trigger] self.state().sync_req_map[
                        self.sync_requests.superblocking_reqs@[i]
                    ] <= self.in_flight_sync.unwrap().image@@.journal_seq_end by {
                    assert(self.sync_requests.superblocking_reqs@
                        == old(self).sync_requests.journal_cleaning_reqs@);
                    assert(old(self).state().sync_req_map[
                        old(self).sync_requests.journal_cleaning_reqs@[i]
                    ] <= old(self).sync_requests.sync_target_lsn as nat);
                    assert(old(self).sync_requests.sync_target_lsn as nat
                        <= abstract_image.journal_seq_end);
                }
            }
            assert(self.inv_api(api));
        }
        api.log("unified-cache superblock write issued");
        true
    }

    fn poll_sync_preparation(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            !progress ==> self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        if !self.outstanding_requests.is_empty() {
            return false;
        }
        proof {
            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                assert_maps_equal!(
                    self.outstanding_requests@,
                    Map::<ID, OutstandingReqInfo>::empty(),
                    id => {
                        if self.outstanding_requests@.contains_key(id) {
                            assert(!self.outstanding_requests@.is_empty());
                            assert(false);
                        }
                    }
                );
            }
            assert(self.in_flight_sync is None) by {
                if self.in_flight_sync is Some {
                    let in_flight = self.in_flight_sync.unwrap();
                    assert(self.outstanding_requests@.contains_key(in_flight.req_id));
                    assert(false);
                }
            }
        }

        if self.sync_requests.superblocking_reqs.len() > 0 {
            return false;
        }
        proof {
            assert(self.sync_requests.superblocking_reqs@.len() == 0);
        }

        if self.sync_requests.journal_cleaning_reqs.len() == 0 {
            if self.sync_requests.buffered_reqs.len() == 0 {
                return false;
            }

            let ghost pre_sync = self.sync_requests;
            let target_lsn = self.branch.exec_seq_end();
            let preferred = Self::choose_preferred_sync_flavor(&mut self.sync_counter);
            proof {
                assert(self.sync_requests.journal_cleaning_reqs@.len() == 0);
                assert(self.in_flight_sync is None);
                assert(self.sync_requests.superblocking_reqs@.len() == 0);
            }
            self.sync_requests.promote_buffered(target_lsn);
            match preferred {
                SyncFlavor::BranchAndEmptyJournal => {
                    if self.branch.persisted_root_count == self.branch.image.sealed_roots.len() {
                        self.pending_branch_sync = Some(PendingBranchSync::SealPending);
                        api.log("unified-cache branch sync preparation started");
                    } else {
                        self.pending_branch_sync = None;
                        api.log("unified-cache branch sync deferred until roots are persisted");
                    }
                },
                SyncFlavor::JournalOnly => {
                    self.pending_branch_sync = None;
                },
            }

            proof {
                assert(self.state() == old(self).state());
                assert(self.in_flight_sync is None);
                assert(self.state().sync_phase is None);
                assert(self.sync_requests.superblocking_reqs@.len() == 0);
                assert(self.sync_requests.ids_unique());
                assert(self.sync_requests.all_ids().to_set()
                    =~= self.state().sync_req_map.dom()) by {
                    assert(self.sync_requests.all_ids() == pre_sync.all_ids());
                    assert(pre_sync.all_ids().to_set()
                        =~= old(self).state().sync_req_map.dom());
                }
                assert forall |i: int|
                    0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
                    implies #[trigger] self.state().sync_req_map[
                        self.sync_requests.journal_cleaning_reqs@[i]
                    ] <= self.sync_requests.sync_target_lsn as nat by {
                    assert(self.sync_requests.journal_cleaning_reqs@
                        == pre_sync.buffered_reqs@);
                    assert(self.sync_requests.sync_target_lsn as nat
                        == self.state().branch.seq_end());
                    assert(old(self).state().sync_req_map[
                        pre_sync.buffered_reqs@[i]
                    ] <= old(self).state().branch.seq_end());
                }
                assert forall |i: int| 0 <= i < self.sync_requests.buffered_reqs@.len()
                    implies #[trigger] self.state().sync_req_map[
                        self.sync_requests.buffered_reqs@[i]
                    ] <= self.state().branch.seq_end() by {
                    assert(false);
                }
                reveal(Implementation::sync_wf);
                assert(self.sync_wf());
                reveal(Implementation::inv_api);
                reveal(Implementation::inv);
                assert(self.inv_api(api));
            }
            return true;
        }

        let branch_preparation_needed = match &self.pending_branch_sync {
            Some(PendingBranchSync::Ready) | None => false,
            Some(_) => true,
        };
        if branch_preparation_needed {
            return self.poll_branch_sync_preparation(api);
        }

        let current_branch_lsn = self.branch.exec_seq_end();
        if self.sync_requests.sync_target_lsn < current_branch_lsn {
            let ghost pre_sync = self.sync_requests;
            self.sync_requests.raise_cleaning_target(current_branch_lsn);
            proof {
                assert(self.state() == old(self).state());
                assert(self.sync_requests.all_ids() == pre_sync.all_ids());
                assert(self.sync_requests.ids_unique());
                assert forall |i: int|
                    0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
                    implies #[trigger] self.state().sync_req_map[
                        self.sync_requests.journal_cleaning_reqs@[i]
                    ] <= self.sync_requests.sync_target_lsn as nat by {
                    assert(old(self).state().sync_req_map[
                        pre_sync.journal_cleaning_reqs@[i]
                    ] <= pre_sync.sync_target_lsn as nat);
                    assert(pre_sync.sync_target_lsn <= current_branch_lsn);
                }
                reveal(Implementation::sync_wf);
                assert(self.sync_wf());
                reveal(Implementation::inv_api);
                reveal(Implementation::inv);
                assert(self.inv_api(api));
            }
            return true;
        }

        let target_lsn = self.sync_requests.sync_target_lsn;
        if self.persistent_journal_seq_end > target_lsn {
            return false;
        }
        let marshalled = self.journal.exec_marshaled_seq_end();
        if marshalled < target_lsn {
            return self.record_journal_marshall_step(api);
        }

        let clean = self.journal.exec_clean_watermark();
        if clean < marshalled {
            return self.record_journal_writeback_for_target(api);
        }

        if self.pending_branch_sync.is_some() {
            let ghost _sync_system = self.unified_system_inv_journal_pages_parsable();
            let branch_boundary = self.branch.exec_seq_end();
            let frozen_journal = FrozenJournal::empty_at(branch_boundary);
            let ghost reads = Map::<Address, RawPage>::empty();
            proof {
                assert(frozen_journal.snapshot@.boundary_lsn == branch_boundary as nat);
                assert(frozen_journal.snapshot@.freshest_rec() is None);
                self.journal.view_snapshot_ensures();
                self.journal.view_seq_start_ensures();
                self.journal.view_seq_end_ensures();
                assert(self.journal@.snapshot.boundary_lsn == self.journal.seq_start());
                assert(self.journal@.seq_end() == self.journal.seq_end());
                assert(self.pending_branch_sync.unwrap() is Ready);
                assert(self.live_component_alignment());
                assert(branch_boundary as nat == self.journal.seq_end());
                assert(self.journal.seq_start() <= self.journal.seq_end());
                assert(self.journal.seq_start() <= branch_boundary as nat);
                assert(branch_boundary as nat <= self.journal.seq_end());
                assert(self.journal@.seq_start()
                    <= frozen_journal.snapshot@.boundary_lsn);
                assert(frozen_journal.snapshot@.boundary_lsn
                    <= self.journal@.seq_end());
                assert(target_lsn == branch_boundary) by {
                    assert(!(target_lsn < branch_boundary));
                    assert(target_lsn <= self.state().branch.seq_end());
                    assert(self.state().branch == self.branch@);
                }
                self.journal.marshalled_seq_end_le_seq_end();
                assert(marshalled as nat <= self.journal.seq_end());
                assert(marshalled == branch_boundary) by {
                    assert(target_lsn <= marshalled);
                }
                assert(clean == marshalled) by {
                    assert(!(clean < marshalled));
                    self.journal.clean_watermark_le_marshaled_seq_end();
                }
                assert(self.state().journal.persistent_seq_end
                    <= frozen_journal.seq_end as nat) by {
                    assert(self.state().journal.persistent_seq_end
                        == self.persistent_journal_seq_end as nat);
                    assert(self.persistent_journal_seq_end <= target_lsn);
                }
                Cache::State::access_empty_is_noop(self.state().cache);
                assert(self.state().cache == self.cache@);
                assert(Cache::State::next(
                    self.state().cache,
                    self.cache@,
                    Cache::Label::Access{reads, writes: Map::empty()},
                ));
                reveal(CachedJournal::State::next);
                reveal(CachedJournal::State::next_by);
                assert(CachedJournal::State::freeze_for_commit(
                    self.journal@,
                    self.journal@,
                    CachedJournal::Label::FreezeForCommit{
                        frozen: frozen_journal.snapshot@,
                        reads: to_journal_records(reads),
                    },
                )) by {
                    assert(self.journal.seq_start() <= branch_boundary as nat) by {
                        assert(self.persistent_component_alignment());
                        assert(self.branch.persistent_seq_end <= self.branch.seq_end);
                    }
                }
                assert(CachedJournal::State::next_by(
                    self.journal@,
                    self.journal@,
                    CachedJournal::Label::FreezeForCommit{
                        frozen: frozen_journal.snapshot@,
                        reads: to_journal_records(reads),
                    },
                    CachedJournal::Step::freeze_for_commit(),
                ));
                assert(CachedJournal::State::next(
                    self.journal@,
                    self.journal@,
                    CachedJournal::Label::FreezeForCommit{
                        frozen: frozen_journal.snapshot@,
                        reads: to_journal_records(reads),
                    },
                ));
            }
            return self.launch_frozen_sync(
                SyncFlavor::BranchAndEmptyJournal,
                frozen_journal,
                Ghost(reads),
                api,
            );
        }

        let ghost journal_raw_disk = self.unified_system_inv_journal_pages_parsable();
        let freeze = self.journal.freeze_for_commit(marshalled, self.disk_au_count);
        match freeze {
            CleanForCommitResult::NeedsFlush{} => {
                proof {
                    assert(self.journal.clean_watermark() < marshalled as nat);
                    assert(clean as nat == self.journal.clean_watermark());
                    assert(marshalled as nat == self.journal.marshalled_seq_end());
                    assert(false);
                }
                false
            },
            CleanForCommitResult::Frozen{frozen_journal} => {
                proof {
                    assert(clean == marshalled) by {
                        assert(!(clean < marshalled));
                        self.journal.view_clean_watermark_ensures();
                        self.journal.clean_watermark_le_marshaled_seq_end();
                        assert(self.journal.clean_watermark()
                            <= self.journal.marshalled_seq_end());
                    }
                    assert(self.journal.clean_watermark()
                        == self.journal.marshalled_seq_end());
                    assert(self.state().journal.persistent_seq_end
                        == self.persistent_journal_seq_end as nat);
                    assert(self.persistent_journal_seq_end <= target_lsn);
                    assert(target_lsn <= marshalled);
                    assert(frozen_journal.seq_end == clean);
                    assert(self.state().journal.persistent_seq_end
                        <= frozen_journal.seq_end as nat);
                    assert(self.state().branch == self.branch@);
                    assert(self.state().branch.in_flight is None);
                    assert(self.branch.in_flight_i() is None);
                    self.branch.no_in_flight_implies_commit_idle();
                }

                match frozen_journal.snapshot.freshest_rec {
                    None => {
                        let ghost reads = Map::<Address, RawPage>::empty();
                        proof {
                            assert(frozen_journal.snapshot@.freshest_rec() is None);
                            Cache::State::access_empty_is_noop(self.state().cache);
                            assert(self.state().cache == self.cache@);
                            assert(Cache::State::next(
                                self.state().cache,
                                self.cache@,
                                Cache::Label::Access{reads, writes: Map::empty()},
                            ));
                            reveal(CachedJournal::State::next);
                            reveal(CachedJournal::State::next_by);
                            assert(CachedJournal::State::freeze_for_commit(
                                self.journal@,
                                self.journal@,
                                CachedJournal::Label::FreezeForCommit{
                                    frozen: frozen_journal.snapshot@,
                                    reads: to_journal_records(reads),
                                },
                            )) by {
                            }
                            assert(CachedJournal::State::next_by(
                                self.journal@,
                                self.journal@,
                                CachedJournal::Label::FreezeForCommit{
                                    frozen: frozen_journal.snapshot@,
                                    reads: to_journal_records(reads),
                                },
                                CachedJournal::Step::freeze_for_commit(),
                            ));
                            assert(CachedJournal::State::next(
                                self.journal@,
                                self.journal@,
                                CachedJournal::Label::FreezeForCommit{
                                    frozen: frozen_journal.snapshot@,
                                    reads: to_journal_records(reads),
                                },
                            ));
                        }
                        self.launch_frozen_sync(
                            SyncFlavor::JournalOnly,
                            frozen_journal,
                            Ghost(reads),
                            api,
                        )
                    },
                    Some(root) => {
                        proof {
                            assert(frozen_journal.snapshot@.freshest_rec() == Some(root@));
                            assert(frozen_journal.snapshot.freshest_rec
                                == self.journal.snapshot.freshest_rec);
                            assert(crate::implementation::JournalImpl_v::iaddr_view(
                                frozen_journal.snapshot.freshest_rec,
                            ) == Some(root@));
                            assert(crate::implementation::JournalImpl_v::iaddr_view(
                                self.journal.snapshot.freshest_rec,
                            ) == Some(root@));
                            assert(frozen_journal.snapshot@.freshest_rec() == Some(root@));
                            self.journal.view_snapshot_ensures();
                            assert(self.journal@.snapshot == self.journal.snapshot@);
                            assert(self.journal@.snapshot.freshest_rec() == Some(root@));
                            assert(self.journal@.status is Some);
                            assert(root@.wf());
                            assert(root@ != spec_superblock_addr());
                        }
                        let ghost pre_cache = self.cache@;
                        match self.cache.fetch(&root, true) {
                            FetchErrorCode::Success{slot_handle} => {
                                let ghost reads = map![root@ => slot_handle.rec@];
                                proof {
                                    assert(pre_cache.valid_read(root@, slot_handle.rec@));
                                    assert(journal_raw_disk.contains_key(root@));
                                    assert(journal_raw_disk[root@] == slot_handle.rec@);
                                    assert(to_journal_records(reads)[root@]
                                        == to_journal_records(journal_raw_disk)[root@]);
                                    assert(to_journal_records(reads)[root@].message_seq.seq_end
                                        == frozen_journal.seq_end as nat) by {
                                        assert(to_journal_records(journal_raw_disk)[root@]
                                            .message_seq.seq_end
                                            == self.journal.marshalled_seq_end());
                                        assert(frozen_journal.seq_end == marshalled);
                                    }
                                }
                                self.cache.handle_release(&root, slot_handle);
                                proof {
                                    assert(self.cache@ == pre_cache) by {
                                        assert(self.cache@.lookup_map == pre_cache.lookup_map);
                                        assert(self.cache@.status_map == pre_cache.status_map);
                                        assert(self.cache@.entries == pre_cache.entries);
                                    }
                                    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                                        implies self.cache@.valid_read(addr, reads[addr]) by {
                                        assert(addr == root@);
                                    }
                                    Cache::State::access_read_only_from_valid_reads(
                                        self.cache@,
                                        reads,
                                    );
                                    assert(self.state().cache == self.cache@);
                                    assert(Cache::State::next(
                                        self.state().cache,
                                        self.cache@,
                                        Cache::Label::Access{reads, writes: Map::empty()},
                                    ));
                                    reveal(CachedJournal::State::next);
                                    reveal(CachedJournal::State::next_by);
                                    assert(CachedJournal::State::freeze_for_commit(
                                        self.journal@,
                                        self.journal@,
                                        CachedJournal::Label::FreezeForCommit{
                                            frozen: frozen_journal.snapshot@,
                                            reads: to_journal_records(reads),
                                        },
                                    )) by {
                                    }
                                    assert(CachedJournal::State::next_by(
                                        self.journal@,
                                        self.journal@,
                                        CachedJournal::Label::FreezeForCommit{
                                            frozen: frozen_journal.snapshot@,
                                            reads: to_journal_records(reads),
                                        },
                                        CachedJournal::Step::freeze_for_commit(),
                                    ));
                                    assert(CachedJournal::State::next(
                                        self.journal@,
                                        self.journal@,
                                        CachedJournal::Label::FreezeForCommit{
                                            frozen: frozen_journal.snapshot@,
                                            reads: to_journal_records(reads),
                                        },
                                    ));
                                    assert(self.inv_api(api));
                                }
                                self.launch_frozen_sync(
                                    SyncFlavor::JournalOnly,
                                    frozen_journal,
                                    Ghost(reads),
                                    api,
                                )
                            },
                            FetchErrorCode::LoadInitiate{slot_handle} => {
                                proof {
                                    assert(self.state().outstanding_cache_reqs
                                        == Map::<ID, Address>::empty());
                                    assert(Cache::State::next(
                                        self.state().cache,
                                        self.cache@,
                                        cache_load_label(&root),
                                    ));
                                    assert(self.cache_read_io_lag_inv());
                                }
                                self.issue_acquired_cache_read_io(
                                    root,
                                    slot_handle,
                                    CacheReadPurpose::SyncJournalRoot,
                                    api,
                                )
                            },
                            FetchErrorCode::Awaiting
                            | FetchErrorCode::CacheFull
                            | FetchErrorCode::NotPresent => {
                                proof {
                                    assert(self.cache@ == pre_cache);
                                    assert(self.inv_api(api));
                                }
                                false
                            },
                        }
                    },
                }
            },
        }
    }

    fn continue_pending_user_op(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        if self.pending_branch_sync.is_some() {
            proof {
                assert(self.inv_api(api));
            }
            return false;
        }
        let outstanding_empty = self.outstanding_requests.is_empty();
        if !outstanding_empty {
            proof {
                assert(self.inv_api(api));
            }
            return false;
        }
        proof {
            assert(self.outstanding_requests@.is_empty());
            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                assert_maps_equal!(
                    self.outstanding_requests@,
                    Map::<ID, OutstandingReqInfo>::empty(),
                    id => {
                        if self.outstanding_requests@.contains_key(id) {
                            assert(!self.outstanding_requests@.is_empty());
                            assert(false);
                        }
                    }
                );
            }
            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                assert(self.outstanding_cache_reqs_match_model());
                assert(self.state().outstanding_cache_reqs.dom()
                    == self.outstanding_requests@.dom());
                assert_maps_equal!(
                    self.state().outstanding_cache_reqs,
                    Map::<ID, Address>::empty(),
                    id => {
                        if self.state().outstanding_cache_reqs.contains_key(id) {
                            assert(self.state().outstanding_cache_reqs.dom().contains(id));
                            assert(self.outstanding_requests@.dom().contains(id));
                            assert(false);
                        }
                    }
                );
            }
            assert(self.cache_read_io_lag_inv());
        }
        let ghost user_op_pre_state = self.model@.value();
        proof {
            let tracked empty_disk_responses_for_inv: Tracked<DiskRespShard> =
                Tracked(DiskRespShard::empty(self.instance_id()));
            let system_model = open_system_invariant_disk_response::<
                UnifiedCacheProgramModel,
                UnifiedCacheRefinementProof,
            >(self.model, empty_disk_responses_for_inv);
            assert(system_model.program == user_op_pre_state);
            assert(UnifiedCacheSystemRefinement::inv(system_model));
            assert(user_op_pre_state.state.client_ready());
            UnifiedCacheSystemRefinement::inv_implies_ready_seq_end_alignment(system_model);
            assert(user_op_pre_state.state.journal.journal.seq_end()
                == user_op_pre_state.state.branch.seq_end());
        }

        let mut pending = None;
        core::mem::swap(&mut self.pending_user_op, &mut pending);
        match pending {
            None => false,
            Some(PendingUserOp::Put{req, req_shard, key, value}) => {
                if !self.branch.mini_allocator.is_allocation_ready() {
                    self.pending_user_op = Some(PendingUserOp::Put{req, req_shard, key, value});
                    proof {
                        assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                    }
                    self.record_branch_refill_for_ready(api)
                } else {
                    let mut keys = Vec::new();
                    keys.push(key);
                    let msg = Message::Define{value};
                    let mut msgs = Vec::new();
                    msgs.push(msg);

                    let ghost pre_append_branch = self.branch@;
                    let ghost pre_append_cache = self.cache@;
                    let append_result = self.branch.append_with_cache(
                        &mut self.cache,
                        &keys,
                        &msgs,
                        self.disk_au_count,
                        self.disk_page_count,
                    );
                    proof {
                        assert(self.branch.image.roots_wf());
                    }
                    match append_result {
                        BranchReplayAppendResult::Appended{
                            prepared_cache,
                            branch_reads,
                            writes,
                            receipt,
                            init_root,
                        } => {
                            let ghost pre_insert_journal = self.journal@;
                            self.journal.insert(key, value);
                            let reply = Reply{output: Output::PutOutput, id: req.id};
                            let ghost new_atomic_journal = AtomicJournalState::State{
                                journal: self.journal@,
                                mini_allocator: self.journal.journal_alloc.i(),
                                ..user_op_pre_state.state.journal
                            };
                            let ghost prepared_state = UnifiedCacheProgramModel{
                                state: UnifiedCacheSystem::State{
                                    cache: prepared_cache@,
                                    ..user_op_pre_state.state
                                }
                            };
                            let ghost post_state = UnifiedCacheProgramModel{
                                state: UnifiedCacheSystem::State{
                                    cache: self.cache@,
                                    journal: new_atomic_journal,
                                    branch: self.branch@,
                                    free_aus: self.au_pool@,
                                    ..user_op_pre_state.state
                                }
                            };
                            let tracked mut model = KVStoreTokenized::model::arbitrary();
                            proof {
                                let map_req = req.mapspec_req();
                                let map_reply = reply.mapspec_reply();
                                let records = crate::abstract_system::MsgHistory_v::MsgHistory::singleton_at(
                                    user_op_pre_state.state.branch.seq_end(),
                                    crate::abstract_system::MsgHistory_v::KeyedMessage::from_kv(key, value),
                                );
                                let journal_lbl = AtomicJournalState::Label::Put{messages: records};
                                let cached_journal_lbl = CachedJournal::Label::Put{messages: records};
                                let branch_lbl = AtomicBranchState::Label::Append{
                                    keys: keys@,
                                    msgs: msgs@,
                                    receipt: receipt@,
                                    init_root: init_root@,
                                    read_nodes: to_branch_nodes(branch_reads@),
                                    write_nodes: to_branch_nodes(writes@),
                                };

                                assert(self.model@.value() == user_op_pre_state);
                                assert(map_req.input is PutInput);
                                assert(map_reply.output is PutOutput);
                                assert(valid_request_reply_pair(map_req, map_reply));
                                assert(keys@ == crate::implementation::UnifiedCacheSystem_v::singleton_key_seq(key));
                                assert(msgs@ == crate::implementation::UnifiedCacheSystem_v::singleton_message_seq(msg));
                                assert(user_op_pre_state.state.cache == pre_append_cache);
                                assert(user_op_pre_state.state.branch == pre_append_branch);
                                assert(Cache::State::next(
                                    user_op_pre_state.state.cache,
                                    prepared_state.state.cache,
                                    Cache::Label::Internal,
                                ));
                                assert(UnifiedCacheSystem::State::cache_internal(
                                    user_op_pre_state.state,
                                    prepared_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                    prepared_cache@,
                                )) by {
                                }
                                assert(UnifiedCacheSystem::State::next_by(
                                    user_op_pre_state.state,
                                    prepared_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                    UnifiedCacheSystem::Step::cache_internal(prepared_cache@),
                                )) by {
                                    reveal(UnifiedCacheSystem::State::next_by);
                                }
                                UnifiedCacheProgramModel::lift_internal_step(user_op_pre_state, prepared_state);

                                assert(user_op_pre_state.state.journal.journal == pre_insert_journal);
                                assert(CachedJournal::State::put(
                                    pre_insert_journal,
                                    self.journal@,
                                    CachedJournal::Label::Put{
                                        messages: crate::abstract_system::MsgHistory_v::MsgHistory::singleton_at(
                                            pre_insert_journal.seq_end(),
                                            crate::abstract_system::MsgHistory_v::KeyedMessage::from_kv(key, value),
                                        ),
                                    },
                                ));
                                assert(records == crate::abstract_system::MsgHistory_v::MsgHistory::singleton_at(
                                    pre_insert_journal.seq_end(),
                                    crate::abstract_system::MsgHistory_v::KeyedMessage::from_kv(key, value),
                                ));
                                assert(CachedJournal::State::put(
                                    user_op_pre_state.state.journal.journal,
                                    self.journal@,
                                    cached_journal_lbl,
                                ));
                                assert(CachedJournal::State::next_by(
                                    user_op_pre_state.state.journal.journal,
                                    self.journal@,
                                    cached_journal_lbl,
                                    CachedJournal::Step::put(),
                                )) by {
                                    reveal(CachedJournal::State::next_by);
                                }
                                assert(CachedJournal::State::next(
                                    user_op_pre_state.state.journal.journal,
                                    self.journal@,
                                    cached_journal_lbl,
                                )) by {
                                    reveal(CachedJournal::State::next);
                                }
                                assert(AtomicJournalState::State::put(
                                    prepared_state.state.journal,
                                    new_atomic_journal,
                                    journal_lbl,
                                    self.journal@,
                                )) by {
                                }
                                assert(AtomicJournalState::State::next_by(
                                    prepared_state.state.journal,
                                    new_atomic_journal,
                                    journal_lbl,
                                    AtomicJournalState::Step::put(self.journal@),
                                )) by {
                                    reveal(AtomicJournalState::State::next_by);
                                }
                                assert(AtomicJournalState::State::next(
                                    prepared_state.state.journal,
                                    new_atomic_journal,
                                    journal_lbl,
                                )) by {
                                    reveal(AtomicJournalState::State::next);
                                }
                                assert(Cache::State::next(
                                    prepared_state.state.cache,
                                    self.cache@,
                                    Cache::Label::Access{reads: branch_reads@, writes: writes@},
                                ));
                                assert(AtomicBranchState::State::next(
                                    prepared_state.state.branch,
                                    self.branch@,
                                    branch_lbl,
                                ));
                                assert(UnifiedCacheSystem::State::execute_put(
                                    prepared_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
                                    self.cache@,
                                    new_atomic_journal,
                                    receipt@,
                                    init_root@,
                                    branch_reads@,
                                    writes@,
                                    self.branch@,
                                )) by {
                                }
                                assert(UnifiedCacheSystem::State::next_by(
                                    prepared_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
                                    UnifiedCacheSystem::Step::execute_put(
                                        self.cache@,
                                        new_atomic_journal,
                                        receipt@,
                                        init_root@,
                                        branch_reads@,
                                        writes@,
                                        self.branch@,
                                    ),
                                )) by {
                                    reveal(UnifiedCacheSystem::State::next_by);
                                }
                                assert(UnifiedCacheSystem::State::next(
                                    prepared_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
                                )) by {
                                    reveal(UnifiedCacheSystem::State::next);
                                }
                                assert(ProgramModelTrait::next(
                                    prepared_state,
                                    post_state,
                                    ProgramLabel::UserIO{
                                        op: ProgramUserOp::Execute{req: map_req, reply: map_reply},
                                    },
                                ));
                                AtomicBranchState::State::append_effect(
                                    user_op_pre_state.state.branch,
                                    self.branch@,
                                    branch_lbl,
                                );
                                assert(post_state.state.branch.seq_end()
                                    == user_op_pre_state.state.branch.seq_end() + keys@.len());
                                assert(keys@.len() > 0);
                                tracked_swap(self.model.borrow_mut(), &mut model);
                            }
                            let tracked _cache_internal_token = self.instance.borrow().internal(
                                KVStoreTokenized::Label::InternalOp{},
                                prepared_state,
                                &mut model,
                            );
                            let tracked new_reply_token = self.instance.borrow().execute_transition(
                                KVStoreTokenized::Label::ExecuteOp{req, reply},
                                post_state,
                                &mut model,
                                req_shard.get(),
                            );
                            self.model = Tracked(model);
                            proof {
                                assert(self.state().branch.seq_end()
                                    >= old(self).state().branch.seq_end());
                                Self::sync_wf_preserved_without_sync_change(old(self), self);
                            }
                            api.send_reply(reply, Tracked(new_reply_token), true);
                            true
                        },
                        BranchReplayAppendResult::NeedCacheLoad{addr, handle} => {
                            self.pending_user_op = Some(PendingUserOp::Put{req, req_shard, key, value});
                            proof {
                                assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                                assert(self.state().outstanding_cache_reqs
                                    == Map::<ID, Address>::empty());
                                assert(self.cache_read_io_lag_inv());
                            }
                            self.issue_acquired_cache_read_io(
                                addr,
                                handle,
                                CacheReadPurpose::Generic,
                                api,
                            )
                        },
                        BranchReplayAppendResult::NeedsAUs => {
                            self.pending_user_op = Some(PendingUserOp::Put{req, req_shard, key, value});
                            proof {
                                assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            }
                            self.record_branch_refill_for_ready(api)
                        },
                        BranchReplayAppendResult::CacheFull => {
                            self.pending_user_op = Some(PendingUserOp::Put{req, req_shard, key, value});
                            api.log("unified-cache pending put waits for cache space");
                            false
                        },
                        BranchReplayAppendResult::Blocked => {
                            self.pending_user_op = Some(PendingUserOp::Put{req, req_shard, key, value});
                            api.log("unified-cache pending put waits");
                            false
                        },
                    }
                }
            },
            Some(PendingUserOp::Query{req, req_shard, key}) => {
                let ghost pre_query_branch = self.branch@;
                let ghost pre_query_cache = self.cache@;
                let query_result = self.branch.query_with_cache(&mut self.cache, key);
                proof {
                    assert(self.branch.image.roots_wf());
                }
                match query_result {
                    BranchQueryResult::Hit{value, msg, reads, receipts} => {
                        let reply = Reply{output: Output::QueryOutput{value}, id: req.id};
                        let ghost post_state = UnifiedCacheProgramModel{
                            state: UnifiedCacheSystem::State{
                                cache: self.cache@,
                                ..user_op_pre_state.state
                            }
                        };
                        let tracked mut model = KVStoreTokenized::model::arbitrary();
                        proof {
                            let map_req = req.mapspec_req();
                            let map_reply = reply.mapspec_reply();
                            assert(self.model@.value() == user_op_pre_state);
                            assert(map_req.input is QueryInput);
                            assert(map_reply.output is QueryOutput);
                            assert(valid_request_reply_pair(map_req, map_reply));
                            assert(user_op_pre_state.state.cache == pre_query_cache);
                            assert(user_op_pre_state.state.branch == pre_query_branch);
                            assert(Cache::State::next(
                                user_op_pre_state.state.cache,
                                self.cache@,
                                Cache::Label::Access{reads: reads@, writes: Map::empty()},
                            ));
                            assert(AtomicBranchState::State::next(
                                user_op_pre_state.state.branch,
                                user_op_pre_state.state.branch,
                                AtomicBranchState::Label::Query{
                                    key,
                                    msg: msg@,
                                    receipts: receipts@,
                                    read_nodes: to_branch_nodes(reads@),
                                },
                            ));
                            assert(UnifiedCacheSystem::State::execute_query(
                                user_op_pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
                                self.cache@,
                                msg@,
                                receipts@,
                                reads@,
                            )) by {
                            }
                            assert(UnifiedCacheSystem::State::next_by(
                                user_op_pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
                                UnifiedCacheSystem::Step::execute_query(
                                    self.cache@,
                                    msg@,
                                    receipts@,
                                    reads@,
                                ),
                            )) by {
                                reveal(UnifiedCacheSystem::State::next_by);
                            }
                            assert(UnifiedCacheSystem::State::next(
                                user_op_pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Execute{req: map_req, reply: map_reply},
                            )) by {
                                reveal(UnifiedCacheSystem::State::next);
                            }
                            assert(ProgramModelTrait::next(
                                user_op_pre_state,
                                post_state,
                                ProgramLabel::UserIO{
                                    op: ProgramUserOp::Execute{req: map_req, reply: map_reply},
                                },
                            ));
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }
                        let tracked new_reply_token = self.instance.borrow().execute_transition(
                            KVStoreTokenized::Label::ExecuteOp{req, reply},
                            post_state,
                            &mut model,
                            req_shard.get(),
                        );
                        self.model = Tracked(model);
                        api.send_reply(reply, Tracked(new_reply_token), true);
                        true
                    },
                    BranchQueryResult::NeedCacheLoad{addr, handle} => {
                        self.pending_user_op = Some(PendingUserOp::Query{req, req_shard, key});
                        proof {
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.state().outstanding_cache_reqs
                                == Map::<ID, Address>::empty());
                            assert(self.cache_read_io_lag_inv());
                        }
                        self.issue_acquired_cache_read_io(
                            addr,
                            handle,
                            CacheReadPurpose::Generic,
                            api,
                        )
                    },
                    BranchQueryResult::Blocked => {
                        self.pending_user_op = Some(PendingUserOp::Query{req, req_shard, key});
                        api.log("unified-cache pending query waits");
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
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            req.input == (Input::PutInput{key, value}),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        self.pending_user_op = Some(PendingUserOp::Put{req, req_shard, key, value});
        let _progress = self.continue_pending_user_op(api);
    }

    fn record_execute_query(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        key: Key,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            req.input == (Input::QueryInput{key}),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        self.pending_user_op = Some(PendingUserOp::Query{req, req_shard, key});
        let _progress = self.continue_pending_user_op(api);
    }

    fn record_journal_marshall_step(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).state().recovery_state is RecoveryComplete,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let ghost pre_state = self.model@.value();
        proof {
            let tracked empty_disk_responses_for_inv: Tracked<DiskRespShard> =
                Tracked(DiskRespShard::empty(self.instance_id()));
            let system_model = open_system_invariant_disk_response::<
                UnifiedCacheProgramModel,
                UnifiedCacheRefinementProof,
            >(self.model, empty_disk_responses_for_inv);
            assert(system_model.program == pre_state);
            assert(UnifiedCacheSystemRefinement::inv(system_model));
            UnifiedCacheSystemRefinement::inv_implies_cache_inv(system_model);
            assert(pre_state.state.cache == self.cache@);
            assert(pre_state.state.cache.inv());
            assert(self.cache@.inv());
        }
        let seq_end = self.journal.exec_seq_end();
        let marshalled = self.journal.exec_marshaled_seq_end();
        if seq_end == marshalled {
            proof {
                assert(self.inv_api(api));
            }
            return false;
        }

        match self.journal.internal_journal_marshall_reserve_slot(
            &mut self.cache,
            self.disk_au_count,
            self.disk_page_count,
        ) {
            MarshalReserveResult::CacheFull{} => {
                proof {
                    self.journal.wf_implies_basic_wf();
                    assert(self.journal.basic_wf());
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i()) by {
                        assert(pre_state.state.journal.mini_allocator
                            == old(self).journal.journal_alloc.i());
                    }
                    Self::live_component_alignment_preserved(old(self), self);
                    assert(self.inv_api(api));
                }
                api.log("unified-cache journal marshalling cache full");
                false
            },
            MarshalReserveResult::Reserved{addr, slot_handle} => {
                let ghost reserved_cache = self.cache@;
                let ghost reserve_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: reserved_cache,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        reserve_state.state.cache,
                        Cache::Label::Internal,
                    ));
                    assert(UnifiedCacheSystem::State::cache_internal(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        reserve_state.state.cache,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        reserve_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::cache_internal(reserve_state.state.cache),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, reserve_state);
                }
                let tracked _reserve_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    reserve_state,
                    &mut model,
                );
                proof {
                    Cache::State::inv_next(
                        pre_state.state.cache,
                        reserve_state.state.cache,
                        Cache::Label::Internal,
                    );
                    assert(self.cache@.inv());
                    assert(self.journal.index_ready());
                    assert(self.journal@ == old(self).journal@);
                    self.journal.view_seq_end_ensures();
                    self.journal.view_marshaled_seq_end_ensures();
                    old(self).journal.view_seq_end_ensures();
                    old(self).journal.view_marshaled_seq_end_ensures();
                    assert(self.journal@.seq_end() == old(self).journal@.seq_end());
                    assert(self.journal@.marshalled_seq_end()
                        == old(self).journal@.marshalled_seq_end());
                    assert(self.journal.seq_end() == old(self).journal.seq_end());
                    assert(self.journal.marshalled_seq_end()
                        == old(self).journal.marshalled_seq_end());
                    assert(old(self).journal.seq_end() != old(self).journal.marshalled_seq_end()) by {
                        assert(seq_end == old(self).journal.seq_end());
                        assert(marshalled == old(self).journal.marshalled_seq_end());
                    }
                    assert(self.journal.seq_end() != self.journal.marshalled_seq_end());
                }
                let raw_page = self.journal.internal_journal_marshall_commit_reserved(
                    &mut self.cache,
                    addr,
                    slot_handle,
                );
                let ghost writes = Map::<Address, RawPage>::empty().insert(addr@, raw_page@);
                let ghost new_atomic_journal = AtomicJournalState::State{
                    journal: self.journal@,
                    mini_allocator: self.journal.journal_alloc.i(),
                    ..reserve_state.state.journal
                };
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        journal: new_atomic_journal,
                        ..reserve_state.state
                    }
                };
                proof {
                    let journal_lbl = AtomicJournalState::Label::JournalMarshal{
                        addr: addr@,
                        writes: to_journal_records(writes),
                    };
                    assert(pre_state.state.journal.journal == old(self).journal@);
                    assert(reserve_state.state.journal == pre_state.state.journal);
                    assert(reserve_state.state.journal.mini_allocator
                        == old(self).journal.journal_alloc.i());
                    assert(old(self).journal.journal_alloc.i().tight_next_addr(
                        old(self).journal@.snapshot.freshest_rec(),
                        addr@,
                    ));
                    assert(reserve_state.state.journal.mini_allocator.tight_next_addr(
                        reserve_state.state.journal.journal.snapshot.freshest_rec(),
                        addr@,
                    )) by {
                        assert(reserve_state.state.journal.journal == old(self).journal@);
                    }
                    assert(new_atomic_journal.mini_allocator
                        == reserve_state.state.journal.mini_allocator.allocate(addr@)) by {
                        assert(self.journal.journal_alloc.i()
                            == old(self).journal.journal_alloc.i().allocate(addr@));
                    }
                    assert(CachedJournal::State::next(
                        reserve_state.state.journal.journal,
                        new_atomic_journal.journal,
                        CachedJournal::Label::JournalMarshal{
                            writes: to_journal_records(writes),
                        },
                    )) by {
                        assert(journal_marshall_labels(addr@, raw_page@).0
                            == CachedJournal::Label::JournalMarshal{
                                writes: to_journal_records(writes),
                            });
                    }
                    assert(AtomicJournalState::State::journal_marshal(
                        reserve_state.state.journal,
                        new_atomic_journal,
                        journal_lbl,
                        new_atomic_journal.journal,
                    )) by {
                    }
                    assert(AtomicJournalState::State::next_by(
                        reserve_state.state.journal,
                        new_atomic_journal,
                        journal_lbl,
                        AtomicJournalState::Step::journal_marshal(new_atomic_journal.journal),
                    )) by {
                        reveal(AtomicJournalState::State::next_by);
                    }
                    assert(AtomicJournalState::State::next(
                        reserve_state.state.journal,
                        new_atomic_journal,
                        journal_lbl,
                    )) by {
                        reveal(AtomicJournalState::State::next);
                    }
                    assert(Cache::State::next(
                        reserve_state.state.cache,
                        post_state.state.cache,
                        Cache::Label::Access{reads: Map::empty(), writes},
                    )) by {
                        assert(journal_marshall_labels(addr@, raw_page@).1
                            == Cache::Label::Access{reads: Map::empty(), writes});
                    }
                    assert(UnifiedCacheSystem::State::journal_marshall(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        addr@,
                        raw_page@,
                        post_state.state.cache,
                        new_atomic_journal,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        reserve_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::journal_marshall(
                            addr@,
                            raw_page@,
                            post_state.state.cache,
                            new_atomic_journal,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(reserve_state, post_state);
                }
                let tracked _marshall_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    self.journal.wf_implies_basic_wf();
                    assert(self.journal.basic_wf());
                    self.journal.view_ensures();
                    assert(self.journal@.status is Some);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i());
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal_metadata_loaded());
                    assert(self.state().cache == self.cache@);
                    assert(self.journal.journal_alloc.bounded(self.disk_au_count));
                    assert(MiniAllocatorImpl::allocators_unique(
                        self.journal.journal_alloc.allocators@,
                    ));
                    assert(self.au_pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(
                            self.journal.journal_alloc.allocators@,
                        ),
                    )) by {
                        assert(MiniAllocatorImpl::allocators_au_set(
                            self.journal.journal_alloc.allocators@,
                        ) =~= MiniAllocatorImpl::allocators_au_set(
                            old(self).journal.journal_alloc.allocators@,
                        ));
                        assert(old(self).au_pool@.disjoint(
                            MiniAllocatorImpl::allocators_au_set(
                                old(self).journal.journal_alloc.allocators@,
                            ),
                        ));
                        assert(self.au_pool@ == old(self).au_pool@);
                    }
                    old(self).journal.journal_alloc.i().allocate_allocated_aus(addr@);
                    assert(self.journal.allocator_index_aligned()) by {
                        reveal(Implementation::inv_api);
                        reveal(Implementation::inv);
                        assert(old(self).journal.allocator_index_aligned());
                        assert(self.journal.journal_alloc.i().allocated_aus()
                            =~= old(self).journal.journal_alloc.i().allocated_aus()
                                .insert(addr@.au));
                        assert(self.journal@.status.unwrap().lsn_au_index.values()
                            =~= old(self).journal@.status.unwrap().lsn_au_index.values()
                                .insert(addr@.au));
                    }
                    assert(self.inv_api(api));
                }
                api.log("unified-cache journal marshalling");
                true
            },
        }
    }

    fn record_journal_writeback_for_target(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            old(self).state().recovery_state is RecoveryComplete,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
            !progress ==> self.outstanding_requests@ == old(self).outstanding_requests@,
    {
        let old_clean = self.journal.exec_clean_watermark();
        let target = self.journal.exec_marshaled_seq_end();
        match self.journal.begin_writeback_for_target(&mut self.cache, target) {
            BeginWritebackForTargetResult::Complete{flushed_domain} => {
                let new_clean = self.journal.exec_clean_watermark();
                if new_clean == old_clean {
                    proof {
                        self.journal.view_ensures();
                        assert(self.journal.index_ready());
                        assert(self.journal@.status is Some);
                        assert(self.state().journal.journal == self.journal@);
                        assert(self.state().journal.ready());
                        assert(self.state().journal_metadata_loaded());
                        assert(self.outstanding_requests@ == old(self).outstanding_requests@);
                        assert(self.inv_api(api));
                    }
                    return false;
                }
                let ghost pre_state = self.model@.value();
                let ghost new_atomic_journal = AtomicJournalState::State{
                    journal: self.journal@,
                    ..pre_state.state.journal
                };
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        journal: new_atomic_journal,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    assert(old_clean < new_clean) by {
                        assert(old_clean <= new_clean);
                        assert(new_clean != old_clean);
                    }
                    let aus = to_aus(flushed_domain@);
                    assert(Cache::State::next(
                        pre_state.state.cache,
                        pre_state.state.cache,
                        Cache::Label::EvictableCheck{aus},
                    )) by {
                        assert(pre_state.state.cache == old(self).cache@);
                    }
                    assert(CachedJournal::State::next(
                        pre_state.state.journal.journal,
                        self.journal@,
                        CachedJournal::Label::ObserveCleanAUs{aus},
                    )) by {
                        assert(pre_state.state.journal.journal == old(self).journal@);
                    }
                    assert(AtomicJournalState::State::observe_clean_aus(
                        pre_state.state.journal,
                        new_atomic_journal,
                        AtomicJournalState::Label::ObserveCleanAUs{aus},
                        self.journal@,
                    )) by {
                    }
                    assert(AtomicJournalState::State::next_by(
                        pre_state.state.journal,
                        new_atomic_journal,
                        AtomicJournalState::Label::ObserveCleanAUs{aus},
                        AtomicJournalState::Step::observe_clean_aus(self.journal@),
                    )) by {
                        reveal(AtomicJournalState::State::next_by);
                    }
                    assert(AtomicJournalState::State::next(
                        pre_state.state.journal,
                        new_atomic_journal,
                        AtomicJournalState::Label::ObserveCleanAUs{aus},
                    )) by {
                        reveal(AtomicJournalState::State::next);
                    }
                    assert(pre_state.state.client_ready());
                    assert(UnifiedCacheSystem::State::observe_clean_journal_aus(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        aus,
                        pre_state.state.cache,
                        new_atomic_journal,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::observe_clean_journal_aus(
                            aus,
                            pre_state.state.cache,
                            new_atomic_journal,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                }
                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                proof {
                    self.journal.view_ensures();
                    assert(self.journal.index_ready());
                    assert(self.journal@.status is Some);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.ready());
                    assert(self.state().journal_metadata_loaded());
                    JournalImpl::allocator_index_alignment_preserved(
                        &old(self).journal,
                        &self.journal,
                    );
                    assert(self.inv_api(api));
                }
                api.log("unified-cache journal clean watermark advanced");
                true
            },
            BeginWritebackForTargetResult::Acquired{request, flushed_domain} => {
                let new_clean = self.journal.exec_clean_watermark();
                let clean_changed = new_clean != old_clean;
                let write_data = request.handle.rec.clone();
                let addr = request.addr;
                let ghost pre_state = self.model@.value();
                let ghost clean_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        journal: AtomicJournalState::State{
                            journal: self.journal@,
                            ..pre_state.state.journal
                        },
                        ..pre_state.state
                    }
                };

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    assert(old(self).journal@.status.unwrap().lsn_au_index.values().contains(addr@.au));
                    assert(pre_state.state.journal.journal == old(self).journal@);
                    assert(pre_state.state.journal.journal.status.unwrap().lsn_au_index.values().contains(addr@.au));
                    let tracked empty_disk_responses_for_inv: Tracked<DiskRespShard> =
                        Tracked(DiskRespShard::empty(self.instance_id()));
                    let system_model = open_system_invariant_disk_response::<
                        UnifiedCacheProgramModel,
                        UnifiedCacheRefinementProof,
                    >(self.model, empty_disk_responses_for_inv);
                    assert(system_model.program == pre_state);
                    assert(UnifiedCacheSystemRefinement::inv(system_model));
                    assert(system_model.program.state.allocation_metadata_loaded());
                    UnifiedCacheSystemRefinement::journal_projection_aus_subset_system_journal_owned(system_model);
                    let journal_src =
                        UnifiedCacheJournalRefinement::unified_cache_journal_source(system_model);
                    let system =
                        UnifiedCacheSystemRefinement::unified_cache_system_i(system_model);
                    assert(journal_src.journal_projection_aus() == journal_src.journal.owned_aus());
                    assert(journal_src.journal.owned_aus()
                        == journal_src.journal.loaded_index_aus()
                            + journal_src.journal.mini_allocator.all_aus());
                    assert(journal_src.journal.loaded_index_aus()
                        == pre_state.state.journal.journal.status.unwrap().lsn_au_index.values());
                    assert(journal_src.journal_projection_aus().contains(addr@.au));
                    assert(system.journal_owned_aus().contains(addr@.au));
                    assert(system.component_disjoint());
                    assert(!system.journal_owned_aus().contains(spec_superblock_addr().au)) by {
                        if system.journal_owned_aus().contains(spec_superblock_addr().au) {
                            assert(crate::implementation::CrashAwareCachingDiskSystem_v::CrashAwareCachingDiskSystem::State::reserved_aus()
                                .contains(spec_superblock_addr().au));
                            assert(false);
                        }
                    }
                    assert(addr@.au != spec_superblock_addr().au);
                    assert(addr@ != spec_superblock_addr());
                    tracked_swap(self.model.borrow_mut(), &mut model);
                    if clean_changed {
                        assert(old_clean < new_clean) by {
                            assert(old_clean <= new_clean);
                            assert(new_clean != old_clean);
                        }
                        let aus = to_aus(flushed_domain@);
                        assert(Cache::State::next(
                            pre_state.state.cache,
                            pre_state.state.cache,
                            Cache::Label::EvictableCheck{aus},
                        )) by {
                            assert(pre_state.state.cache == old(self).cache@);
                        }
                        assert(CachedJournal::State::next(
                            pre_state.state.journal.journal,
                            self.journal@,
                            CachedJournal::Label::ObserveCleanAUs{aus},
                        )) by {
                            assert(pre_state.state.journal.journal == old(self).journal@);
                        }
                        let journal_lbl = AtomicJournalState::Label::ObserveCleanAUs{aus};
                        assert(AtomicJournalState::State::observe_clean_aus(
                            pre_state.state.journal,
                            clean_state.state.journal,
                            journal_lbl,
                            self.journal@,
                        )) by {
                        }
                        assert(AtomicJournalState::State::next_by(
                            pre_state.state.journal,
                            clean_state.state.journal,
                            journal_lbl,
                            AtomicJournalState::Step::observe_clean_aus(self.journal@),
                        )) by {
                            reveal(AtomicJournalState::State::next_by);
                        }
                        assert(AtomicJournalState::State::next(
                            pre_state.state.journal,
                            clean_state.state.journal,
                            journal_lbl,
                        )) by {
                            reveal(AtomicJournalState::State::next);
                        }
                        assert(pre_state.state.client_ready());
                        assert(UnifiedCacheSystem::State::observe_clean_journal_aus(
                            pre_state.state,
                            clean_state.state,
                            UnifiedCacheSystem::Label::Internal,
                            aus,
                            pre_state.state.cache,
                            clean_state.state.journal,
                        )) by {
                        }
                        assert(UnifiedCacheSystem::State::next_by(
                            pre_state.state,
                            clean_state.state,
                            UnifiedCacheSystem::Label::Internal,
                            UnifiedCacheSystem::Step::observe_clean_journal_aus(
                                aus,
                                pre_state.state.cache,
                                clean_state.state.journal,
                            ),
                        )) by {
                            reveal(UnifiedCacheSystem::State::next_by);
                        }
                        UnifiedCacheProgramModel::lift_internal_step(pre_state, clean_state);
                    }
                }
                if clean_changed {
                    let tracked _internal_token = self.instance.borrow().internal(
                        KVStoreTokenized::Label::InternalOp{},
                        clean_state,
                        &mut model,
                    );
                }

                let req_id_perm = Tracked(api.send_disk_request_predict_id());
                let disk_req = IDiskRequest::WriteReq{to: addr, data: write_data};
                let ghost updated = map![req_id_perm@ => addr@];
                let ghost req_map = map![req_id_perm@ => disk_req@];
                let ghost disk_request_tuples =
                    multiset_map_singleton(req_id_perm@, disk_req@);
                let ghost disk_response_tuples = Multiset::empty();
                let ghost model_before_disk = if clean_changed { clean_state } else { pre_state };
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        outstanding_cache_reqs:
                            model_before_disk.state.outstanding_cache_reqs.union_prefer_right(updated),
                        ..model_before_disk.state
                    }
                };
                proof {
                    assert(self.cache.valid_writeback_handle(&addr, request.handle));
                    assert(old(self).journal@.status.unwrap().lsn_au_index.values().contains(addr@.au));
                    assert(pre_state.state.journal.journal == old(self).journal@);
                    assert(pre_state.state.journal.journal.status.unwrap().lsn_au_index.values().contains(addr@.au));
                    assert(addr@.au != spec_superblock_addr().au);
                    assert(addr@ != spec_superblock_addr());
                    FracCacheImpl::valid_writeback_handle_has_inv(&self.cache, &addr, request.handle);
                    assert(request.handle.inv());
                    assert(request.handle.rec.len() == PAGE_SIZE_BYTES);
                    assert(write_data@ == request.handle.rec@);
                    assert(write_data.len() == PAGE_SIZE_BYTES);

                    multiset_map_singleton_ensures(req_id_perm@, disk_req@);
                    assert(multiset_to_map(disk_request_tuples) == req_map);
                    Self::singleton_updated_addr_map(req_id_perm@, disk_req@, addr@);
                    assert(updated.is_injective());
                    assert(!updated.contains_value(spec_superblock_addr()));
                    Self::singleton_req_map_values(req_id_perm@, disk_req@);
                    assert(Cache::State::next(
                        model_before_disk.state.cache,
                        self.cache@,
                        Cache::Label::DiskOps{
                            requests: req_map.values(),
                            responses: Map::empty(),
                        },
                    )) by {
                        if clean_changed {
                            assert(model_before_disk.state.cache == pre_state.state.cache);
                        } else {
                            assert(model_before_disk.state.cache == pre_state.state.cache);
                        }
                    }
                    assert(UnifiedCacheSystem::State::cache_io_begin(
                        model_before_disk.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        req_map,
                        self.cache@,
                        disk_request_tuples,
                        disk_response_tuples,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        model_before_disk.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    let info = ProgramDiskInfo{
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheProgramModel::disk_step_matches_info(
                        model_before_disk.state,
                        UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                        info,
                    ));
                    UnifiedCacheProgramModel::lift_disk_step(model_before_disk, post_state, info);
                }
                let tracked empty_disk_responses = DiskRespShard::empty(self.instance_id());
                let tracked new_disk_req_token = self.instance.borrow().disk_transitions(
                    KVStoreTokenized::Label::DiskOp{
                        disk_request_tuples,
                        disk_response_tuples,
                    },
                    post_state,
                    &mut model,
                    empty_disk_responses,
                );
                self.model = Tracked(model);

                let id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));
                self.outstanding_requests.insert(id, OutstandingReqInfo::CacheWrite{
                    addr,
                    write_handle: request.handle,
                });
                proof {
                    assert(id == req_id_perm@);
                    FracCacheImpl::valid_writeback_handle_has_inv(&self.cache, &addr, request.handle);
                    assert(self.cache.entry_fetched(&addr));
                    assert(self.outstanding_requests_wf()) by {
                        assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                            implies {
                                match self.outstanding_requests@[id2] {
                                    OutstandingReqInfo::CacheRead{addr, load_handle, ..} => {
                                        &&& self.cache.entry_fetched(&addr)
                                        &&& self.cache.valid_load_handle(&addr, load_handle)
                                    },
                                    OutstandingReqInfo::CacheWrite{addr, write_handle} => {
                                        &&& self.cache.entry_fetched(&addr)
                                        &&& self.cache.valid_writeback_handle(&addr, write_handle)
                                    },
                                    OutstandingReqInfo::SuperblockWrite => true,
                                }
                            } by {
                            if id2 == id {
                                assert(self.outstanding_requests@[id2]
                                    == OutstandingReqInfo::CacheWrite{
                                        addr,
                                        write_handle: request.handle,
                                    });
                            } else {
                                assert(old(self).outstanding_requests@
                                    == Map::<ID, OutstandingReqInfo>::empty());
                                assert(false);
                            }
                        }
                    }
                    assert(self.outstanding_requests@.dom() =~= set![id]);
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                        assert(old(self).outstanding_cache_reqs_match_model());
                        assert(pre_state.state.outstanding_cache_reqs.dom()
                            == old(self).outstanding_requests@.dom());
                        assert(old(self).outstanding_requests@
                            == Map::<ID, OutstandingReqInfo>::empty());
                        assert_maps_equal!(
                            pre_state.state.outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            k => {
                                if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                                    assert(pre_state.state.outstanding_cache_reqs.dom().contains(k));
                                    assert(old(self).outstanding_requests@.dom().contains(k));
                                    assert(false);
                                }
                            }
                        );
                    }
                    assert(model_before_disk.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                        if clean_changed {
                            assert(model_before_disk == clean_state);
                        } else {
                            assert(model_before_disk == pre_state);
                        }
                    }
                    assert(self.state().outstanding_cache_reqs == map![id => addr@]) by {
                        assert(post_state.state.outstanding_cache_reqs
                            == model_before_disk.state.outstanding_cache_reqs.union_prefer_right(updated));
                        assert(model_before_disk.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                        assert(updated == map![req_id_perm@ => addr@]);
                        assert(id == req_id_perm@);
                        assert_maps_equal!(self.state().outstanding_cache_reqs, map![id => addr@], k => {
                            if k == id {
                                assert(updated.contains_key(k));
                            } else {
                                assert(!updated.contains_key(k));
                            }
                        });
                    }
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                    self.journal.view_ensures();
                    assert(self.journal.index_ready());
                    assert(self.journal@.status is Some);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.ready());
                    assert(self.state().journal_metadata_loaded());
                    JournalImpl::allocator_index_alignment_preserved(
                        &old(self).journal,
                        &self.journal,
                    );
                    assert(self.inv_api(api));
                }
                api.log("unified-cache journal cache writeback");
                true
            },
        }
    }

    fn record_journal_replay_append(
        &mut self,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReplayingJournal,
            old(self).state().recovery_state is MetadataLoadComplete,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let ghost pre_state = self.model@.value();
        let start_lsn = self.branch.exec_seq_end();
        let journal_start_lsn = self.journal.exec_seq_start();
        let journal_end_lsn = self.journal.exec_seq_end();
        if start_lsn < journal_start_lsn {
            api.log_u64("start_lsn = ", start_lsn);
            api.log_u64("journal_start_lsn = ", journal_start_lsn);
            api.log("unified-cache journal replay cursor before journal start");

            proof {
                assert(self.inv_api(api));
            }
            return false;
        }
        if journal_end_lsn <= start_lsn {
            api.log("unified-cache journal replay cursor at journal end");
            proof {
                assert(self.inv_api(api));
            }
            return false;
        }
        let tail_empty = match self.journal.status.as_ref() {
            Some(status) => status.unmarshalled_tail.len() == 0,
            None => false,
        };
        if !tail_empty {
            api.log("unified-cache journal replay waits for marshalled journal");
            proof {
                assert(self.inv_api(api));
            }
            return false;
        }
        let ghost journal_raw_disk = self.unified_system_inv_journal_pages_parsable();
        let ghost pre_replay_branch = self.branch@;
        let ghost pre_replay_journal = self.journal@;
        proof {
            match &self.journal.status {
                Some(status) => {
                    assert(status.unmarshalled_tail.len() == 0);
                    self.journal.tail_empty_implies_no_unmarshalled_entries();
                },
                None => {
                    assert(false);
                },
            }
            assert(journal_start_lsn as nat == self.journal.seq_start());
            assert(self.journal.seq_start() <= start_lsn as nat);
            assert(journal_end_lsn as nat == self.journal.seq_end());
            assert((start_lsn as nat) < self.journal.seq_end());
            assert(start_lsn as nat == pre_replay_branch.seq_end);
            assert(pre_state.state.branch == pre_replay_branch);
            assert(pre_state.state.journal.journal == pre_replay_journal);
        }
        let ghost pre_replay_cache = self.cache@;
        let replay = self.journal.recover_map_step_for_unified(
            &mut self.cache,
            start_lsn,
            Ghost(journal_raw_disk),
        );
        match replay {
            UnifiedRecoverMapResult::NotInCache{} => {
                api.log("unified-cache journal replay record not in cache");
                proof {
                    assert(self.inv_api(api));
                }
                false
            },
            UnifiedRecoverMapResult::InvalidRecord{} => {
                api.log("unified-cache journal replay invalid record");
                proof {
                    assert(self.inv_api(api));
                }
                false
            },
	            UnifiedRecoverMapResult::FetchSuccess{reads, addr, record, keys, msgs} => {
	                if keys.is_empty() {
	                    api.log("unified-cache journal replay empty record");
		                proof {
	                    let lbls = map_recovery_labels(self.journal.seq_start(), reads@, addr@);
	                    assert(lbls.0 == Cache::Label::Access{
	                        reads: reads@,
                            writes: Map::<Address, RawPage>::empty(),
                        });
                        Cache::State::access_read_only_is_noop(
                            pre_replay_cache,
                            self.cache@,
                            reads@,
                        );
                        assert(self.cache@ == pre_replay_cache);
                        assert(self.inv_api(api));
                    }
                    return false;
		                }
		                proof {
	                    let lbls = map_recovery_labels(self.journal.seq_start(), reads@, addr@);
                    assert(lbls.0 == Cache::Label::Access{
                        reads: reads@,
                        writes: Map::<Address, RawPage>::empty(),
                    });
                    Cache::State::access_read_only_is_noop(
                        pre_replay_cache,
                        self.cache@,
                        reads@,
	                    );
	                    assert(self.cache@ == pre_replay_cache);
		                    assert(self.inv_api(api));
		                }
                let ghost pre_branch_load_state = self.branch.load_state;
                let ghost pre_branch_allocators = self.branch.mini_allocator.allocators@;
                let ghost pre_branch_mini_allocator_i = self.branch.mini_allocator.i();
                let ghost pre_au_pool = self.au_pool@;
		                let append_result = self.branch.replay_append_from_journal(
		                    &mut self.cache,
	                    &keys,
	                    &msgs,
	                    self.disk_au_count,
		                    self.disk_page_count,
                        );
                        proof {
                            assert(self.branch.image.roots_wf());
                        }
		                match append_result {
	                    BranchReplayAppendResult::Appended{
	                        prepared_cache,
	                        branch_reads,
	                        writes,
	                        receipt,
	                        init_root,
	                    } => {
	                        let ghost new_atomic_journal = AtomicJournalState::State{
	                            journal: self.journal@,
	                            ..pre_state.state.journal
	                        };
	                        let ghost prepared_state = UnifiedCacheProgramModel{
	                            state: UnifiedCacheSystem::State{
	                                cache: prepared_cache@,
	                                ..pre_state.state
	                            }
	                        };
	                        let ghost post_state = UnifiedCacheProgramModel{
	                            state: UnifiedCacheSystem::State{
	                                cache: self.cache@,
                                journal: new_atomic_journal,
                                branch: self.branch@,
                                ..pre_state.state
                            }
                        };
                        proof {
                            let journal_lbls = map_recovery_labels(
                                self.journal.seq_start(),
                                reads@,
                                addr@,
                            );
                            let journal_cache_lbl = journal_lbls.0;
                            let journal_lbl = journal_lbls.1;
                            let combined_reads = reads@.union_prefer_right(branch_reads@);
                            let combined_cache_lbl = Cache::Label::Access{
                                reads: combined_reads,
                                writes: writes@,
	                            };
	                            assert(journal_cache_lbl == Cache::Label::Access{
	                                reads: reads@,
	                                writes: Map::<Address, RawPage>::empty(),
	                            });
	                            assert(pre_state.state.cache == pre_replay_cache);
	                            assert(UnifiedCacheSystem::State::cache_internal(
	                                pre_state.state,
	                                prepared_state.state,
	                                UnifiedCacheSystem::Label::Internal,
	                                prepared_cache@,
	                            )) by {
	                            }
	                            assert(UnifiedCacheSystem::State::next_by(
	                                pre_state.state,
	                                prepared_state.state,
	                                UnifiedCacheSystem::Label::Internal,
	                                UnifiedCacheSystem::Step::cache_internal(prepared_cache@),
	                            )) by {
	                                reveal(UnifiedCacheSystem::State::next_by);
	                            }
	                            UnifiedCacheProgramModel::lift_internal_step(pre_state, prepared_state);
	                            self.journal.view_seq_start_ensures();
	                            self.journal.view_seq_end_ensures();
                            assert(self.journal@.seq_start() == self.journal.seq_start()) by {
                                assert(self.journal@.seq_start()
                                    == self.journal@.snapshot.boundary_lsn);
                            }
                            assert(self.journal@.seq_end() == self.journal.seq_end());
                            assert(self.journal@ == pre_replay_journal);
                            assert(self.journal.seq_start() == pre_state.state.journal.journal.seq_start()) by {
                                assert(pre_state.state.journal.journal == pre_replay_journal);
                                assert(pre_replay_journal == self.journal@);
                            }
                            assert(pre_state.state.branch.seq_end() == start_lsn as nat) by {
                                assert(start_lsn as nat == pre_replay_branch.seq_end);
                                assert(pre_state.state.branch == pre_replay_branch);
                            }
                            append_puts_wf(start_lsn as nat, keys@, msgs@);
                            assert(pre_state.state.branch.seq_end() + keys@.len()
                                <= pre_state.state.journal.journal.seq_end()) by {
                                let full_msgs = to_journal_records(reads@)[addr@].message_seq;
                                assert(full_msgs.maybe_discard_old(start_lsn as nat)
                                    == append_puts(start_lsn as nat, keys@, msgs@));
                                assert(append_puts(start_lsn as nat, keys@, msgs@).seq_end
                                    == start_lsn as nat + keys@.len());
                                assert(full_msgs.seq_end <= self.journal.seq_end());
                                assert(full_msgs.wf());
                                assert(start_lsn as nat <= full_msgs.seq_end);
                                assert(full_msgs.maybe_discard_old(start_lsn as nat).seq_end
                                    == full_msgs.seq_end);
                                assert(pre_state.state.journal.journal == pre_replay_journal);
                                assert(self.journal@ == pre_replay_journal);
                                assert(pre_state.state.journal.journal.seq_end()
                                    == self.journal.seq_end());
                            }
	                            assert forall |read_addr: Address|
	                                #[trigger] reads@.contains_key(read_addr)
	                                    && !branch_reads@.contains_key(read_addr)
	                                implies prepared_cache@.valid_read(read_addr, reads@[read_addr]) by {
	                                Cache::State::access_read_valid(
	                                    pre_replay_cache,
	                                    pre_replay_cache,
                                    reads@,
	                                    Map::<Address, RawPage>::empty(),
	                                    read_addr,
	                                );
	                                assert(prepared_cache@.valid_read(read_addr, reads@[read_addr]));
	                            }
	                            Cache::State::access_union_prefer_right_reads(
	                                prepared_cache@,
	                                self.cache@,
	                                branch_reads@,
	                                reads@,
                                writes@,
	                            );
	                            assert(Cache::State::next(
	                                prepared_state.state.cache,
	                                self.cache@,
	                                combined_cache_lbl,
	                            ));
                            assert(reads@ <= combined_reads) by {
                                assert forall |read_addr: Address| #[trigger] reads@.contains_key(read_addr)
                                    implies combined_reads.contains_key(read_addr)
                                        && combined_reads[read_addr] == reads@[read_addr] by {
	                                    if branch_reads@.contains_key(read_addr) {
	                                        Cache::State::access_read_valid(
	                                            prepared_cache@,
	                                            self.cache@,
	                                            branch_reads@,
	                                            writes@,
	                                            read_addr,
	                                        );
	                                        Cache::State::access_read_valid(
	                                            pre_replay_cache,
                                            pre_replay_cache,
                                            reads@,
	                                            Map::<Address, RawPage>::empty(),
	                                            read_addr,
	                                        );
	                                        assert(prepared_cache@.valid_read(read_addr, reads@[read_addr]));
	                                        Cache::State::valid_read_unique(
	                                            prepared_cache@,
	                                            read_addr,
	                                            branch_reads@[read_addr],
	                                            reads@[read_addr],
                                        );
                                    }
                                }
                            }
                            assert(branch_reads@ <= combined_reads) by {
                                assert forall |read_addr: Address| #[trigger] branch_reads@.contains_key(read_addr)
                                    implies combined_reads.contains_key(read_addr)
                                        && combined_reads[read_addr] == branch_reads@[read_addr] by {
                                }
                            }
                            assert(journal_lbl == CachedJournal::Label::ReadForRecovery{
                                messages: to_journal_records(reads@)[addr@]
                                    .message_seq.maybe_discard_old(self.journal.seq_start()),
                                reads: to_journal_records(reads@),
                            });
                            assert(CachedJournal::State::next(
                                pre_state.state.journal.journal,
                                new_atomic_journal.journal,
                                CachedJournal::Label::ReadForRecovery{
                                    messages: to_journal_records(reads@)[addr@]
                                        .message_seq.maybe_discard_old(
                                            pre_state.state.journal.journal.snapshot.boundary_lsn,
                                        ),
                                    reads: to_journal_records(reads@),
                                },
                            )) by {
                                assert(pre_state.state.journal.journal == pre_replay_journal);
                                assert(self.journal@ == pre_replay_journal);
                                assert(new_atomic_journal.journal == pre_replay_journal);
                                assert(pre_state.state.journal.journal.snapshot.boundary_lsn
                                    == self.journal.seq_start());
                            }
                            let atomic_journal_lbl = AtomicJournalState::Label::ReadForRecovery{
                                messages: to_journal_records(reads@)[addr@]
                                    .message_seq.maybe_discard_old(
                                        pre_state.state.journal.journal.snapshot.boundary_lsn,
                                    ),
                                reads: to_journal_records(reads@),
                            };
                            assert(AtomicJournalState::State::read_for_recovery(
                                pre_state.state.journal,
                                new_atomic_journal,
                                atomic_journal_lbl,
                                new_atomic_journal.journal,
                            )) by {
                            }
                            assert(AtomicJournalState::State::next_by(
                                pre_state.state.journal,
                                new_atomic_journal,
                                atomic_journal_lbl,
                                AtomicJournalState::Step::read_for_recovery(
                                    new_atomic_journal.journal,
                                ),
                            )) by {
                                reveal(AtomicJournalState::State::next_by);
                            }
                            assert(AtomicJournalState::State::next(
                                pre_state.state.journal,
                                new_atomic_journal,
                                atomic_journal_lbl,
                            )) by {
                                reveal(AtomicJournalState::State::next);
                            }
                            let atomic_branch_lbl = AtomicBranchState::Label::Append{
                                keys: keys@,
                                msgs: msgs@,
                                receipt: receipt@,
                                init_root: init_root@,
                                read_nodes: to_branch_nodes(branch_reads@),
                                write_nodes: to_branch_nodes(writes@),
                            };
	                            assert(AtomicBranchState::State::next(
	                                pre_state.state.branch,
	                                self.branch@,
	                                atomic_branch_lbl,
	                            )) by {
	                                assert(pre_state.state.branch == pre_replay_branch);
	                            }
	                            AtomicBranchState::State::append_effect(
	                                pre_state.state.branch,
	                                self.branch@,
	                                atomic_branch_lbl,
	                            );
	                            assert(pre_state.state.branch.metadata_loaded());
	                            assert(self.branch@.metadata_loaded());
	                            assert(to_journal_records(reads@)[addr@].message_seq
	                                .maybe_discard_old(pre_state.state.branch.seq_end())
                                == append_puts(pre_state.state.branch.seq_end(), keys@, msgs@)) by {
                                assert(pre_state.state.branch.seq_end() == start_lsn as nat);
                                assert(to_journal_records(reads@)[addr@].message_seq
                                    .maybe_discard_old(start_lsn as nat)
                                    == append_puts(start_lsn as nat, keys@, msgs@));
                            }
	                            assert(UnifiedCacheSystem::State::read_for_recovery(
	                                prepared_state.state,
	                                post_state.state,
	                                UnifiedCacheSystem::Label::Internal,
                                addr@,
                                keys@,
                                msgs@,
                                receipt@,
                                init_root@,
                                reads@,
                                branch_reads@,
                                writes@,
                                self.cache@,
                                new_atomic_journal,
                                self.branch@,
	                            )) by {
	                            }
	                            assert(UnifiedCacheSystem::State::next_by(
	                                prepared_state.state,
	                                post_state.state,
	                                UnifiedCacheSystem::Label::Internal,
                                UnifiedCacheSystem::Step::read_for_recovery(
                                    addr@,
                                    keys@,
                                    msgs@,
                                    receipt@,
                                    init_root@,
                                    reads@,
                                    branch_reads@,
                                    writes@,
                                    self.cache@,
                                    new_atomic_journal,
                                    self.branch@,
                                ),
	                            )) by {
	                                reveal(UnifiedCacheSystem::State::next_by);
	                            }
	                            UnifiedCacheProgramModel::lift_internal_step(prepared_state, post_state);
	                        }
	                        let tracked mut model = KVStoreTokenized::model::arbitrary();
	                        proof {
	                            tracked_swap(self.model.borrow_mut(), &mut model);
	                        }
	                        let tracked _cache_internal_token = self.instance.borrow().internal(
	                            KVStoreTokenized::Label::InternalOp{},
	                            prepared_state,
	                            &mut model,
	                        );
	                        let tracked _replay_token = self.instance.borrow().internal(
	                            KVStoreTokenized::Label::InternalOp{},
	                            post_state,
	                            &mut model,
	                        );
                        self.model = Tracked(model);
                        proof {
                            assert(self.state().cache == self.cache@);
                            assert(self.state().branch == self.branch@);
                            assert(self.state().free_aus =~= self.au_pool@);
                            assert(self.recovery_phase is ReplayingJournal);
                            assert(self.state().recovery_state is MetadataLoadComplete);
                            assert(self.state().journal_metadata_loaded());
                            assert(self.state().branch_metadata_loaded());
                            assert(self.state().journal.journal == self.journal@);
                            assert(self.journal.wf());
                            assert(self.journal.index_ready());
                            assert(self.branch.metadata_loaded());
                            assert(MiniAllocatorImpl::allocators_unique(
                                self.branch.mini_allocator.allocators@,
                            ));
                            assert(self.branch.mini_allocator.bounded(self.disk_au_count));
                            assert(self.branch.active_branch is Some);
                            assert(!(self.branch.active_branch is None));
                            assert(self.branch.active_branch is None
                                && self.branch.mini_allocator.allocation_ready() ==>
                                self.branch.mini_allocator.i().allocated_aus() == Set::<AU>::empty()) by {
                                assert(!(self.branch.active_branch is None));
                            }
                            assert(self.au_pool@.disjoint(
                                MiniAllocatorImpl::allocators_au_set(
                                    self.branch.mini_allocator.allocators@,
                                ),
                            ));
                            assert(self.inv_api(api));
                        }
                        api.log("unified-cache journal replay append");
                        true
                    },
                    BranchReplayAppendResult::NeedsAUs => {
                        api.log("unified-cache journal replay needs branch aus");
                        proof {
                            assert(self.branch.mini_allocator.i() == pre_branch_mini_allocator_i);
                            assert(self.inv_api(api));
                        }
                        false
                    },
                    BranchReplayAppendResult::NeedCacheLoad{addr, handle} => {
                        proof {
                            assert(self.branch.load_state == pre_branch_load_state);
                            assert(self.branch.metadata_loaded());
                            assert(self.branch.mini_allocator.allocators@ == pre_branch_allocators);
                            assert(self.branch.mini_allocator.i() == pre_branch_mini_allocator_i);
                            assert(MiniAllocatorImpl::allocators_unique(
                                self.branch.mini_allocator.allocators@,
                            ));
                            assert(self.au_pool@ == pre_au_pool);
                            assert(self.au_pool@.disjoint(
                                MiniAllocatorImpl::allocators_au_set(
                                    self.branch.mini_allocator.allocators@,
                                ),
                            ));
                            assert(Cache::State::next(
                                self.state().cache,
                                self.cache@,
                                cache_load_label(&addr),
                            ));
                            assert(self.state().outstanding_cache_reqs
                                == Map::<ID, Address>::empty());
                            assert(self.cache_read_io_lag_inv());
                        }
                        self.issue_acquired_cache_read_io(
                            addr,
                            handle,
                            CacheReadPurpose::Generic,
                            api,
                        )
                    },
                    BranchReplayAppendResult::CacheFull => {
                        api.log("unified-cache journal replay cache full");
                        proof {
                            assert(self.branch.mini_allocator.i() == pre_branch_mini_allocator_i);
                            assert(self.inv_api(api));
                        }
                        false
                    },
                    BranchReplayAppendResult::Blocked => {
                        api.log("unified-cache journal replay append blocked");
                        proof {
                            assert(self.branch.mini_allocator.i() == pre_branch_mini_allocator_i);
                            assert(self.inv_api(api));
                        }
                        false
                    },
                }
            },
        }
    }

    fn issue_cache_writeback_io(
        &mut self,
        addr: IAddress,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    ) -> (started: bool)
        requires
            old(self).inv_api(old(api)),
            !(old(self).state().recovery_state is Begin),
            !(old(self).state().recovery_state is AwaitingSuperblock),
            addr@.wf(),
            addr@ != spec_superblock_addr(),
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            !started ==> *self == *old(self),
            self.recovery_phase == old(self).recovery_phase,
    {
        let ghost pre_state = self.model@.value();
        let ghost pre_outstanding = self.outstanding_requests@;
        let ghost pre_cache = self.cache;

        match self.cache.begin_writeback(&addr) {
            WritebackAcquireResult::Acquired{handle} => {
                let write_data = handle.rec.clone();
                proof {
                    assert(self.cache.valid_writeback_handle(&addr, handle));
                    FracCacheImpl::valid_writeback_handle_has_inv(&self.cache, &addr, handle);
                    assert(handle.inv());
                    assert(handle.rec.len() == PAGE_SIZE_BYTES);
                    assert(write_data@ == handle.rec@);
                    assert(write_data.len() == PAGE_SIZE_BYTES);
                }

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }

                let req_id_perm = Tracked(api.send_disk_request_predict_id());
                let disk_req = IDiskRequest::WriteReq{to: addr, data: write_data};
                let ghost req_map = map![req_id_perm@ => disk_req@];
                let ghost updated = map![req_id_perm@ => addr@];
                let ghost disk_request_tuples =
                    multiset_map_singleton(req_id_perm@, disk_req@);
                let ghost disk_response_tuples = Multiset::empty();
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        cache: self.cache@,
                        outstanding_cache_reqs:
                            pre_state.state.outstanding_cache_reqs.union_prefer_right(updated),
                        ..pre_state.state
                    }
                };

                proof {
                    multiset_map_singleton_ensures(req_id_perm@, disk_req@);
                    assert(multiset_to_map(disk_request_tuples) == req_map);
                    Self::singleton_updated_addr_map(req_id_perm@, disk_req@, addr@);
                    assert(updated.is_injective());
                    assert(!updated.contains_value(spec_superblock_addr()));
                    Self::singleton_req_map_values(req_id_perm@, disk_req@);
                    assert(UnifiedCacheSystem::State::cache_io_begin(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        req_map,
                        self.cache@,
                        disk_request_tuples,
                        disk_response_tuples,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    let info = ProgramDiskInfo{
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheProgramModel::disk_step_matches_info(
                        pre_state.state,
                        UnifiedCacheSystem::Step::cache_io_begin(
                            req_map,
                            self.cache@,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                        info,
                    ));
                    UnifiedCacheProgramModel::lift_disk_step(pre_state, post_state, info);
                }

                let tracked empty_disk_responses = DiskRespShard::empty(self.instance_id());
                let tracked new_disk_req_token = self.instance.borrow().disk_transitions(
                    KVStoreTokenized::Label::DiskOp{
                        disk_request_tuples,
                        disk_response_tuples,
                    },
                    post_state,
                    &mut model,
                    empty_disk_responses,
                );
                self.model = Tracked(model);

                let id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));
                self.outstanding_requests.insert(id, OutstandingReqInfo::CacheWrite{
                    addr,
                    write_handle: handle,
                });

                proof {
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                        assert(old(self).outstanding_cache_reqs_match_model());
                        assert(pre_state.state.outstanding_cache_reqs.dom()
                            == pre_outstanding.dom());
                        assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty());
                        assert_maps_equal!(
                            pre_state.state.outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            k => {
                                if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                                    assert(pre_state.state.outstanding_cache_reqs.dom().contains(k));
                                    assert(pre_outstanding.dom().contains(k));
                                    assert(false);
                                }
                            }
                        );
                    }
                    assert(self.state().outstanding_cache_reqs == map![id => addr@]) by {
                        assert(post_state.state.outstanding_cache_reqs
                            == pre_state.state.outstanding_cache_reqs.union_prefer_right(updated));
                        assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                        assert(updated == map![req_id_perm@ => addr@]);
                        assert(id == req_id_perm@);
                        assert_maps_equal!(self.state().outstanding_cache_reqs, map![id => addr@], k => {
                            if k == id {
                                assert(updated.contains_key(k));
                            } else {
                                assert(!updated.contains_key(k));
                            }
                        });
                    }
                    assert(self.outstanding_requests_wf()) by {
                        assert forall |id2: ID| #[trigger] self.outstanding_requests@.contains_key(id2)
                            implies {
                                match self.outstanding_requests@[id2] {
                                    OutstandingReqInfo::CacheRead{addr, load_handle, ..} => {
                                        &&& self.cache.entry_fetched(&addr)
                                        &&& self.cache.valid_load_handle(&addr, load_handle)
                                    },
                                    OutstandingReqInfo::CacheWrite{addr, write_handle} => {
                                        &&& self.cache.entry_fetched(&addr)
                                        &&& self.cache.valid_writeback_handle(&addr, write_handle)
                                    },
                                    OutstandingReqInfo::SuperblockWrite => true,
                                }
                            } by {
                            if id2 == id {
                            } else {
                                assert(pre_outstanding == Map::<ID, OutstandingReqInfo>::empty());
                                assert(!pre_outstanding.contains_key(id2));
                                assert(false);
                            }
                        }
                    }
                    assert(self.outstanding_requests@.dom() =~= set![id]);
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                }
                true
            },
            WritebackAcquireResult::NotPresent
            | WritebackAcquireResult::NotDirty
            | WritebackAcquireResult::Busy => {
                proof {
                    assert(self.cache@ == pre_cache@);
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                }
                false
            },
        }
    }

    fn recover_begin(&mut self, api: &mut ClientAPI<UnifiedCacheProgramModel>)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is FetchingSuperblock,
            old(self).state().recovery_state is Begin,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase is FetchingSuperblock,
            self.state().recovery_state is AwaitingSuperblock,
    {
        // api.log("unified-cache recovery begins");
        api.log("unified-cache recovery begins");

        let ghost pre_state = self.model@.value();
        let tracked mut model = KVStoreTokenized::model::arbitrary();
        proof {
            tracked_swap(self.model.borrow_mut(), &mut model);
        }

        let req_id_perm = Tracked(api.send_disk_request_predict_id());
        let disk_req = IDiskRequest::ReadReq{from: superblock_addr()};
        let ghost read_req = DiskRequest::ReadReq{from: spec_superblock_addr()};
        let ghost disk_request_tuples = multiset_map_singleton(req_id_perm@, disk_req@);
        let ghost disk_response_tuples = Multiset::empty();
        let ghost post_state = UnifiedCacheProgramModel{
            state: UnifiedCacheSystem::State{
                recovery_state: RecoveryState::AwaitingSuperblock,
                ..pre_state.state
            }
        };

        proof {
            multiset_map_singleton_ensures(req_id_perm@, disk_req@);
            assert(disk_req@ == read_req);
            assert(disk_request_tuples == Multiset::empty().insert((req_id_perm@, read_req)));
            assert(UnifiedCacheSystem::State::initiate_recovery(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Disk,
                req_id_perm@,
                disk_request_tuples,
                disk_response_tuples,
            )) by {
            }
            assert(UnifiedCacheSystem::State::next_by(
                pre_state.state,
                post_state.state,
                UnifiedCacheSystem::Label::Disk,
                UnifiedCacheSystem::Step::initiate_recovery(
                    req_id_perm@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
            )) by {
                reveal(UnifiedCacheSystem::State::next_by);
            }
            let info = ProgramDiskInfo{
                reqs: disk_request_tuples,
                resps: disk_response_tuples,
            };
            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                pre_state.state,
                UnifiedCacheSystem::Step::initiate_recovery(
                    req_id_perm@,
                    disk_request_tuples,
                    disk_response_tuples,
                ),
                info,
            ));
            UnifiedCacheProgramModel::lift_disk_step(pre_state, post_state, info);
        }

        let tracked empty_disk_responses = DiskRespShard::empty(self.instance_id());
        let tracked new_disk_req_token = self.instance.borrow().disk_transitions(
            KVStoreTokenized::Label::DiskOp{
                disk_request_tuples,
                disk_response_tuples,
            },
            post_state,
            &mut model,
            empty_disk_responses,
        );
        self.model = Tracked(model);

        let _id = api.send_disk_request(disk_req, req_id_perm, Tracked(new_disk_req_token));

        proof {
            assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                assert(old(self).outstanding_cache_reqs_match_model());
                assert(pre_state.state.outstanding_cache_reqs.dom()
                    == old(self).outstanding_requests@.dom());
                assert(old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                assert_maps_equal!(
                    pre_state.state.outstanding_cache_reqs,
                    Map::<ID, Address>::empty(),
                    k => {
                        if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                            assert(pre_state.state.outstanding_cache_reqs.dom().contains(k));
                            assert(old(self).outstanding_requests@.dom().contains(k));
                            assert(!old(self).outstanding_requests@.contains_key(k));
                            assert(false);
                        }
                    }
                );
            }
            assert(self.state().cache == self.cache@);
            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
            assert(self.outstanding_requests@ == old(self).outstanding_requests@);
            assert(self.outstanding_requests_wf());
            assert(self.outstanding_cache_reqs_match_model());
            assert(self.outstanding_requests_single_flight());
        }
    }

    fn recover_step(&mut self, api: &mut ClientAPI<UnifiedCacheProgramModel>) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is FetchingSuperblock ==> old(self).state().recovery_state is AwaitingSuperblock,
            old(self).recovery_phase is LoadingJournal ==> old(self).state().recovery_state is SuperblockAvailable,
            old(self).recovery_phase is LoadingJournal ==> old(self).state().journal.journal == old(self).journal@,
            old(self).recovery_phase is LoadingBranch ==> old(self).state().recovery_state is SuperblockAvailable,
            old(self).recovery_phase is ReplayingJournal ==> old(self).state().recovery_state is MetadataLoadComplete,
        ensures
            self.inv_api(api),
            !(self.recovery_phase is FetchingSuperblock),
            self.recovery_phase is LoadingJournal ==> self.state().recovery_state is SuperblockAvailable,
            self.recovery_phase is LoadingJournal ==> self.state().journal.journal == self.journal@,
            self.recovery_phase is LoadingBranch ==> self.state().recovery_state is SuperblockAvailable,
            self.recovery_phase is ReplayingJournal ==> self.state().recovery_state is MetadataLoadComplete,
    {
        // api.log("unified-cache recovery skeleton step");
        // self.recovery_phase = RecoveryPhase::ReadyForUserOperation;
        // true
        match self.recovery_phase {
            RecoveryPhase::FetchingSuperblock => {
                api.log("await unified-cache superblock response");

                let ghost pre_state = self.model@.value();
                let DiskResponseRecord{
                    id: disk_req_id,
                    disk_response: i_disk_response,
                    token: disk_response_token,
                } = api.blocking_receive_disk_response();
                let ghost recovered_superblock_raw = i_disk_response@->data;

                proof {
                    let sys_model =
                        open_system_invariant_disk_response_singleton::<
                            UnifiedCacheProgramModel,
                            UnifiedCacheRefinementProof,
                        >(
                            self.model,
                            disk_response_token,
                            disk_req_id,
                            i_disk_response@,
                        );
                    assert(UnifiedCacheRefinementProof::inv(sys_model));
                    assert(sys_model.program == pre_state);
                    assert(UnifiedCacheSystemRefinement::inv(sys_model));
                    UnifiedCacheSystemRefinement::recovery_superblock_response_facts(
                        sys_model,
                        disk_req_id,
                        i_disk_response@,
                    );
                    assert(sys_model.program.state.recovery_state is AwaitingSuperblock);
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                    assert(!sys_model.program.state.outstanding_cache_reqs.contains_key(disk_req_id)) by {
                        assert(sys_model.program.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                    }
                    assert(sys_model.disk.responses.contains_key(disk_req_id));
                    assert(sys_model.disk.responses[disk_req_id] == i_disk_response@);
                    assert(i_disk_response@ is ReadResp);
                    assert(sys_model.disk.responses[disk_req_id]->data
                        == sys_model.disk.content[spec_superblock_addr()]);
                    assert(abstract_superblock_raw_wf(i_disk_response@->data));
                }

                let raw_page = match i_disk_response {
                    IDiskResponse::ReadResp{data} => data,
                    IDiskResponse::WriteResp{} => {
                        unreached()
                    },
                };
                proof {
                    assert(raw_page@ == recovered_superblock_raw);
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
                let bootstrap_au = bootstrap_alloc_au(self.disk_au_count);
                self.persistent_journal_seq_end = superblock.payload.journal.seq_end;
                self.journal = JournalImpl::new(superblock.payload.journal.snapshot, bootstrap_au);
                let branch_seq_end =
                    superblock.payload.branch.betree.seq_end;
                let initial_persisted_root_count = superblock.payload.branch.roots.len();
                proof {
                    let image = layout.spec_parse(raw_page@);
                    assert(image.wf());
                    assert(superblock@ == layout.spec_parse_inner(raw_page@));
                    assert(superblock@@ == image);
                    assert(superblock@.wf());
                    assert(superblock@.geometry.formatted_au_count
                        <= self.disk_au_count as nat);
                    assert(self.journal.snapshot_geometry_bounded(
                        self.disk_au_count,
                    )) by {
                        assert(self.journal@.snapshot
                            == superblock@.payload.journal.snapshot);
                        assert(superblock@.addresses_bounded());
                    }
                    assert forall |i: int| 0 <= i < superblock.payload.branch.roots@.len()
                        implies #[trigger] superblock.payload.branch.roots@[i]@.wf() by {
                        assert(superblock.payload.branch.roots@[i]@
                            == superblock@.payload.branch.roots[i]);
                        assert(superblock@.payload.branch.roots[i] == image.branch_roots[i]);
                        assert(image.branch_roots[i].wf());
                    }
                }
                let branch_image_impl = BranchImageImpl::from_parts(
                    superblock.payload.branch.roots,
                    branch_seq_end,
                );
                proof {
                    assert(branch_image_impl.roots_bounded(self.disk_au_count)) by {
                        assert forall |i: int|
                            0 <= i < branch_image_impl.sealed_roots@.len()
                            implies #[trigger] branch_image_impl.sealed_roots@[i]@.au
                                < self.disk_au_count as nat by {
                            assert(branch_image_impl.sealed_roots@[i]@
                                == superblock@.payload.branch.roots[i]);
                            assert(superblock@.addresses_bounded());
                            assert(superblock@.geometry.formatted_au_count
                                <= self.disk_au_count as nat);
                        }
                    }
                }
                self.branch.initialize_from_image(
                    branch_image_impl,
                    initial_persisted_root_count,
                    self.disk_au_count,
                );

                let ghost image = layout.spec_parse(raw_page@);
                let ghost branch_image = crate::implementation::AtomicBranchState_v::AtomicBranchImage{
                    sealed_roots: image.branch_roots,
                    seq_end: image.branch_seq_end,
                };
                let ghost new_journal = AtomicJournalState::State{
                    journal: CachedJournal::State{
                        snapshot: image.journal_snapshot,
                        status: None,
                    },
                    mini_allocator: MiniAllocator::empty(),
                    persistent_seq_end: image.journal_seq_end,
                    in_flight: None,
                    prepared: false,
                };
                let ghost new_branch = AtomicBranchState::State{
                    image: branch_image,
                    persistent_image: branch_image,
                    in_flight: None,
                    prepared: false,
                    branch_summary: Map::empty(),
                    persisted_root_count: image.branch_roots.len() as nat,
                    active_branch: CachedBranch::State::empty_active(),
                    mini_allocator: MiniAllocator::empty(),
                    seq_end: image.branch_seq_end,
                };
                let ghost disk_request_tuples = Multiset::empty();
                let ghost disk_response_tuples = multiset_map_singleton(disk_req_id, i_disk_response@);
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        recovery_state: RecoveryState::SuperblockAvailable,
                        journal: new_journal,
                        branch: new_branch,
                        persistent_image: Some(image),
                        sync_phase: AtomicSyncPhase::None,
                        sync_req_map: Map::empty(),
                        ..pre_state.state
                    }
                };

                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }

                proof {
                    assert(i_disk_response@ is ReadResp);
                    assert(i_disk_response@->data == raw_page@);
                    assert(abstract_superblock_raw_wf(raw_page@));
                    assert(image.wf());
                    assert(superblock_matches(raw_page@, image));
                    assert(AtomicJournalState::State::initialize(
                        new_journal,
                        image.journal_snapshot,
                        image.journal_seq_end,
                    )) by {
                    }
                    assert(AtomicBranchState::State::initialize(
                        new_branch,
                        branch_image,
                        image.branch_roots.len() as nat,
                    )) by {
                    }
                    multiset_map_singleton_ensures(disk_req_id, i_disk_response@);
                    assert(disk_response_tuples == Multiset::empty().insert((
                        disk_req_id,
                        DiskResponse::ReadResp{data: raw_page@},
                    )));
                    assert(UnifiedCacheSystem::State::superblock_recovery(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        disk_req_id,
                        raw_page@,
                        image,
                        new_journal,
                        new_branch,
                        disk_request_tuples,
                        disk_response_tuples,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Disk,
                        UnifiedCacheSystem::Step::superblock_recovery(
                            disk_req_id,
                            raw_page@,
                            image,
                            new_journal,
                            new_branch,
                            disk_request_tuples,
                            disk_response_tuples,
                        ),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    let info = ProgramDiskInfo{
                        reqs: disk_request_tuples,
                        resps: disk_response_tuples,
                    };
                    assert(UnifiedCacheProgramModel::disk_step_matches_info(
                        pre_state.state,
                        UnifiedCacheSystem::Step::superblock_recovery(
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
                    UnifiedCacheProgramModel::lift_disk_step(pre_state, post_state, info);
                }

                let tracked _disk_req_token = self.instance.borrow().disk_transitions(
                    KVStoreTokenized::Label::DiskOp{
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
                    assert(self.state().cache == self.cache@);
                    assert(superblock@ == layout.spec_parse_inner(raw_page@));
                    assert(superblock@@ == image);
                    assert(self.journal@.snapshot == image.journal_snapshot);
                    assert(self.journal.snapshot_geometry_bounded(
                        self.disk_au_count,
                    )) by {
                        assert(self.journal@.snapshot
                            == superblock@.payload.journal.snapshot);
                        assert(superblock@.addresses_bounded());
                        assert(superblock@.geometry.formatted_au_count
                            <= self.disk_au_count as nat);
                    }
                    self.journal.view_ensures();
                    assert(!self.journal.index_ready());
                    assert(self.journal@.status is None);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.mini_allocator == self.journal.journal_alloc.i()) by {
                        assert(post_state.state.journal.mini_allocator == MiniAllocator::empty());
                        assert(self.journal.journal_alloc.i() == MiniAllocator::empty());
                    }
                    assert(MiniAllocatorImpl::allocators_unique(self.journal.journal_alloc.allocators@));
                    assert(self.au_pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(
                            self.journal.journal_alloc.allocators@,
                        ),
                    )) by {
                        assert(MiniAllocatorImpl::allocators_au_set(
                            self.journal.journal_alloc.allocators@,
                        ) =~= Set::<AU>::empty());
                    }
                    assert(self.state().branch == self.branch@);
                    assert(self.branch.image.roots_bounded(self.disk_au_count)) by {
                        assert(self.branch.image@ == branch_image_impl@);
                        assert(branch_image_impl.roots_bounded(self.disk_au_count));
                    }
                    assert(self.persistent_component_alignment()) by {
                        reveal(Implementation::persistent_component_alignment);
                        assert(self.branch.persistent_seq_end as nat
                            == image.branch_seq_end);
                        self.journal.view_seq_start_ensures();
                        assert(self.journal@.snapshot.boundary_lsn
                            == image.journal_snapshot.boundary_lsn);
                        assert(self.journal.seq_start()
                            == image.journal_snapshot.boundary_lsn);
                        assert(image.branch_seq_end
                            == image.journal_snapshot.boundary_lsn);
                    }
                    assert(post_state.state.outstanding_cache_reqs == pre_state.state.outstanding_cache_reqs);
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
                    assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                    assert(self.outstanding_requests@ == old(self).outstanding_requests@);
                    assert(self.outstanding_requests_wf());
                    assert(self.outstanding_cache_reqs_match_model());
                    assert(self.outstanding_requests_single_flight());
                    assert(old(self).recovery_sync_empty()) by {
                        reveal(Implementation::inv_api);
                        reveal(Implementation::inv);
                    }
                    assert(self.sync_requests == old(self).sync_requests);
                    assert(self.in_flight_sync == old(self).in_flight_sync);
                    assert(self.state().sync_phase is None);
                    assert(self.state().sync_req_map == Map::<SyncReqId, nat>::empty());
                    assert(self.recovery_sync_empty()) by {
                        reveal(Implementation::recovery_sync_empty);
                        reveal(Implementation::sync_requests_empty);
                    }
                    self.sync_wf_from_empty();
                    assert(self.inv_api(api));
                }
                true
            },
            RecoveryPhase::LoadingJournal => {
                let outstanding_empty = self.outstanding_requests.is_empty();
                if !outstanding_empty {
                    return false;
                }
                proof {
                    assert(self.outstanding_requests@.is_empty());
                    assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                        assert_maps_equal!(
                            self.outstanding_requests@,
                            Map::<ID, OutstandingReqInfo>::empty(),
                            id => {
                                if self.outstanding_requests@.contains_key(id) {
                                    assert(!self.outstanding_requests@.is_empty());
                                    assert(false);
                                }
                            }
                        );
                    }
                    assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                        assert(self.outstanding_cache_reqs_match_model());
                        assert(self.state().outstanding_cache_reqs.dom()
                            == self.outstanding_requests@.dom());
                        assert_maps_equal!(
                            self.state().outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if self.state().outstanding_cache_reqs.contains_key(id) {
                                    assert(self.state().outstanding_cache_reqs.dom().contains(id));
                                    assert(self.outstanding_requests@.dom().contains(id));
                                    assert(!self.outstanding_requests@.contains_key(id));
                                    assert(false);
                                }
                            }
                        );
                    }
                }
                let index_ready = self.journal.exec_index_ready();
                if index_ready {
                    api.log("unified-cache journal model transition pending");
                    false
                } else {
                    proof {
                        broadcast use JournalImpl::view_ensures;
                        assert(index_ready == self.journal.index_ready());
                        assert(!self.journal.index_ready());
                        assert(self.journal@.status is None);
                    }
                    match self.journal.exec_freshest_rec() {
                        None => {
                            let ghost pre_state = self.model@.value();
                            let ghost pre_journal_view = self.journal@;
                            let reads = self.journal.recover_empty_index();
                            let ghost journal_reads = to_journal_records(reads@);
                            let ghost discovered_aus = Set::<AU>::empty();
                            let ghost new_atomic_journal = AtomicJournalState::State{
                                journal: self.journal@,
                                ..pre_state.state.journal
                            };
                            let ghost post_state = UnifiedCacheProgramModel{
                                state: UnifiedCacheSystem::State{
                                    cache: self.cache@,
                                    journal: new_atomic_journal,
                                    free_aus: pre_state.state.free_aus - discovered_aus,
                                    ..pre_state.state
                                }
                            };

                            let tracked mut model = KVStoreTokenized::model::arbitrary();
                            proof {
                                tracked_swap(self.model.borrow_mut(), &mut model);
                            }

                            proof {
                                assert(pre_state.state.recovery_state is SuperblockAvailable);
                                assert(pre_state.state.journal.journal == pre_journal_view);
                                assert(pre_state.state.cache == self.cache@);
                                assert(reads@ == Map::<Address, crate::spec::AsyncDisk_t::RawPage>::empty());
                                assert(journal_reads =~= Map::<Address, crate::journal::LinkedJournal_v::JournalRecord>::empty()) by {
                                    assert_maps_equal!(
                                        journal_reads,
                                        Map::<Address, crate::journal::LinkedJournal_v::JournalRecord>::empty(),
                                        addr => {
                                        }
                                    );
                                }

                                let cache_lbl = Cache::Label::Access{
                                    reads: reads@,
                                    writes: Map::empty(),
                                };
                                assert forall |addr| #[trigger] cache_lbl->reads.contains_key(addr)
                                    implies pre_state.state.cache.valid_read(addr, cache_lbl->reads[addr]) by {
                                    assert(reads@ == Map::<Address, crate::spec::AsyncDisk_t::RawPage>::empty());
                                }
                                assert forall |addr| #[trigger] cache_lbl->writes.contains_key(addr)
                                    implies pre_state.state.cache.valid_write(addr) by {
                                }
                                let updated_entries = pre_state.state.cache.write_updated_entries(cache_lbl->writes);
                                let updated_status_map = pre_state.state.cache.write_updated_status(cache_lbl->writes);
                                assert(cache_lbl->writes == Map::<Address, crate::spec::AsyncDisk_t::RawPage>::empty());
                                assert(pre_state.state.cache.entries.union_prefer_right(updated_entries)
                                    =~= pre_state.state.cache.entries);
                                assert(pre_state.state.cache.status_map.union_prefer_right(updated_status_map)
                                    =~= pre_state.state.cache.status_map);
                                assert(Cache::State::next_by(
                                    pre_state.state.cache,
                                    self.cache@,
                                    cache_lbl,
                                    Cache::Step::access{},
                                )) by {
                                    reveal(Cache::State::next_by);
                                }
                                assert(Cache::State::next(
                                    pre_state.state.cache,
                                    self.cache@,
                                    cache_lbl,
                                )) by {
                                    reveal(Cache::State::next);
                                }

                                let atomic_lbl = AtomicJournalState::Label::LoadIndex{
                                    reads: journal_reads,
                                    discovered_aus,
                                };
                                assert(AtomicJournalState::State::load_index(
                                    pre_state.state.journal,
                                    new_atomic_journal,
                                    atomic_lbl,
                                    self.journal@,
                                    0,
                                    0,
                                )) by {
                                }
                                assert(AtomicJournalState::State::next_by(
                                    pre_state.state.journal,
                                    new_atomic_journal,
                                    atomic_lbl,
                                    AtomicJournalState::Step::load_index(self.journal@, 0, 0),
                                )) by {
                                    reveal(AtomicJournalState::State::next_by);
                                }
                                assert(AtomicJournalState::State::next(
                                    pre_state.state.journal,
                                    new_atomic_journal,
                                    atomic_lbl,
                                )) by {
                                    reveal(AtomicJournalState::State::next);
                                }

                                assert(UnifiedCacheSystem::State::journal_load_index(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                    reads@,
                                    reads@,
                                    discovered_aus,
                                    self.cache@,
                                    new_atomic_journal,
                                )) by {
                                }
                                assert(UnifiedCacheSystem::State::next_by(
                                    pre_state.state,
                                    post_state.state,
                                    UnifiedCacheSystem::Label::Internal,
                                    UnifiedCacheSystem::Step::journal_load_index(
                                        reads@,
                                        reads@,
                                        discovered_aus,
                                        self.cache@,
                                        new_atomic_journal,
                                    ),
                                )) by {
                                    reveal(UnifiedCacheSystem::State::next_by);
                                }
                                UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                            }

                            let tracked _internal_token = self.instance.borrow().internal(
                                KVStoreTokenized::Label::InternalOp{},
                                post_state,
                                &mut model,
                            );
                            self.model = Tracked(model);
                            self.recovery_phase = RecoveryPhase::LoadingBranch;
                            proof {
                                assert(self.state().journal.mini_allocator
                                    == self.journal.journal_alloc.i()) by {
                                    assert(new_atomic_journal.mini_allocator
                                        == pre_state.state.journal.mini_allocator);
                                }
                                assert(self.state().journal.mini_allocator == MiniAllocator::empty()) by {
                                    assert(new_atomic_journal.mini_allocator
                                        == pre_state.state.journal.mini_allocator);
                                }
                                assert(self.branch.metadata_recovery_wf());
                                assert(self.persistent_component_alignment()) by {
                                    reveal(Implementation::persistent_component_alignment);
                                    assert(self.branch == old(self).branch);
                                    assert(self.journal.seq_start() == old(self).journal.seq_start());
                                    assert(old(self).persistent_component_alignment());
                                }
                            }
                            api.log("unified-cache empty journal index recovered");
                            true
                        },
                        Some(_) => {
                            let ghost journal_raw_disk = self.unified_system_inv_journal_pages_parsable();
                            proof {
                                assert(!self.journal.index_ready());
                                assert(self.journal@.status is None);
                                assert(self.journal@.snapshot.freshest_rec() is Some ==>
                                    journal_disk_load_index_inv(
                                        DiskView{
                                            boundary_lsn: self.journal@.snapshot.boundary_lsn,
                                            entries: to_journal_records(journal_raw_disk),
                                        },
                                        self.journal@.snapshot.freshest_rec(),
                                        self.journal@.snapshot.first()));
                            }
                            let step = self.journal.recover_index_step_for_unified(
                                &mut self.cache,
                                Ghost(journal_raw_disk),
                                self.disk_au_count,
                            );
                            match step {
                                UnifiedRecoverIndexResult::CacheLoad{slot_handle, addr} => {
                                    proof {
                                        assert(addr@ != spec_superblock_addr());
                                        assert(self.state().journal.mini_allocator
                                            == self.journal.journal_alloc.i()) by {
                                            assert(old(self).state().journal.mini_allocator
                                                == old(self).journal.journal_alloc.i());
                                        }
                                        assert(self.state().journal.mini_allocator
                                            == MiniAllocator::empty()) by {
                                            assert(old(self).state().journal.mini_allocator
                                                == MiniAllocator::empty());
                                        }
                                    }
                                    self.issue_acquired_cache_read_io(
                                        addr,
                                        slot_handle,
                                        CacheReadPurpose::JournalIndex,
                                        api,
                                    );
                                    api.log("unified-cache journal index cache read");
                                    true
                                },
                                UnifiedRecoverIndexResult::IndexComplete{reads, discovered_aus} => {
                                    self.record_journal_load_index_complete(reads, discovered_aus, api);
                                    api.log("unified-cache journal index recovered");
                                    true
                                },
                                UnifiedRecoverIndexResult::IndexProgress{} => {
                                    api.log("unified-cache journal index recovery progress");
                                    false
                                },
                            }
                        },
                    }
                }
            },
            RecoveryPhase::LoadingBranch => {
                let ghost pre_state = self.model@.value();
                let ghost pre_branch = self.branch@;
                let ghost pre_cache = self.cache@;
                let ghost pre_pool = self.au_pool@;
                let outstanding_empty = self.outstanding_requests.is_empty();
                if !outstanding_empty {
                    return false;
                }

                proof {
                    assert(self.outstanding_requests@.is_empty());
                    assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                        assert_maps_equal!(
                            self.outstanding_requests@,
                            Map::<ID, OutstandingReqInfo>::empty(),
                            id => {
                                if self.outstanding_requests@.contains_key(id) {
                                    assert(!self.outstanding_requests@.is_empty());
                                    assert(false);
                                }
                            }
                        );
                    }
                    assert(pre_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                        assert(self.outstanding_cache_reqs_match_model());
                        assert(pre_state.state.outstanding_cache_reqs.dom()
                            == self.outstanding_requests@.dom());
                        assert_maps_equal!(
                            pre_state.state.outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if pre_state.state.outstanding_cache_reqs.contains_key(id) {
                                    assert(pre_state.state.outstanding_cache_reqs.dom().contains(id));
                                    assert(self.outstanding_requests@.dom().contains(id));
                                    assert(!self.outstanding_requests@.contains_key(id));
                                    assert(false);
                                }
                            }
                        );
                    }
                }

                let step = self.branch.recover_metadata_step(
                    &mut self.cache,
                    self.disk_au_count,
                    self.disk_page_count,
                );
                match step {
                    BranchMetadataStepResult::NeedCacheLoad{addr, handle, kind} => {
                        proof {
                            assert(self.branch@ == pre_branch);
                            assert(old(self).branch.image.roots_bounded(
                                old(self).disk_au_count,
                            )) by {
                                reveal(Implementation::inv_api);
                                reveal(Implementation::inv);
                            }
                            assert(self.branch.image.roots_bounded(
                                self.disk_au_count,
                            )) by {
                                assert(self.branch.image@
                                    == old(self).branch.image@);
                                assert(self.disk_au_count
                                    == old(self).disk_au_count);
                            }
                            assert(self.state().branch == self.branch@);
                            assert(Cache::State::next(
                                self.state().cache,
                                self.cache@,
                                cache_load_label(&addr),
                            ));
                            assert(self.state().outstanding_cache_reqs
                                == Map::<ID, Address>::empty());
                            assert(self.cache_read_io_lag_inv());
                        }
                        self.issue_acquired_cache_read_io(
                            addr,
                            handle,
                            CacheReadPurpose::BranchMetadata{kind},
                            api,
                        )
                    },
                    BranchMetadataStepResult::RootComplete{root, reads, discovered_aus} => {
                        let ghost pool_discovered = iau_vec_set(discovered_aus@);
                        let ghost branch_discovered = iau_seq_set(discovered_aus@);
                        self.au_pool.remove_aus(self.disk_au_count, discovered_aus);
                        let ghost post_state = UnifiedCacheProgramModel{
                            state: UnifiedCacheSystem::State{
                                cache: self.cache@,
                                free_aus: pre_state.state.free_aus - branch_discovered,
                                branch: self.branch@,
                                ..pre_state.state
                            }
                        };
                        let tracked mut model = KVStoreTokenized::model::arbitrary();
                        proof {
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }
                        proof {
                            assert(pre_state.state.recovery_state is SuperblockAvailable);
                            assert(pre_state.state.cache == pre_cache);
                            assert(pre_state.state.branch == pre_branch);
                            Self::iau_vec_set_matches_branch_set(discovered_aus@);
                            assert(pool_discovered =~= branch_discovered);
                            assert(Cache::State::next(
                                pre_state.state.cache,
                                self.cache@,
                                Cache::Label::Access{reads: reads@, writes: Map::empty()},
                            ));
                            assert(AtomicBranchState::State::next(
                                pre_state.state.branch,
                                self.branch@,
                                AtomicBranchState::Label::LoadMetadata{
                                    root: root@,
                                    discovered_aus: branch_discovered,
                                    read_nodes: crate::implementation::AtomicBranchState_v::to_branch_nodes(reads@),
                                },
                            ));
                            assert(UnifiedCacheSystem::State::branch_load_metadata(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Internal,
                                root@,
                                reads@,
                                branch_discovered,
                                self.cache@,
                                self.branch@,
                            )) by {
                            }
                            assert(UnifiedCacheSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Internal,
                                UnifiedCacheSystem::Step::branch_load_metadata(
                                    root@,
                                    reads@,
                                    branch_discovered,
                                    self.cache@,
                                    self.branch@,
                                ),
                            )) by {
                                reveal(UnifiedCacheSystem::State::next_by);
                            }
                            UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                        }
                        let tracked _internal_token = self.instance.borrow().internal(
                            KVStoreTokenized::Label::InternalOp{},
                            post_state,
                            &mut model,
                        );
                        self.model = Tracked(model);
                        proof {
                            assert(self.state().free_aus =~= self.au_pool@) by {
                                assert(self.au_pool@ =~= pre_pool - pool_discovered);
                                assert(pool_discovered =~= branch_discovered);
                                assert(pre_state.state.free_aus =~= pre_pool);
                            }
                            assert(self.state().cache == self.cache@);
                            assert(self.state().branch == self.branch@);
                            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                        }
                        true
                    },
                    BranchMetadataStepResult::AllComplete => {
                        let ghost post_state = UnifiedCacheProgramModel{
                            state: UnifiedCacheSystem::State{
                                recovery_state: RecoveryState::MetadataLoadComplete,
                                ..pre_state.state
                            }
                        };
                        let tracked mut model = KVStoreTokenized::model::arbitrary();
                        proof {
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }
                        proof {
                            assert(pre_state.state.recovery_state is SuperblockAvailable);
                            assert(pre_state.state.journal_metadata_loaded());
                            assert(self.branch@ == pre_branch);
                            assert(pre_state.state.branch_metadata_loaded()) by {
                                assert(pre_state.state.branch == pre_branch);
                                assert(self.branch@.metadata_loaded());
                            }
                            assert(pre_state.state.branch.mini_allocator == MiniAllocator::empty()) by {
                                assert(pre_state.state.branch == pre_branch);
                                assert(self.branch@.mini_allocator == MiniAllocator::empty());
                            }
                            assert(UnifiedCacheSystem::State::metadata_load_complete(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Internal,
                            )) by {
                            }
                            assert(UnifiedCacheSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Internal,
                                UnifiedCacheSystem::Step::metadata_load_complete(),
                            )) by {
                                reveal(UnifiedCacheSystem::State::next_by);
                            }
                            UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                        }
                        let tracked _internal_token = self.instance.borrow().internal(
                            KVStoreTokenized::Label::InternalOp{},
                            post_state,
                            &mut model,
                        );
                        self.model = Tracked(model);
                        self.recovery_phase = RecoveryPhase::ReplayingJournal;
                        proof {
                            assert(self.state().cache == self.cache@);
                            assert(self.state().branch == self.branch@);
                            assert(self.state().free_aus =~= self.au_pool@);
                            assert(self.state().journal.mini_allocator
                                == self.journal.journal_alloc.i()) by {
                                assert(post_state.state.journal == pre_state.state.journal);
                            }
                            assert(self.state().journal.mini_allocator == MiniAllocator::empty()) by {
                                assert(post_state.state.journal == pre_state.state.journal);
                            }
                            assert(self.journal.index_aus_bounded(
                                self.disk_au_count,
                            )) by {
                                reveal(Implementation::inv_api);
                                reveal(Implementation::inv);
                                assert(self.journal == old(self).journal);
                            }
                            assert(self.branch.image.roots_bounded(
                                self.disk_au_count,
                            )) by {
                                reveal(Implementation::inv_api);
                                reveal(Implementation::inv);
                                assert(self.branch.image@
                                    == old(self).branch.image@);
                            }
                            assert(self.branch@.mini_allocator == MiniAllocator::empty());
                            self.branch.mini_allocator.empty_view_implies_no_allocators();
                            assert(!self.branch.mini_allocator.allocation_ready());
                            self.branch.mini_allocator
                                .not_allocation_ready_implies_allocated_aus_empty();
                            assert(MiniAllocatorImpl::allocators_unique(
                                self.branch.mini_allocator.allocators@,
                            ));
                            assert(self.au_pool@.disjoint(
                                MiniAllocatorImpl::allocators_au_set(
                                    self.branch.mini_allocator.allocators@,
                                ),
                            )) by {
                                assert(MiniAllocatorImpl::allocators_au_set(
                                    self.branch.mini_allocator.allocators@,
                                ) =~= Set::<AU>::empty());
                            }
                            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                        }
                        true
                    },
                    BranchMetadataStepResult::Blocked => {
                        proof {
                            assert(self.state().cache == self.cache@);
                            assert(self.state().branch == self.branch@);
                            assert(self.state().free_aus =~= self.au_pool@);
                            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                        }
                        false
                    },
                }
            },
            RecoveryPhase::ReplayingJournal => {
                let outstanding_empty = self.outstanding_requests.is_empty();
                if !outstanding_empty {
                    return false;
                }
                proof {
                    assert(self.outstanding_requests@.is_empty());
                    assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                        assert_maps_equal!(
                            self.outstanding_requests@,
                            Map::<ID, OutstandingReqInfo>::empty(),
                            id => {
                                if self.outstanding_requests@.contains_key(id) {
                                    assert(!self.outstanding_requests@.is_empty());
                                    assert(false);
                                }
                            }
                        );
                    }
                    assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                        assert(self.outstanding_cache_reqs_match_model());
                        assert(self.state().outstanding_cache_reqs.dom()
                            == self.outstanding_requests@.dom());
                        assert_maps_equal!(
                            self.state().outstanding_cache_reqs,
                            Map::<ID, Address>::empty(),
                            id => {
                                if self.state().outstanding_cache_reqs.contains_key(id) {
                                    assert(self.state().outstanding_cache_reqs.dom().contains(id));
                                    assert(self.outstanding_requests@.dom().contains(id));
                                    assert(!self.outstanding_requests@.contains_key(id));
                                    assert(false);
                                }
                            }
                        );
                    }
                }

                let branch_seq_end = self.branch.exec_seq_end();
                let journal_seq_end = self.journal.exec_seq_end();
                if branch_seq_end != journal_seq_end {
                    if branch_seq_end > journal_seq_end {
                        api.log("unified-cache journal replay seq mismatch");
                        return false;
                    }
                    let refill_progress = self.record_branch_refill_for_replay(api);
                    if refill_progress {
                        return true;
                    }
                    return self.record_journal_replay_append(api);
                }

                let ghost pre_state = self.model@.value();
                let ghost end_lsn = pre_state.state.branch.seq_end();
                let ghost post_state = UnifiedCacheProgramModel{
                    state: UnifiedCacheSystem::State{
                        recovery_state: RecoveryState::RecoveryComplete,
                        ..pre_state.state
                    }
                };
                let tracked mut model = KVStoreTokenized::model::arbitrary();
                proof {
                    tracked_swap(self.model.borrow_mut(), &mut model);
                }
                proof {
                    assert(pre_state.state.recovery_state is MetadataLoadComplete);
                    assert(pre_state.state.branch == self.branch@);
                    assert(pre_state.state.journal.journal == self.journal@);
                    assert(end_lsn == branch_seq_end as nat) by {
                        assert(self.branch@.seq_end == branch_seq_end as nat);
                    }
                    self.journal.view_seq_end_ensures();
                    assert(self.journal@.seq_end() == journal_seq_end as nat);
                    assert(end_lsn == self.journal@.seq_end()) by {
                        assert(branch_seq_end == journal_seq_end);
                    }

                    let journal_lbl = AtomicJournalState::Label::QueryEndLsn{end_lsn};
                    assert(CachedJournal::State::query_end_lsn(
                        pre_state.state.journal.journal,
                        pre_state.state.journal.journal,
                        CachedJournal::Label::QueryEndLsn{end_lsn},
                    )) by {
                    }
                    assert(CachedJournal::State::next_by(
                        pre_state.state.journal.journal,
                        pre_state.state.journal.journal,
                        CachedJournal::Label::QueryEndLsn{end_lsn},
                        CachedJournal::Step::query_end_lsn(),
                    )) by {
                        reveal(CachedJournal::State::next_by);
                    }
                    assert(CachedJournal::State::next(
                        pre_state.state.journal.journal,
                        pre_state.state.journal.journal,
                        CachedJournal::Label::QueryEndLsn{end_lsn},
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
                    assert(UnifiedCacheSystem::State::recovery_complete(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                    )) by {
                    }
                    assert(UnifiedCacheSystem::State::next_by(
                        pre_state.state,
                        post_state.state,
                        UnifiedCacheSystem::Label::Internal,
                        UnifiedCacheSystem::Step::recovery_complete(),
                    )) by {
                        reveal(UnifiedCacheSystem::State::next_by);
                    }
                    UnifiedCacheProgramModel::lift_internal_step(pre_state, post_state);
                }

                let tracked _internal_token = self.instance.borrow().internal(
                    KVStoreTokenized::Label::InternalOp{},
                    post_state,
                    &mut model,
                );
                self.model = Tracked(model);
                self.recovery_phase = RecoveryPhase::ReadyForUserOperation;
                proof {
                    assert(self.state().cache == self.cache@);
                    assert(self.state().branch == self.branch@);
                    assert(self.state().free_aus =~= self.au_pool@);
                    assert(self.state().journal.journal == self.journal@);
                    assert(self.state().journal.mini_allocator
                        == self.journal.journal_alloc.i()) by {
                        assert(post_state.state.journal == pre_state.state.journal);
                    }
                    assert(self.state().journal.mini_allocator == MiniAllocator::empty()) by {
                        assert(post_state.state.journal == pre_state.state.journal);
                    }
                    self.journal.journal_alloc.empty_view_implies_no_allocators();
                    assert(MiniAllocatorImpl::allocators_unique(
                        self.journal.journal_alloc.allocators@,
                    ));
                    assert(self.au_pool@.disjoint(
                        MiniAllocatorImpl::allocators_au_set(
                            self.journal.journal_alloc.allocators@,
                        ),
                    )) by {
                        assert(MiniAllocatorImpl::allocators_au_set(
                            self.journal.journal_alloc.allocators@,
                        ) =~= Set::<AU>::empty());
                    }
	                    assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
	                    assert(self.outstanding_requests_wf());
	                    assert(self.outstanding_cache_reqs_match_model());
	                    assert(self.outstanding_requests_single_flight());
	                    if !(self.recovery_phase is ReadyForUserOperation) {
	                        assert(!(old(self).recovery_phase is ReadyForUserOperation));
	                        assert(old(self).recovery_sync_empty()) by {
	                            reveal(Implementation::inv_api);
	                            reveal(Implementation::inv);
	                        }
	                    }
	                    assert(self.state().journal.persistent_seq_end
	                        == self.persistent_journal_seq_end as nat) by {
	                        assert(post_state.state.journal.persistent_seq_end
	                            == pre_state.state.journal.persistent_seq_end);
	                        assert(old(self).state().journal.persistent_seq_end
	                            == old(self).persistent_journal_seq_end as nat);
	                    }
	                    Self::sync_wf_preserved_without_sync_change(old(self), self);
	                    assert(self.inv_api(api));
	                }
                api.log("unified-cache recovery complete");
                true
            },
            RecoveryPhase::ReadyForUserOperation => {
                false
            },
        }
    }

    fn handle_disk_response(
        &mut self,
        rec: DiskResponseRecord<UnifiedCacheProgramModel>,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            rec.token@.instance_id() == old(self).instance_id(),
            rec.token@.multiset() == multiset_map_singleton(rec.id, rec.disk_response@),
            rec.disk_response is ReadResp ==> rec.disk_response->data.len() == PAGE_SIZE_BYTES,
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        let DiskResponseRecord{id, disk_response, token} = rec;
        let ghost response = disk_response@;
        let ghost pre_outstanding = self.outstanding_requests@;
        let expected_response = self.outstanding_requests.contains_key(&id);
        let ready_for_response = match self.recovery_phase {
            RecoveryPhase::ReadyForUserOperation => true,
            _ => false,
        };
        if expected_response && ready_for_response {
            proof {
                reveal(Implementation::inv_api);
                reveal(Implementation::inv);
                assert(self.state().journal.journal == self.journal@);
                assert(!(self.state().recovery_state is Begin));
                assert(!(self.state().recovery_state is AwaitingSuperblock));
            }
            let ghost _response_journal_disk = self.unified_system_inv_journal_pages_parsable();
        }

        let req_info = self.outstanding_requests.remove(&id);
        match req_info {
            None => {
                api.log("unified-cache unexpected disk response");
            },
            Some(OutstandingReqInfo::CacheRead{addr, load_handle, purpose}) => {
                match disk_response {
                    IDiskResponse::ReadResp{data} => {
                        let mut load_handle = load_handle;
                        load_handle.rec = data;

                        proof {
                            assert(load_handle.rec.len() == PAGE_SIZE_BYTES);
                            assert(pre_outstanding.contains_key(id));
                            assert(old(self).outstanding_requests_wf());
                            assert(old(self).cache.entry_fetched(&addr));
                            assert(old(self).cache.valid_load_handle(&addr, load_handle));
                        }

                        let ghost pre_state = self.model@.value();
                        let ghost pre_cache_reqs = pre_state.state.outstanding_cache_reqs;
                        self.cache.load_release(&addr, load_handle);

                        let ghost resp_map = map![id => response];
                        let ghost disk_request_tuples = Multiset::empty();
                        let ghost disk_response_tuples = multiset_map_singleton(id, response);
                        let ghost finished_cache_reqs =
                            pre_state.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
                        let ghost cache_resps = Map::new(
                            |a| finished_cache_reqs.contains_key(a),
                            |a| resp_map[finished_cache_reqs[a]],
                        );
                        let ghost post_state = UnifiedCacheProgramModel{
                            state: UnifiedCacheSystem::State{
                                cache: self.cache@,
                                outstanding_cache_reqs:
                                    pre_state.state.outstanding_cache_reqs.remove_keys(resp_map.dom()),
                                ..pre_state.state
                            }
                        };

                        let tracked mut model = KVStoreTokenized::model::arbitrary();
                        proof {
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }

                        proof {
                            assert(pre_state.state.outstanding_cache_reqs == map![id => addr@]) by {
                                assert(pre_state.state.outstanding_cache_reqs.contains_key(id));
                                assert(pre_state.state.outstanding_cache_reqs[id] == addr@);
                                assert_maps_equal!(pre_state.state.outstanding_cache_reqs, map![id => addr@], k => {
                                    if k == id {
                                    } else {
                                        if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                                            assert(old(self).outstanding_requests@.contains_key(k));
                                            assert(old(self).outstanding_requests@.contains_key(id));
                                            assert(old(self).outstanding_requests_single_flight());
                                            assert(k == id);
                                            assert(false);
                                        }
                                    }
                                });
                            }
                            multiset_map_singleton_ensures(id, response);
                            assert(multiset_to_map(disk_response_tuples) == resp_map);
                            Self::cache_resps_singleton(pre_cache_reqs, id, addr@, response);
                            assert(cache_resps == map![addr@ => response]);
                            assert(UnifiedCacheSystem::State::cache_io_end(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                resp_map,
                                self.cache@,
                                disk_request_tuples,
                                disk_response_tuples,
                            )) by {
                            }
                            assert(UnifiedCacheSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                            )) by {
                                reveal(UnifiedCacheSystem::State::next_by);
                            }
                            let info = ProgramDiskInfo{
                                reqs: disk_request_tuples,
                                resps: disk_response_tuples,
                            };
                            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                                pre_state.state,
                                UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                                info,
                            ));
                            UnifiedCacheProgramModel::lift_disk_step(pre_state, post_state, info);
                            assert(post_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                                assert(pre_state.state.outstanding_cache_reqs == map![id => addr@]);
                                assert(resp_map.dom() == set![id]);
                                assert_maps_equal!(
                                    post_state.state.outstanding_cache_reqs,
                                    Map::<ID, Address>::empty(),
                                    k => {
                                        if post_state.state.outstanding_cache_reqs.contains_key(k) {
                                            assert(!resp_map.dom().contains(k));
                                            assert(pre_state.state.outstanding_cache_reqs.contains_key(k));
                                            assert(k == id);
                                            assert(false);
                                        }
                                    }
                                );
                            }
                        }

                        let tracked _disk_req_token = self.instance.borrow().disk_transitions(
                            KVStoreTokenized::Label::DiskOp{
                                disk_request_tuples,
                                disk_response_tuples,
                            },
                            post_state,
                            &mut model,
                            token.get(),
                        );
                        self.model = Tracked(model);

                        proof {
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                        }
                    },
                    IDiskResponse::WriteResp{} => {
                        self.outstanding_requests.insert(id, OutstandingReqInfo::CacheRead{
                            addr,
                            load_handle,
                            purpose,
                        });
                        api.log("unified-cache read got write response");
                    },
                }
            },
            Some(OutstandingReqInfo::CacheWrite{addr, write_handle}) => {
                match disk_response {
                    IDiskResponse::WriteResp{} => {
                        proof {
                            assert(pre_outstanding.contains_key(id));
                            assert(old(self).outstanding_requests_wf());
                            assert(old(self).cache.entry_fetched(&addr));
                            assert(old(self).cache.valid_writeback_handle(&addr, write_handle));
                        }

                        let ghost pre_state = self.model@.value();
                        let ghost pre_cache_reqs = pre_state.state.outstanding_cache_reqs;
                        self.cache.complete_writeback(&addr, write_handle);

                        let ghost resp_map = map![id => response];
                        let ghost disk_request_tuples = Multiset::empty();
                        let ghost disk_response_tuples = multiset_map_singleton(id, response);
                        let ghost finished_cache_reqs =
                            pre_state.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
                        let ghost cache_resps = Map::new(
                            |a| finished_cache_reqs.contains_key(a),
                            |a| resp_map[finished_cache_reqs[a]],
                        );
                        let ghost post_state = UnifiedCacheProgramModel{
                            state: UnifiedCacheSystem::State{
                                cache: self.cache@,
                                outstanding_cache_reqs:
                                    pre_state.state.outstanding_cache_reqs.remove_keys(resp_map.dom()),
                                ..pre_state.state
                            }
                        };

                        let tracked mut model = KVStoreTokenized::model::arbitrary();
                        proof {
                            tracked_swap(self.model.borrow_mut(), &mut model);
                        }

                        proof {
                            assert(pre_state.state.outstanding_cache_reqs == map![id => addr@]) by {
                                assert(pre_state.state.outstanding_cache_reqs.contains_key(id));
                                assert(pre_state.state.outstanding_cache_reqs[id] == addr@);
                                assert_maps_equal!(pre_state.state.outstanding_cache_reqs, map![id => addr@], k => {
                                    if k == id {
                                    } else {
                                        if pre_state.state.outstanding_cache_reqs.contains_key(k) {
                                            assert(old(self).outstanding_requests@.contains_key(k));
                                            assert(old(self).outstanding_requests@.contains_key(id));
                                            assert(old(self).outstanding_requests_single_flight());
                                            assert(k == id);
                                            assert(false);
                                        }
                                    }
                                });
                            }
                            multiset_map_singleton_ensures(id, response);
                            assert(multiset_to_map(disk_response_tuples) == resp_map);
                            Self::cache_resps_singleton(pre_cache_reqs, id, addr@, response);
                            assert(cache_resps == map![addr@ => response]);
                            assert(UnifiedCacheSystem::State::cache_io_end(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                resp_map,
                                self.cache@,
                                disk_request_tuples,
                                disk_response_tuples,
                            )) by {
                            }
                            assert(UnifiedCacheSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                            )) by {
                                reveal(UnifiedCacheSystem::State::next_by);
                            }
                            let info = ProgramDiskInfo{
                                reqs: disk_request_tuples,
                                resps: disk_response_tuples,
                            };
                            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                                pre_state.state,
                                UnifiedCacheSystem::Step::cache_io_end(
                                    resp_map,
                                    self.cache@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                                info,
                            ));
                            UnifiedCacheProgramModel::lift_disk_step(pre_state, post_state, info);
                            assert(post_state.state.outstanding_cache_reqs == Map::<ID, Address>::empty()) by {
                                assert(pre_state.state.outstanding_cache_reqs == map![id => addr@]);
                                assert(resp_map.dom() == set![id]);
                                assert_maps_equal!(
                                    post_state.state.outstanding_cache_reqs,
                                    Map::<ID, Address>::empty(),
                                    k => {
                                        if post_state.state.outstanding_cache_reqs.contains_key(k) {
                                            assert(!resp_map.dom().contains(k));
                                            assert(pre_state.state.outstanding_cache_reqs.contains_key(k));
                                            assert(k == id);
                                            assert(false);
                                        }
                                    }
                                );
                            }
                        }

                        let tracked _disk_req_token = self.instance.borrow().disk_transitions(
                            KVStoreTokenized::Label::DiskOp{
                                disk_request_tuples,
                                disk_response_tuples,
                            },
                            post_state,
                            &mut model,
                            token.get(),
                        );
                        self.model = Tracked(model);

                        proof {
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                        }
                    },
                    IDiskResponse::ReadResp{..} => {
                        self.outstanding_requests.insert(id, OutstandingReqInfo::CacheWrite{
                            addr,
                            write_handle,
                        });
                        api.log("unified-cache write got read response");
                    },
                }
            },
            Some(OutstandingReqInfo::SuperblockWrite) => {
                match disk_response {
                    IDiskResponse::ReadResp{..} => {
                        self.outstanding_requests.insert(id, OutstandingReqInfo::SuperblockWrite);
                        api.log("unified-cache superblock write got read response");
                    },
                    IDiskResponse::WriteResp{} => {
                        let mut in_flight = None;
                        core::mem::swap(&mut self.in_flight_sync, &mut in_flight);
                        let in_flight = match in_flight {
                            Some(in_flight) => in_flight,
                            None => {
                                proof {
                                    assert(old(self).in_flight_sync is Some) by {
                                        if old(self).in_flight_sync is None {
                                            assert(old(self).state().outstanding_cache_reqs.dom()
                                                == old(self).outstanding_requests@.dom());
                                            assert(!old(self).state().outstanding_cache_reqs.contains_key(id));
                                            assert(old(self).outstanding_requests@.contains_key(id));
                                            assert(false);
                                        }
                                    }
                                    assert(false);
                                }
                                unreached()
                            },
                        };
                        let boundary_lsn = in_flight.image.payload.journal.snapshot.boundary_lsn;
                        let persistent_seq_end = in_flight.image.payload.journal.seq_end;
                        let journal_marshalled_seq_end = self.journal.exec_marshaled_seq_end();
                        let ghost abstract_image = in_flight.image@@;
                        let ghost pre_state = self.model@.value();
                        let ghost pre_journal = self.journal@;
                        let ghost pre_branch = self.branch@;
                        let ghost discarded_aus = {
                            let old_index = pre_journal.status.unwrap().lsn_au_index;
                            let kept = crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to(
                                old_index,
                                boundary_lsn as nat,
                            );
                            old_index.values() - kept.values()
                        };
                        let ghost discarded_aus_seq = in_flight.discarded_aus@;

                        proof {
                            assert(in_flight.req_id == id) by {
                                assert(old(self).outstanding_requests_single_flight());
                                assert(old(self).outstanding_requests@.contains_key(id));
                                assert(old(self).outstanding_requests@.contains_key(in_flight.req_id));
                            }
                            assert(abstract_image.wf());
                            match in_flight.flavor {
                                SyncFlavor::JournalOnly => {
                                    assert(boundary_lsn as nat == self.journal.seq_start());
                                    self.journal.seq_start_le_marshalled_end();
                                    self.journal.discard_at_seq_start_deallocates_nothing();
                                    assert(discarded_aus =~= Set::<AU>::empty());
                                    assert(discarded_aus_seq.len() == 0);
                                },
                                SyncFlavor::BranchAndEmptyJournal => {
                                    assert(boundary_lsn as nat == self.journal.seq_end());
                                    assert(boundary_lsn as nat == self.journal.marshalled_seq_end());
                                    self.journal.discard_at_seq_end_deallocates_all();
                                    assert(discarded_aus =~=
                                        pre_journal.status.unwrap().lsn_au_index.values());
                                    assert(iau_vec_set(discarded_aus_seq) =~= discarded_aus);
                                },
                            }
                            assert((boundary_lsn as nat) <= self.journal.marshalled_seq_end());
                            assert(boundary_lsn <= journal_marshalled_seq_end);
                            assert(pre_state.state.journal.journal == self.journal@);
                            assert(pre_state.state.journal.in_flight == Some(AtomicJournalImage{
                                snapshot: abstract_image.journal_snapshot,
                                seq_end: abstract_image.journal_seq_end,
                            }));
                            assert(pre_state.state.journal.prepared);
                            assert(pre_state.state.branch.in_flight == Some(
                                crate::implementation::AtomicBranchState_v::AtomicBranchImage{
                                    sealed_roots: abstract_image.branch_roots,
                                    seq_end: abstract_image.branch_seq_end,
                                },
                            ));
                            assert(pre_state.state.branch.prepared);
                            assert(self.branch@ == pre_state.state.branch);
                            assert(self.branch.prepared_i());
                            self.branch.prepared_i_implies_commit_prepared();
                        }

                        proof {
                            reveal(Implementation::inv_api);
                            reveal(Implementation::inv);
                            assert(old(self).recovery_phase is ReadyForUserOperation);
                            assert(self.journal == old(self).journal);
                            assert(old(self).journal.wf());
                            assert(self.journal.wf());
                        }
                        let ghost journal_before_discard = self.journal@;
                        proof {
                            assert(journal_before_discard == pre_journal);
                        }
                        self.journal.discard_old(boundary_lsn, self.disk_au_count);
                        let allocator_discarded_aus = match in_flight.flavor {
                            SyncFlavor::JournalOnly => Vec::<IAU>::new(),
                            SyncFlavor::BranchAndEmptyJournal => {
                                self.journal.prune_allocated_aus(
                                    self.disk_au_count,
                                )
                            },
                        };
                        let ghost allocator_discarded_aus_seq = allocator_discarded_aus@;
                        let complete_result = self.branch.commit_complete();
                        match complete_result {
                            Ok(()) => {},
                            Err(_) => {
                                proof { assert(false); }
                                unreached()
                            },
                        }
                        proof {
                            assert forall |i: int| 0 <= i < discarded_aus_seq.len()
                                implies 0 < #[trigger] (discarded_aus_seq[i] as nat)
                                    < (self.disk_au_count as nat) by {
                            }
                            assert(self.au_pool@.disjoint(iau_vec_set(discarded_aus_seq))) by {
                                assert(pre_state.state.free_aus =~= self.au_pool@);
                                assert(pre_state.state.client_ready());
                                assert(pre_state.state.free_aus.disjoint(
                                    pre_state.state.journal.loaded_index_aus(),
                                ));
                                assert(iau_vec_set(discarded_aus_seq)
                                    <= pre_state.state.journal.loaded_index_aus());
                            }
                        }
                        self.au_pool.free_aus(
                            self.disk_au_count,
                            &in_flight.discarded_aus,
                        );

                        let ghost new_atomic_journal = AtomicJournalState::State{
                            journal: self.journal@,
                            persistent_seq_end: abstract_image.journal_seq_end,
                            mini_allocator: self.journal.journal_alloc.i(),
                            in_flight: None,
                            prepared: false,
                        };
                        let ghost post_state = UnifiedCacheProgramModel{
                            state: UnifiedCacheSystem::State{
                                journal: new_atomic_journal,
                                branch: self.branch@,
                                free_aus: self.au_pool@,
                                persistent_image: Some(abstract_image),
                                sync_phase: AtomicSyncPhase::None,
                                ..pre_state.state
                            }
                        };
                        let ghost disk_request_tuples = Multiset::empty();
                        let ghost disk_response_tuples = multiset_map_singleton(id, response);
                        let tracked mut model = KVStoreTokenized::model::arbitrary();

                        proof {
                            tracked_swap(self.model.borrow_mut(), &mut model);
                            let old_index = pre_journal.status.unwrap().lsn_au_index;
                            let kept = crate::allocation_layer::AllocationJournal_v::lsn_au_index_discard_up_to(
                                old_index,
                                boundary_lsn as nat,
                            );
                            assert(journal_before_discard == pre_journal);
                            assert(old_index.values() - kept.values() == discarded_aus);
                            assert(CachedJournal::State::next(
                                pre_journal,
                                self.journal@,
                                CachedJournal::Label::DiscardOld{
                                    start_lsn: boundary_lsn as nat,
                                    require_end: pre_journal.seq_end(),
                                    deallocs: discarded_aus,
                                },
                            ));
                            assert(AtomicJournalState::State::commit_complete(
                                pre_state.state.journal,
                                new_atomic_journal,
                                AtomicJournalState::Label::CommitComplete{
                                    require_end: pre_state.state.journal.journal.seq_end(),
                                    discarded_aus,
                                },
                                self.journal@,
                            )) by {
                                assert(pre_state.state.journal.journal == pre_journal);
                                let allocator = pre_state.state.journal.mini_allocator;
                                assert(self.journal.journal_alloc.i()
                                    == allocator.prune(discarded_aus)) by {
                                    match in_flight.flavor {
                                        SyncFlavor::JournalOnly => {
                                            assert(discarded_aus =~= Set::<AU>::empty());
                                            assert(self.journal.journal_alloc.i() == allocator);
                                            assert(allocator.allocs.remove_keys(discarded_aus)
                                                == allocator.allocs) by {
                                                assert_maps_equal!(
                                                    allocator.allocs.remove_keys(discarded_aus),
                                                    allocator.allocs,
                                                    au => {}
                                                );
                                            }
                                            assert(allocator.prune(discarded_aus) == allocator) by {
                                                assert(allocator.curr is Some ==>
                                                    !discarded_aus.contains(allocator.curr.unwrap()));
                                            }
                                        },
                                        SyncFlavor::BranchAndEmptyJournal => {
                                            let removed = iau_vec_set(allocator_discarded_aus_seq);
                                            assert(removed =~= allocator.allocated_aus());
                                            assert(allocator.allocated_aus() <= discarded_aus) by {
                                                assert(old(self).journal.allocator_index_aligned());
                                                assert(discarded_aus =~=
                                                    pre_journal.status.unwrap().lsn_au_index.values());
                                            }
                                            assert forall |au: AU| {
                                                &&& #[trigger] discarded_aus.contains(au)
                                                &&& allocator.allocs.contains_key(au)
                                            } implies removed.contains(au) by {
                                                assert(pre_journal.status.unwrap().lsn_au_index.values().contains(au));
                                                assert(allocator.allocated_aus().contains(au));
                                            }
                                            assert(allocator.allocs.remove_keys(discarded_aus)
                                                == allocator.allocs.remove_keys(removed)) by {
                                                assert_maps_equal!(
                                                    allocator.allocs.remove_keys(discarded_aus),
                                                    allocator.allocs.remove_keys(removed),
                                                    au => {}
                                                );
                                            }
                                            assert(allocator.prune(discarded_aus)
                                                == allocator.prune(removed)) by {
                                                assert(allocator
                                                    == old(self).journal.journal_alloc.i());
                                                reveal(Implementation::inv_api);
                                                reveal(Implementation::inv);
                                                assert(old(self).journal.wf());
                                                old(self).journal.wf_implies_basic_wf();
                                                assert(old(self).journal.basic_wf());
                                                assert(old(self).journal.journal_alloc.wf());
                                                if allocator.curr is Some {
                                                    let curr = allocator.curr.unwrap();
                                                    assert(allocator.allocs.contains_key(curr));
                                                    if discarded_aus.contains(curr) {
                                                        assert(removed.contains(curr));
                                                    }
                                                    if removed.contains(curr) {
                                                        assert(allocator.allocated_aus().contains(curr));
                                                        assert(discarded_aus.contains(curr));
                                                    }
                                                }
                                            }
                                        },
                                    }
                                }
                            }
                            assert(AtomicJournalState::State::next_by(
                                pre_state.state.journal,
                                new_atomic_journal,
                                AtomicJournalState::Label::CommitComplete{
                                    require_end: pre_state.state.journal.journal.seq_end(),
                                    discarded_aus,
                                },
                                AtomicJournalState::Step::commit_complete(self.journal@),
                            )) by {
                                reveal(AtomicJournalState::State::next_by);
                            }
                            assert(AtomicJournalState::State::next(
                                pre_state.state.journal,
                                new_atomic_journal,
                                AtomicJournalState::Label::CommitComplete{
                                    require_end: pre_state.state.journal.journal.seq_end(),
                                    discarded_aus,
                                },
                            )) by {
                                reveal(AtomicJournalState::State::next);
                            }
                            assert(expected_response);
                            assert(ready_for_response);
                            assert(pre_state.state.journal.wf());
                            AtomicJournalState::State::commit_complete_effect(
                                pre_state.state.journal,
                                new_atomic_journal,
                                AtomicJournalState::Label::CommitComplete{
                                    require_end: pre_state.state.journal.journal.seq_end(),
                                    discarded_aus,
                                },
                            );
                            assert(AtomicBranchState::State::next(
                                pre_state.state.branch,
                                self.branch@,
                                AtomicBranchState::Label::CommitComplete,
                            ));
                            multiset_map_singleton_ensures(id, response);
                            assert(response == DiskResponse::WriteResp{});
                            assert(disk_response_tuples
                                == Multiset::singleton((id, response))) by {
                                assert(disk_response_tuples
                                    == Multiset::empty().insert((id, response)));
                            }
                            assert(disk_response_tuples == Multiset::singleton((
                                in_flight.req_id,
                                DiskResponse::WriteResp{},
                            )));
                            assert(self.au_pool@ =~=
                                pre_state.state.free_aus + discarded_aus) by {
                                assert(iau_vec_set(discarded_aus_seq) =~= discarded_aus);
                            }
                            assert(UnifiedCacheSystem::State::execute_sync_end(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                discarded_aus,
                                new_atomic_journal,
                                self.branch@,
                                disk_request_tuples,
                                disk_response_tuples,
                            )) by {
                            }
                            assert(UnifiedCacheSystem::State::next_by(
                                pre_state.state,
                                post_state.state,
                                UnifiedCacheSystem::Label::Disk,
                                UnifiedCacheSystem::Step::execute_sync_end(
                                    discarded_aus,
                                    new_atomic_journal,
                                    self.branch@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                            )) by {
                                reveal(UnifiedCacheSystem::State::next_by);
                            }
                            let info = ProgramDiskInfo{
                                reqs: disk_request_tuples,
                                resps: disk_response_tuples,
                            };
                            assert(UnifiedCacheProgramModel::disk_step_matches_info(
                                pre_state.state,
                                UnifiedCacheSystem::Step::execute_sync_end(
                                    discarded_aus,
                                    new_atomic_journal,
                                    self.branch@,
                                    disk_request_tuples,
                                    disk_response_tuples,
                                ),
                                info,
                            ));
                            UnifiedCacheProgramModel::lift_disk_step(
                                pre_state,
                                post_state,
                                info,
                            );
                        }

                        let tracked _disk_req_token = self.instance.borrow().disk_transitions(
                            KVStoreTokenized::Label::DiskOp{
                                disk_request_tuples,
                                disk_response_tuples,
                            },
                            post_state,
                            &mut model,
                            token.get(),
                        );
                        self.model = Tracked(model);
                        self.persistent_journal_seq_end = persistent_seq_end;

                        proof {
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                            assert(self.state().outstanding_cache_reqs == Map::<ID, Address>::empty());
                            assert(self.outstanding_requests_wf());
                            assert(self.outstanding_cache_reqs_match_model());
                            assert(self.outstanding_requests_single_flight());
                            assert(self.state().journal.journal == self.journal@);
                            self.journal.wf_implies_basic_wf();
                            self.journal.view_ensures();
                            assert(self.journal.basic_wf());
                            assert(self.journal.index_ready());
                            assert(self.journal@.status is Some);
                            assert(self.state().journal.ready());
                            assert(self.state().journal_metadata_loaded());
                            assert(self.state().branch == self.branch@);
                            assert(self.state().free_aus =~= self.au_pool@);
                            assert(self.state().journal.persistent_seq_end
                                == self.persistent_journal_seq_end as nat);
                            assert(self.persistent_component_alignment()) by {
                                assert(self.branch.persistent_seq_end as nat
                                    == abstract_image.branch_seq_end);
                                assert(abstract_image.branch_seq_end
                                    == abstract_image.journal_snapshot.boundary_lsn);
                                assert(self.journal.seq_start()
                                    == boundary_lsn as nat);
                            }
                            assert(self.sync_wf()) by {
                                reveal(Implementation::sync_wf);
                                assert(self.in_flight_sync is None);
                                assert(self.state().sync_phase is None);
                                assert forall |i: int|
                                    0 <= i < self.sync_requests.superblocking_reqs@.len()
                                    implies #[trigger] self.state().sync_req_map[
                                        self.sync_requests.superblocking_reqs@[i]
                                    ] <= self.state().journal.persistent_seq_end by {
                                    assert(old(self).state().sync_req_map[
                                        old(self).sync_requests.superblocking_reqs@[i]
                                    ] <= old(self).in_flight_sync.unwrap().image@@.journal_seq_end);
                                }
                            }
                            assert(self.journal.allocator_index_aligned()) by {
                                match in_flight.flavor {
                                    SyncFlavor::JournalOnly => {
                                        assert(self.journal.journal_alloc.i()
                                            == old(self).journal.journal_alloc.i());
                                        assert(old(self).journal.allocator_index_aligned());
                                        assert(pre_journal.status.unwrap().lsn_au_index.values()
                                            - self.journal@.status.unwrap().lsn_au_index.values()
                                            =~= Set::<AU>::empty());
                                        assert(pre_journal.status.unwrap().lsn_au_index.values()
                                            <= self.journal@.status.unwrap().lsn_au_index.values()) by {
                                            assert forall |au: AU| #[trigger]
                                                pre_journal.status.unwrap().lsn_au_index.values().contains(au)
                                                implies self.journal@.status.unwrap().lsn_au_index.values().contains(au) by {
                                                if !self.journal@.status.unwrap().lsn_au_index.values().contains(au) {
                                                    assert((pre_journal.status.unwrap().lsn_au_index.values()
                                                        - self.journal@.status.unwrap().lsn_au_index.values()).contains(au));
                                                    assert(false);
                                                }
                                            }
                                        }
                                    },
                                    SyncFlavor::BranchAndEmptyJournal => {
                                        assert(self.journal.journal_alloc.i().allocated_aus()
                                            =~= Set::<AU>::empty());
                                    },
                                }
                            }
                            assert(self.au_pool@.disjoint(
                                MiniAllocatorImpl::allocators_au_set(
                                    self.branch.mini_allocator.allocators@,
                                ),
                            )) by {
                                assert(self.branch.mini_allocator
                                    == old(self).branch.mini_allocator);
                                assert(self.au_pool@ =~=
                                    old(self).au_pool@ + discarded_aus);
                                assert(discarded_aus
                                    <= pre_state.state.journal.loaded_index_aus());
                                assert(pre_state.state.journal.loaded_index_aus().disjoint(
                                    pre_state.state.branch.mini_allocator.all_aus(),
                                ));
                                assert(pre_state.state.branch.mini_allocator
                                    == old(self).branch.mini_allocator.i());
                                assert(MiniAllocatorImpl::allocators_au_set(
                                    old(self).branch.mini_allocator.allocators@,
                                ) =~= old(self).branch.mini_allocator.i().all_aus());
                            }
                            reveal(Implementation::inv_api);
                            reveal(Implementation::inv);
                            assert(self.inv_api(api));
                        }
                        api.log("unified-cache sync committed");
                    },
                }
            },
        }


        match self.recovery_phase {
            RecoveryPhase::ReadyForUserOperation => {
                if self.outstanding_requests.is_empty() {
                    proof {
                        assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                            assert_maps_equal!(
                                self.outstanding_requests@,
                                Map::<ID, OutstandingReqInfo>::empty(),
                                k => {
                                    if self.outstanding_requests@.contains_key(k) {
                                        assert(!self.outstanding_requests@.is_empty());
                                        assert(false);
                                    }
                                }
                            );
                        }
                    }
                    let _ = self.poll_sync_preparation(api);
                }
            },
            _ => {},
        }
    }

    fn handle_user_request(
        &mut self,
        req: Request,
        req_shard: Tracked<RequestShard>,
        api: &mut ClientAPI<UnifiedCacheProgramModel>,
    )
        requires
            old(self).inv_api(old(api)),
            old(self).recovery_phase is ReadyForUserOperation,
            req_shard@.instance_id() == old(self).instance_id(),
            req_shard@.element() == req,
            old(self).outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty(),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        match req.input {
            Input::NoopInput => {
                self.record_execute_noop(req, req_shard, api);
            },
            Input::PutInput{key, value} => {
                self.record_execute_put(req, req_shard, key, value, api);
            },
            Input::QueryInput{key} => {
                self.record_execute_query(req, req_shard, key, api);
            },
            Input::SyncInput => {
                self.record_accept_sync_request(req, req_shard, api);
            },
            Input::SimulateCrash => {
                api.log("simulate crash skeleton");
            },
        }
    }

    fn do_background_work(&mut self, api: &mut ClientAPI<UnifiedCacheProgramModel>) -> (progress: bool)
        requires
            old(self).inv_api(old(api)),
        ensures
            self.inv_api(api),
            self.recovery_phase == old(self).recovery_phase,
    {
        match self.recovery_phase {
            RecoveryPhase::ReadyForUserOperation => {
                let outstanding_empty = self.outstanding_requests.is_empty();
                if !outstanding_empty {
                    proof {
                        assert(self.inv());
                    }
                    return false;
                }
                proof {
                    assert(self.outstanding_requests@.is_empty());
                    assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                        assert_maps_equal!(
                            self.outstanding_requests@,
                            Map::<ID, OutstandingReqInfo>::empty(),
                            k => {
                                if self.outstanding_requests@.contains_key(k) {
                                    assert(!self.outstanding_requests@.is_empty());
                                }
                            }
                        );
                    }
                }

                if self.sync_requests.superblocking_reqs.len() > 0 {
                    proof {
                        assert(self.sync_requests.superblocking_reqs@.len() > 0);
                        assert(self.in_flight_sync is None) by {
                            if self.in_flight_sync is Some {
                                let in_flight = self.in_flight_sync.unwrap();
                                assert(self.outstanding_requests@.contains_key(in_flight.req_id));
                                assert(false);
                            }
                        }
                    }
                    return self.record_deliver_completed_sync_reply(api);
                }

                let sync_progress = self.poll_sync_preparation(api);
                if sync_progress {
                    return true;
                }
                proof {
                    assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty());
                }

                if self.pending_branch_sync.is_some() {
                    proof {
                        assert(self.inv_api(api));
                    }
                    return false;
                }

                if self.journal.free_aus_below_threshold() {
                    return self.record_journal_refill_for_ready(api);
                }
                if self.branch.mini_allocator.free_aus_below_threshold() {
                    return self.record_branch_refill_for_ready(api);
                }
                let branch_maintenance_progress = self.record_branch_maintenance_step(api);
                if branch_maintenance_progress {
                    return true;
                }

                let marshall_progress = self.record_journal_marshall_step(api);
                if marshall_progress {
                    return true;
                }

                self.record_journal_writeback_for_target(api)
            },
            _ => {
                false
            },
        }
    }
}

impl KVStoreTrait for Implementation {
    type ProgramModel = UnifiedCacheProgramModel;
    type Proof = UnifiedCacheRefinementProof;

    closed spec fn wf_init(self) -> bool
    {
        Implementation::wf_init(&self)
    }

    closed spec fn instance_id(self) -> InstanceId
    {
        Implementation::instance_id(&self)
    }

    fn configured_disk_geometry() -> (out: IDiskGeometry)
    {
        IDiskGeometry {
            physical_au_count: DEFAULT_PHYSICAL_AUS,
            pages_per_au: IMPLEMENTATION_PAGES_PER_AU,
        }
    }

    fn new(geometry: IDiskGeometry) -> (out: Self)
    {
        let cache = FracCacheImpl::new();
        let snapshot = IJournalSnapshot::new_empty(0);
        let disk_au_count = geometry.physical_au_count;
        let disk_page_count = geometry.pages_per_au;
        let bootstrap_au = bootstrap_alloc_au(disk_au_count);
        let journal = JournalImpl::new(snapshot, bootstrap_au);
        let branch = BranchStackImpl::awaiting_superblock(BRANCH_FREE_AU_THRESHOLD);
        let au_pool = AuPoolImpl::new(disk_au_count);

        let ghost free_aus = au_pool@;
        let ghost initial_state = UnifiedCacheSystem::State {
            recovery_state: RecoveryState::Begin,
            cache: cache@,
            outstanding_cache_reqs: Map::<ID, Address>::empty(),
            free_aus,
            journal: AtomicJournalState::State::empty(),
            branch: AtomicBranchState::State::empty(),
            persistent_image: None,
            sync_phase: AtomicSyncPhase::None,
            sync_req_map: Map::<SyncReqId, nat>::empty(),
        };

        proof {
            assert(free_aus.disjoint(UnifiedCacheSystem::State::reserved_aus())) by {
                assert(spec_superblock_addr().au == 0);
                assert(UnifiedCacheSystem::State::reserved_aus() =~= set![0]) by {
                }
                assert(!free_aus.contains(0));
            }
            assert(UnifiedCacheSystem::State::initialize(
                initial_state,
                cache.total_slots() as nat,
                free_aus,
            )) by {
                assert(initial_state.cache == Cache::State::empty(cache.total_slots() as nat));
            }
            assert(UnifiedCacheSystem::State::init_by(
                initial_state,
                UnifiedCacheSystem::Config::initialize(cache.total_slots() as nat, free_aus),
            )) by {
                reveal(UnifiedCacheSystem::State::init_by);
            }
            assert(UnifiedCacheSystem::State::init(initial_state)) by {
                reveal(UnifiedCacheSystem::State::init);
            }
        }

        let tracked (
            Tracked(instance),
            Tracked(model),
            Tracked(requests),
            Tracked(replies),
            Tracked(disk_requests),
            Tracked(disk_responses),
        ) = KVStoreTokenized::Instance::initialize(UnifiedCacheProgramModel{state: initial_state});

        Implementation {
            disk_au_count,
            disk_page_count,
            recovery_phase: RecoveryPhase::FetchingSuperblock,
            cache,
            journal,
            branch,
            au_pool,
            persistent_journal_seq_end: 0,
            sync_counter: 0,
            sync_requests: SyncRequestBuffer::new_empty(),
            pending_branch_sync: None,
            in_flight_sync: None,
            outstanding_requests: HashMapWithView::new(),
            pending_user_op: None,
            model: Tracked(model),
            instance: Tracked(instance),
        }
    }

    fn kvstore_mkfs(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        let layout = DiskLayout::new();
        let superblock = layout.exec_mkfs(self.disk_au_count, self.disk_page_count);
        api.format_storage(
            superblock,
        );
        api.log("unified-cache mkfs complete");
    }

    #[verifier::exec_allows_no_decreases_clause]
    fn kvstore_main(&mut self, mut api: ClientAPI<Self::ProgramModel>)
    {
        self.recover_begin(&mut api);

        let debug_print = true;
        loop
            invariant
                self.inv_api(&api),
                self.recovery_phase is FetchingSuperblock
                    ==> self.state().recovery_state is AwaitingSuperblock,
                self.recovery_phase is LoadingJournal
                    ==> self.state().recovery_state is SuperblockAvailable,
                self.recovery_phase is LoadingJournal
                    ==> self.state().journal.journal == self.journal@,
                self.recovery_phase is LoadingBranch
                    ==> self.state().recovery_state is SuperblockAvailable,
                self.recovery_phase is ReplayingJournal
                    ==> self.state().recovery_state is MetadataLoadComplete,
        {
            let mut progress = false;

            match self.recovery_phase {
                RecoveryPhase::LoadingJournal
                | RecoveryPhase::LoadingBranch
                | RecoveryPhase::ReplayingJournal
                | RecoveryPhase::ReadyForUserOperation => {
                    match api.receive_disk_response() {
                        None => {},
                        Some(rec) => {
                            progress = true;
                            self.handle_disk_response(rec, &mut api);
                        },
                    }
                },
                RecoveryPhase::FetchingSuperblock => {},
            }

            match self.recovery_phase {
                RecoveryPhase::FetchingSuperblock
                | RecoveryPhase::LoadingJournal
                | RecoveryPhase::LoadingBranch
                | RecoveryPhase::ReplayingJournal => {
                    progress = self.recover_step(&mut api) || progress;
                },
                RecoveryPhase::ReadyForUserOperation => {
                    let outstanding_empty = self.outstanding_requests.is_empty();
                    if outstanding_empty {
                        proof {
                            assert(self.outstanding_requests@.is_empty());
                            assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                                assert_maps_equal!(
                                    self.outstanding_requests@,
                                    Map::<ID, OutstandingReqInfo>::empty(),
                                    k => {
                                        if self.outstanding_requests@.contains_key(k) {
                                            assert(!self.outstanding_requests@.is_empty());
                                        }
                                    }
                                );
                            }
                        }
                        let pending_progress = self.continue_pending_user_op(&mut api);
                        progress = progress || pending_progress;
                        if self.pending_user_op.is_none() && self.outstanding_requests.is_empty() {
                            proof {
                                assert(self.outstanding_requests@.is_empty());
                                assert(self.outstanding_requests@ == Map::<ID, OutstandingReqInfo>::empty()) by {
                                    assert_maps_equal!(
                                        self.outstanding_requests@,
                                        Map::<ID, OutstandingReqInfo>::empty(),
                                        k => {
                                            if self.outstanding_requests@.contains_key(k) {
                                                assert(!self.outstanding_requests@.is_empty());
                                            }
                                        }
                                    );
                                }
                            }
                            match api.receive_request(debug_print) {
                                None => {},
                                Some(rec) => {
                                    progress = true;
                                    match rec.request.input {
                                        Input::SimulateCrash => {
                                            return;
                                        },
                                        _ => {
                                            self.handle_user_request(rec.request, rec.token, &mut api);
                                        },
                                    }
                                },
                            }
                        }
                    }

                    let bg_progress = self.do_background_work(&mut api);
                    progress = progress || bg_progress;
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
// Utility Proofs
//
// Keep small algebraic/map proof helpers out of the executable implementation
// flow above. These lemmas have no runtime role; they only discharge local
// proof obligations around singleton disk/cache request maps.
///////////////////////////////////////////////////////////////////////////////

impl Implementation {
    proof fn live_component_alignment_preserved(pre: &Self, post: &Self)
        requires
            pre.live_component_alignment(),
            post.branch@.seq_end() == pre.branch@.seq_end(),
            post.journal.seq_end() == pre.journal.seq_end(),
        ensures
            post.live_component_alignment(),
    {
        reveal(Implementation::live_component_alignment);
    }

    proof fn sync_wf_from_empty(&self)
        requires
            self.recovery_sync_empty(),
        ensures
            self.sync_wf(),
    {
        reveal(Implementation::sync_wf);
        reveal(Implementation::sync_requests_empty);
        reveal(Implementation::recovery_sync_empty);
        assert(self.sync_requests.ids_unique());
        assert(self.sync_requests.all_ids().to_set()
            =~= self.state().sync_req_map.dom()) by {
            assert(self.sync_requests.all_ids().to_set()
                =~= Set::<SyncReqId>::empty()) by {
                assert_sets_equal!(
                    self.sync_requests.all_ids().to_set(),
                    Set::<SyncReqId>::empty(),
                    id => {
                        if self.sync_requests.all_ids().to_set().contains(id) {
                            assert(false);
                        }
                    }
                );
            }
            assert(self.state().sync_req_map.dom()
                =~= Set::<SyncReqId>::empty()) by {
                assert_maps_equal!(
                    self.state().sync_req_map,
                    Map::<SyncReqId, nat>::empty(),
                    id => {}
                );
            }
        }
        assert forall |i: int| 0 <= i < self.sync_requests.journal_cleaning_reqs@.len()
            implies #[trigger] self.state().sync_req_map[
                self.sync_requests.journal_cleaning_reqs@[i]
            ] <= self.sync_requests.sync_target_lsn as nat by {
            assert(false);
        }
        assert forall |i: int| 0 <= i < self.sync_requests.buffered_reqs@.len()
            implies #[trigger] self.state().sync_req_map[
                self.sync_requests.buffered_reqs@[i]
            ] <= self.state().branch.seq_end() by {
            assert(false);
        }
        assert(self.in_flight_sync is None);
        assert(self.state().sync_phase is None);
        assert(self.sync_requests.superblocking_reqs@.len() == 0);
    }

    proof fn sync_wf_preserved_without_sync_change(pre: &Self, post: &Self)
        requires
            pre.sync_wf(),
            post.sync_requests == pre.sync_requests,
            post.pending_branch_sync == pre.pending_branch_sync,
            pre.pending_branch_sync is None || post.branch == pre.branch,
            post.disk_au_count == pre.disk_au_count,
            pre.pending_branch_sync is Some ==> {
                &&& pre.state().branch == pre.branch@
                &&& post.state().branch == post.branch@
            },
            post.in_flight_sync == pre.in_flight_sync,
            post.state().sync_req_map == pre.state().sync_req_map,
            post.state().sync_phase == pre.state().sync_phase,
            post.state().branch.seq_end() >= pre.state().branch.seq_end(),
            post.state().journal.persistent_seq_end
                >= pre.state().journal.persistent_seq_end,
            !(post.recovery_phase is ReadyForUserOperation)
                ==> !(pre.recovery_phase is ReadyForUserOperation),
            !(pre.recovery_phase is ReadyForUserOperation)
                ==> pre.recovery_sync_empty(),
            pre.in_flight_sync is Some ==> {
                &&& post.outstanding_requests@ == pre.outstanding_requests@
                &&& post.state().journal.in_flight == pre.state().journal.in_flight
                &&& post.state().journal.prepared == pre.state().journal.prepared
                &&& post.state().branch.in_flight == pre.state().branch.in_flight
                &&& post.state().branch.prepared == pre.state().branch.prepared
                &&& post.journal.seq_start() == pre.journal.seq_start()
                &&& post.journal.seq_end() == pre.journal.seq_end()
                &&& post.journal.marshalled_seq_end() == pre.journal.marshalled_seq_end()
                &&& post.state().journal.loaded_index_aus()
                    == pre.state().journal.loaded_index_aus()
            },
        ensures
            post.sync_wf(),
            !(post.recovery_phase is ReadyForUserOperation)
                ==> post.recovery_sync_empty(),
            pre.recovery_sync_empty() ==> post.recovery_sync_empty(),
    {
        reveal(Implementation::sync_wf);
        if pre.pending_branch_sync is Some {
            assert(post.branch == pre.branch);
            assert(pre.state().branch == pre.branch@);
            assert(post.state().branch == post.branch@);
            assert(post.state().branch == pre.state().branch);
        }
        assert(post.sync_requests.all_ids() == pre.sync_requests.all_ids());
        if !(post.recovery_phase is ReadyForUserOperation) {
            assert(!(pre.recovery_phase is ReadyForUserOperation));
            assert(pre.recovery_sync_empty());
            assert(pre.sync_requests.all_ids().len() == 0);
            assert(post.sync_requests.all_ids().len() == 0);
            assert(post.sync_requests == pre.sync_requests);
            assert(post.sync_requests_empty()) by {
                reveal(Implementation::sync_requests_empty);
            }
            assert(post.in_flight_sync is None);
            assert(post.state().sync_phase is None);
            assert(post.state().sync_req_map == Map::<SyncReqId, nat>::empty());
            assert(post.recovery_sync_empty()) by {
                reveal(Implementation::recovery_sync_empty);
            }
        }
        assert(post.sync_requests.ids_unique());
        assert(post.sync_requests.all_ids().to_set()
            =~= post.state().sync_req_map.dom()) by {
            assert(pre.sync_requests.all_ids().to_set()
                =~= pre.state().sync_req_map.dom());
        }
        assert forall |i: int| 0 <= i < post.sync_requests.journal_cleaning_reqs@.len()
            implies #[trigger] post.state().sync_req_map[
                post.sync_requests.journal_cleaning_reqs@[i]
            ] <= post.sync_requests.sync_target_lsn as nat by {
            assert(post.sync_requests.journal_cleaning_reqs@
                == pre.sync_requests.journal_cleaning_reqs@);
            assert(post.sync_requests.sync_target_lsn
                == pre.sync_requests.sync_target_lsn);
            assert(pre.state().sync_req_map
                == post.state().sync_req_map);
            assert(pre.state().sync_req_map[
                pre.sync_requests.journal_cleaning_reqs@[i]
            ] <= pre.sync_requests.sync_target_lsn as nat);
        }
        assert forall |i: int| 0 <= i < post.sync_requests.buffered_reqs@.len()
            implies #[trigger] post.state().sync_req_map[
                post.sync_requests.buffered_reqs@[i]
            ] <= post.state().branch.seq_end() by {
            assert(post.sync_requests.buffered_reqs@
                == pre.sync_requests.buffered_reqs@);
            assert(post.state().sync_req_map == pre.state().sync_req_map);
            assert(pre.state().sync_req_map[
                pre.sync_requests.buffered_reqs@[i]
            ] <= pre.state().branch.seq_end());
        }
        match post.in_flight_sync {
            None => {
                assert(pre.in_flight_sync is None);
                assert(post.state().sync_phase is None);
                assert forall |i: int| 0 <= i < post.sync_requests.superblocking_reqs@.len()
                    implies #[trigger] post.state().sync_req_map[
                        post.sync_requests.superblocking_reqs@[i]
                    ] <= post.state().journal.persistent_seq_end by {
                    assert(post.sync_requests.superblocking_reqs@
                        == pre.sync_requests.superblocking_reqs@);
                    assert(post.state().sync_req_map == pre.state().sync_req_map);
                }
            },
            Some(in_flight) => {
                let pre_in_flight = pre.in_flight_sync.unwrap();
                assert(in_flight.req_id == pre_in_flight.req_id);
                assert(in_flight.image@@ == pre_in_flight.image@@);
                assert(in_flight.image@@.wf());
                if in_flight.flavor is JournalOnly {
                    assert(pre_in_flight.flavor is JournalOnly);
                    assert(in_flight.image@@.journal_snapshot.boundary_lsn
                        == post.journal.seq_start());
                }
                assert(post.state().sync_phase == pre.state().sync_phase);
                assert(post.state().sync_phase == AtomicSyncPhase::SuperblockWriteIssued{
                    req_id: in_flight.req_id,
                    image: in_flight.image@@,
                });
                assert(post.sync_requests.journal_cleaning_reqs@.len() == 0);
                assert(post.sync_requests.superblocking_reqs@.len() > 0);
                assert(post.outstanding_requests@.contains_key(in_flight.req_id));
                assert(post.outstanding_requests@[in_flight.req_id] is SuperblockWrite);
                assert forall |i: int| 0 <= i < post.sync_requests.superblocking_reqs@.len()
                    implies #[trigger] post.state().sync_req_map[
                        post.sync_requests.superblocking_reqs@[i]
                    ] <= in_flight.image@@.journal_seq_end by {
                    assert(post.sync_requests.superblocking_reqs@
                        == pre.sync_requests.superblocking_reqs@);
                    assert(post.state().sync_req_map == pre.state().sync_req_map);
                    assert(pre.state().sync_req_map[
                        pre.sync_requests.superblocking_reqs@[i]
                    ] <= pre_in_flight.image@@.journal_seq_end);
                }
            },
        }
        if pre.recovery_sync_empty() {
            reveal(Implementation::recovery_sync_empty);
            reveal(Implementation::sync_requests_empty);
            assert(post.sync_requests.buffered_reqs@
                == pre.sync_requests.buffered_reqs@);
            assert(post.sync_requests.journal_cleaning_reqs@
                == pre.sync_requests.journal_cleaning_reqs@);
            assert(post.sync_requests.superblocking_reqs@
                == pre.sync_requests.superblocking_reqs@);
            assert(post.sync_requests.all_ids()
                == pre.sync_requests.all_ids());
            assert(post.sync_requests.ids_unique());
            assert(post.recovery_sync_empty());
        }
    }

    proof fn singleton_req_map_values(id: ID, req: DiskRequest)
        ensures
            map![id => req].values() == set![req],
    {
        let m = map![id => req];
        assert forall |r: DiskRequest| #[trigger] m.values().contains(r)
            implies set![req].contains(r) by {
            let key = choose |key: ID| m.contains_key(key) && #[trigger] m[key] == r;
            assert(key == id);
            assert(r == req);
        }
        assert forall |r: DiskRequest| #[trigger] set![req].contains(r)
            implies m.values().contains(r) by {
            assert(r == req);
            assert(m.contains_key(id));
            assert(m[id] == req);
        }
    }

    proof fn singleton_updated_addr_map(
        id: ID,
        req: DiskRequest,
        addr: Address,
    )
        requires
            req.addr() == addr,
        ensures
            Map::new(|i| map![id => req].contains_key(i), |i| map![id => req][i].addr())
                == map![id => addr],
    {
        let updated = Map::new(
            |i| map![id => req].contains_key(i),
            |i| map![id => req][i].addr(),
        );
        assert_maps_equal!(updated, map![id => addr], i => {
            if i == id {
                assert(map![id => req].contains_key(i));
                assert(updated[i] == req.addr());
            } else {
                assert(!map![id => req].contains_key(i));
            }
        });
    }

    proof fn iau_vec_set_matches_branch_set(aus: Seq<IAU>)
        ensures
            iau_vec_set(aus) =~= iau_seq_set(aus),
    {
        let branch_map = Map::new(
            |i: int| 0 <= i < aus.len(),
            |i: int| aus[i] as nat,
        );
        assert(branch_map.values() == iau_seq_set(aus)) by {
        }
        assert_sets_equal!(iau_vec_set(aus), iau_seq_set(aus), au => {
            if iau_vec_set(aus).contains(au) {
                let i = choose |i: int| 0 <= i < aus.len() && #[trigger] (aus[i] as nat) == au;
                assert(branch_map.contains_key(i));
                assert(branch_map[i] == au);
                assert(branch_map.values().contains(au)) by {
                }
            }
            if iau_seq_set(aus).contains(au) {
                assert(branch_map.values().contains(au));
                let i = choose |i: int| branch_map.contains_key(i) && #[trigger] branch_map[i] == au;
                assert(0 <= i < aus.len());
                assert((aus[i] as nat) == au);
                assert(iau_vec_set(aus).contains(au));
            }
        });
    }

    proof fn cache_resps_singleton(
        pre_cache_reqs: Map<ID, Address>,
        id: ID,
        addr: Address,
        resp: DiskResponse,
    )
        requires
            pre_cache_reqs == map![id => addr],
        ensures ({
            let resp_map = map![id => resp];
            let finished_cache_reqs = pre_cache_reqs.restrict(resp_map.dom()).invert();
            let cache_resps = Map::new(
                |a| finished_cache_reqs.contains_key(a),
                |a| resp_map[finished_cache_reqs[a]],
            );
            cache_resps == map![addr => resp]
        }),
    {
        let resp_map = map![id => resp];
        let restricted = pre_cache_reqs.restrict(resp_map.dom());
        assert_maps_equal!(restricted, map![id => addr], k => {
            if k == id {
                assert(resp_map.dom().contains(k));
            } else {
                assert(!pre_cache_reqs.contains_key(k));
            }
        });
        let finished_cache_reqs = restricted.invert();
        assert_maps_equal!(finished_cache_reqs, map![addr => id], a => {
            if a == addr {
                assert(restricted.contains_pair(id, addr));
            } else {
                assert(!restricted.contains_value(a));
            }
        });
        let cache_resps = Map::new(
            |a| finished_cache_reqs.contains_key(a),
            |a| resp_map[finished_cache_reqs[a]],
        );
        assert_maps_equal!(cache_resps, map![addr => resp], a => {
            if a == addr {
                assert(finished_cache_reqs[a] == id);
            } else {
                assert(!finished_cache_reqs.contains_key(a));
            }
        });
    }
}

///////////////////////////////////////////////////////////////////////////////
// Refinement Proof Obligations
//
// The trait implementation has to keep these proof methods inside the trait
// impl, but the whole proof-obligation block lives below the executable
// implementation so the runtime shape stays easier to read.
///////////////////////////////////////////////////////////////////////////////

impl RefinementObligation<UnifiedCacheProgramModel> for UnifiedCacheRefinementProof {
    open spec fn inv(model: SystemModel::State<UnifiedCacheProgramModel>) -> bool
    {
        let unified = UnifiedCacheSystemRefinement::unified_cache_system_i(model);
        &&& UnifiedCacheSystemRefinement::inv(model)
        &&& CachingDiskSystemRefinement::caching_disk_system_coordination_i(unified).inv()
    }

    open spec fn i(model: SystemModel::State<UnifiedCacheProgramModel>) -> CrashTolerantAsyncMap::State
    {
        CachingDiskSystemRefinement::caching_disk_system_i(
            UnifiedCacheSystemRefinement::unified_cache_system_i(model),
        )
    }

    open spec fn i_lbl(
        pre: SystemModel::State<UnifiedCacheProgramModel>,
        post: SystemModel::State<UnifiedCacheProgramModel>,
        lbl: SystemModel::Label,
    ) -> CrashTolerantAsyncMap::Label
    {
        CachingDiskSystemRefinement::caching_disk_system_i_lbl(
            UnifiedCacheSystemRefinement::unified_cache_system_i(pre),
            UnifiedCacheSystemRefinement::unified_cache_system_i(post),
            UnifiedCacheSystemRefinement::unified_cache_system_i_lbl(pre, post, lbl),
        )
    }

    proof fn i_lbl_valid(
        pre: SystemModel::State<UnifiedCacheProgramModel>,
        post: SystemModel::State<UnifiedCacheProgramModel>,
        lbl: SystemModel::Label,
        ctam_lbl: CrashTolerantAsyncMap::Label,
    )
    {
    }

    proof fn init_refines(pre: SystemModel::State<UnifiedCacheProgramModel>)
    {
        UnifiedCacheSystemRefinement::init_refines(pre);
        CachingDiskSystemRefinement::init_refines_ctam(
            UnifiedCacheSystemRefinement::unified_cache_system_i(pre),
        );

        assert(CrashTolerantAsyncMap::State::init(Self::i(pre)));
        reveal(CrashTolerantAsyncMap::State::init);
        reveal(CrashTolerantAsyncMap::State::init_by);
        let config = choose |config| CrashTolerantAsyncMap::State::init_by(Self::i(pre), config);
        match config {
            CrashTolerantAsyncMap::Config::initialize() => {
                assert(CrashTolerantAsyncMap::State::initialize(Self::i(pre)));
            },
            CrashTolerantAsyncMap::Config::dummy_to_use_type_params(_) => {
                assert(false);
            },
        }
    }

    proof fn next_refines(
        pre: SystemModel::State<UnifiedCacheProgramModel>,
        post: SystemModel::State<UnifiedCacheProgramModel>,
        lbl: SystemModel::Label,
    )
    {
        let unified_pre = UnifiedCacheSystemRefinement::unified_cache_system_i(pre);
        let unified_post = UnifiedCacheSystemRefinement::unified_cache_system_i(post);
        let unified_lbl = UnifiedCacheSystemRefinement::unified_cache_system_i_lbl(pre, post, lbl);

        UnifiedCacheSystemRefinement::next_refines(pre, post, lbl);
        UnifiedCacheSystemRefinement::inv_implies_caching_disk_refinement_inv(pre);
        CachingDiskSystemRefinement::next_refines_ctam(unified_pre, unified_post, unified_lbl);
    }

}

} // verus!
