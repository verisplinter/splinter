// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Skeleton refinement boundary:
// UnifiedCache branch projection -> CrashAwareCachingDiskBranch.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;

use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::AbstractSuperblock_v::AbstractSuperblockImage;
use crate::implementation::AllocationBranchStack_v::normalize_value;
use crate::implementation::AnotherAtomicState_v::{
    AtomicBranchState, AtomicInflightInfo,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CrashAwareCachingDiskBranch_v::CrashAwareCachingDiskBranch;
use crate::implementation::UnifiedCacheProgramModel_v::UnifiedCacheProgramModel;
use crate::implementation::UnifiedCacheSystem_v::UnifiedCacheSystem;
use crate::trusted::ProgramModelTrait_t::DiskModel;
use crate::trusted::SystemModel_t::SystemModel;

verus! {

#[verifier::ext_equal]
pub struct UnifiedCacheBranchSource {
    pub branch: AtomicBranchState::State,
    pub cache: Cache::State,
    pub disk: DiskModel,
    pub persistent_image: Option<AbstractSuperblockImage>,
    pub in_flight: Option<AtomicInflightInfo>,
    pub in_flight_image: Option<AbstractSuperblockImage>,
}

pub open spec fn unified_cache_branch_source(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> UnifiedCacheBranchSource
{
    let state = model.program.state;
    UnifiedCacheBranchSource{
        branch: state.branch,
        cache: state.cache,
        disk: model.disk,
        persistent_image: state.persistent_image,
        in_flight: state.in_flight,
        in_flight_image: if state.in_flight is Some {
            Option::Some(state.atomic_inflight_superblock_i())
        } else {
            Option::None
        },
    }
}

pub open spec fn unified_cache_branch_i(
    src: UnifiedCacheBranchSource,
) -> CrashAwareCachingDiskBranch::State
{
    arbitrary()
}

pub open spec fn unified_cache_branch_i_lbl(
    lbl: AtomicBranchState::Label,
) -> CrashAwareCachingDiskBranch::Label
{
    match lbl {
        AtomicBranchState::Label::Query{key, msg, ..} => {
            CrashAwareCachingDiskBranch::Label::Query{
                key,
                value: normalize_value(msg),
            }
        },
        AtomicBranchState::Label::LoadMetadata{root, discovered_aus, ..} => {
            CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus}
        },
        AtomicBranchState::Label::Append{keys, msgs, ..} => {
            CrashAwareCachingDiskBranch::Label::Append{keys, msgs}
        },
        AtomicBranchState::Label::Grow{..}
        | AtomicBranchState::Label::Split{..}
        | AtomicBranchState::Label::Seal{..}
        | AtomicBranchState::Label::ObservePersistedRoots{..} => {
            CrashAwareCachingDiskBranch::Label::Internal
        },
        AtomicBranchState::Label::FillAUs{aus} => {
            CrashAwareCachingDiskBranch::Label::InternalAlloc{
                allocs: aus,
                deallocs: Set::empty(),
            }
        },
        AtomicBranchState::Label::CommitStart{branch_image} => {
            CrashAwareCachingDiskBranch::Label::CommitStart{
                new_boundary_lsn: branch_image.seq_end,
                sealed_roots: branch_image.sealed_roots,
            }
        },
        AtomicBranchState::Label::CommitPrepared => {
            CrashAwareCachingDiskBranch::Label::FreezePrepared
        },
        AtomicBranchState::Label::CommitComplete => {
            CrashAwareCachingDiskBranch::Label::CommitComplete
        },
    }
}

pub open spec fn inv(src: UnifiedCacheBranchSource) -> bool
{
    arbitrary()
}

pub open spec fn init_shared_facts(src: UnifiedCacheBranchSource) -> bool
{
    true
}

pub proof fn init_refines(pre: SystemModel::State<UnifiedCacheProgramModel>)
    requires
        SystemModel::State::initialize(pre, pre.program, pre.disk),
        init_shared_facts(unified_cache_branch_source(pre)),
    ensures
        CrashAwareCachingDiskBranch::State::init(
            unified_cache_branch_i(unified_cache_branch_source(pre)),
        ),
        inv(unified_cache_branch_source(pre)),
{
    assume(false);
}

pub proof fn next_refines(
    pre: UnifiedCacheBranchSource,
    post: UnifiedCacheBranchSource,
    lbl: AtomicBranchState::Label,
)
    requires
        AtomicBranchState::State::next(pre.branch, post.branch, lbl),
        inv(pre),
    ensures
        CrashAwareCachingDiskBranch::State::next(
            unified_cache_branch_i(pre),
            unified_cache_branch_i(post),
            unified_cache_branch_i_lbl(lbl),
        ),
        inv(post),
{
    match lbl {
        AtomicBranchState::Label::Query{..}
        | AtomicBranchState::Label::LoadMetadata{..}
        | AtomicBranchState::Label::Append{..}
        | AtomicBranchState::Label::Grow{..}
        | AtomicBranchState::Label::Split{..}
        | AtomicBranchState::Label::Seal{..}
        | AtomicBranchState::Label::FillAUs{..}
        | AtomicBranchState::Label::ObservePersistedRoots{..}
        | AtomicBranchState::Label::CommitStart{..}
        | AtomicBranchState::Label::CommitPrepared
        | AtomicBranchState::Label::CommitComplete => {
            assume(false);
        },
    }
}

} // verus!
