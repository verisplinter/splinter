// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// ProgramModelTrait wrapper for UnifiedCacheSystem.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf, empty_abstract_superblock_image,
    parse_abstract_superblock,
};
use crate::implementation::AtomicBranchState_v::AtomicBranchState;
use crate::implementation::AtomicJournalState_v::AtomicJournalState;
use crate::implementation::Cache_v::Cache;
use crate::implementation::DiskLayout_v::DiskLayout;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::UnifiedCacheSystem_v::UnifiedCacheSystem;
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse, RawPage};
use crate::spec::MapSpec_t::ID;
use crate::trusted::ProgramModelTrait_t::{
    DiskModel, ProgramDiskInfo, ProgramLabel, ProgramModelTrait, ProgramUserOp,
};

verus! {

#[verifier::ext_equal]
pub struct UnifiedCacheProgramModel {
    pub state: UnifiedCacheSystem::State,
}

impl UnifiedCacheProgramModel {
    pub open spec fn disk_step_matches_info(
        pre: UnifiedCacheSystem::State,
        step: UnifiedCacheSystem::Step,
        info: ProgramDiskInfo,
    ) -> bool
    {
        match step {
            UnifiedCacheSystem::Step::initiate_recovery(_, reqs, resps) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheSystem::Step::superblock_recovery(
                _,
                _,
                _,
                _,
                _,
                reqs,
                resps,
            ) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheSystem::Step::execute_sync_begin(
                _,
                _,
                _,
                _,
                _,
                reqs,
                resps,
            ) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheSystem::Step::execute_sync_prepared(_, _, _, _, reqs, resps) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheSystem::Step::execute_sync_end(_, _, _, reqs, resps) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheSystem::Step::cache_io_begin(_, _, reqs, resps) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheSystem::Step::cache_io_end(resp_map, _, reqs, resps) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
                &&& resp_map.dom() <= pre.outstanding_cache_reqs.dom()
            },
            _ => false,
        }
    }

    pub open spec fn valid_disk_transition(pre: Self, post: Self, info: ProgramDiskInfo) -> bool
    {
        exists |step: UnifiedCacheSystem::Step| {
            &&& UnifiedCacheSystem::State::next_by(
                pre.state,
                post.state,
                UnifiedCacheSystem::Label::Disk,
                step,
            )
            &&& Self::disk_step_matches_info(pre.state, step, info)
        }
    }
}

impl ProgramModelTrait for UnifiedCacheProgramModel {
    open spec fn is_mkfs(disk: DiskModel) -> bool
    {
        &&& DiskLayout::spec_new().mkfs(disk.content)
        &&& disk.content.dom() =~= set![spec_superblock_addr()]
        &&& abstract_superblock_raw_wf(disk.content[spec_superblock_addr()])
        &&& parse_abstract_superblock(disk.content[spec_superblock_addr()])
            == empty_abstract_superblock_image()
        &&& disk.requests == Map::<ID, DiskRequest>::empty()
        &&& disk.responses == Map::<ID, DiskResponse>::empty()
    }

    open spec fn init(pre: Self) -> bool
    {
        UnifiedCacheSystem::State::init(pre.state)
    }

    open spec fn next(pre: Self, post: Self, lbl: ProgramLabel) -> bool
    {
        match lbl {
            ProgramLabel::UserIO{op} => {
                match op {
                    ProgramUserOp::Execute{req, reply} => {
                        UnifiedCacheSystem::State::next(
                            pre.state,
                            post.state,
                            UnifiedCacheSystem::Label::Execute{req, reply},
                        )
                    },
                    ProgramUserOp::AcceptSyncRequest{sync_req_id} => {
                        UnifiedCacheSystem::State::next(
                            pre.state,
                            post.state,
                            UnifiedCacheSystem::Label::AcceptSyncRequest{sync_req_id},
                        )
                    },
                    ProgramUserOp::DeliverSyncReply{sync_req_id} => {
                        UnifiedCacheSystem::State::next(
                            pre.state,
                            post.state,
                            UnifiedCacheSystem::Label::DeliverSyncReply{sync_req_id},
                        )
                    },
                }
            },
            ProgramLabel::DiskIO{info} => {
                Self::valid_disk_transition(pre, post, info)
            },
            ProgramLabel::Internal{} => {
                UnifiedCacheSystem::State::next(
                    pre.state,
                    post.state,
                    UnifiedCacheSystem::Label::Internal,
                )
            },
        }
    }
}

} // verus!
