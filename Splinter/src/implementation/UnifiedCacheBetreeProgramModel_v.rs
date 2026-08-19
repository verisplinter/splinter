// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// ProgramModelTrait wrapper for UnifiedCacheBetreeSystem.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::implementation::AbstractSuperblock_v::{
    abstract_superblock_raw_wf, empty_abstract_superblock_image,
    parse_abstract_superblock,
};
use crate::implementation::DiskLayout_v::{
    spec_superblock_addr, DiskLayout,
};
use crate::implementation::UnifiedCacheBetreeSystem_v::
    UnifiedCacheBetreeSystem;
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse};
use crate::spec::MapSpec_t::ID;
use crate::trusted::ProgramModelTrait_t::{
    DiskModel, ProgramDiskInfo, ProgramLabel, ProgramModelTrait,
    ProgramUserOp,
};

verus! {

#[verifier::ext_equal]
pub struct UnifiedCacheBetreeProgramModel {
    pub state: UnifiedCacheBetreeSystem::State,
}

impl UnifiedCacheBetreeProgramModel {
    pub open spec fn disk_step_matches_info(
        pre: UnifiedCacheBetreeSystem::State,
        step: UnifiedCacheBetreeSystem::Step,
        info: ProgramDiskInfo,
    ) -> bool {
        match step {
            UnifiedCacheBetreeSystem::Step::initiate_recovery(
                _,
                reqs,
                resps,
            ) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheBetreeSystem::Step::superblock_recovery(
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
            UnifiedCacheBetreeSystem::Step::execute_journal_sync_begin(
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
            UnifiedCacheBetreeSystem::Step::execute_journal_sync_end(
                _,
                _,
                reqs,
                resps,
            ) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheBetreeSystem::Step::execute_store_sync_begin(
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
            UnifiedCacheBetreeSystem::Step::execute_sync_superblock_write(
                _,
                _,
                reqs,
                resps,
            ) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheBetreeSystem::Step::execute_store_sync_end(
                _,
                _,
                reqs,
                resps,
            ) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheBetreeSystem::Step::cache_io_begin(
                _,
                _,
                reqs,
                resps,
            ) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
            },
            UnifiedCacheBetreeSystem::Step::cache_io_end(
                resp_map,
                _,
                reqs,
                resps,
            ) => {
                &&& reqs == info.reqs
                &&& resps == info.resps
                &&& resp_map.dom()
                    <= pre.outstanding_cache_reqs.dom()
            },
            _ => false,
        }
    }

    pub open spec fn valid_disk_transition(
        pre: Self,
        post: Self,
        info: ProgramDiskInfo,
    ) -> bool {
        exists |step: UnifiedCacheBetreeSystem::Step| #![auto] {
            &&& UnifiedCacheBetreeSystem::State::next_by(
                pre.state,
                post.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                step,
            )
            &&& Self::disk_step_matches_info(
                pre.state,
                step,
                info,
            )
        }
    }

    pub proof fn lift_internal_step(pre: Self, post: Self)
        requires
            exists |step: UnifiedCacheBetreeSystem::Step|
                UnifiedCacheBetreeSystem::State::next_by(
                    pre.state,
                    post.state,
                    UnifiedCacheBetreeSystem::Label::Internal,
                    step,
                ),
        ensures
            ProgramModelTrait::next(
                pre,
                post,
                ProgramLabel::Internal{},
            ),
    {
        assert(UnifiedCacheBetreeSystem::State::next(
            pre.state,
            post.state,
            UnifiedCacheBetreeSystem::Label::Internal,
        )) by {
            reveal(UnifiedCacheBetreeSystem::State::next);
        }
    }

    pub proof fn lift_execute_step(
        pre: Self,
        post: Self,
        req: crate::spec::MapSpec_t::Request,
        reply: crate::spec::MapSpec_t::Reply,
    )
        requires UnifiedCacheBetreeSystem::State::next(
            pre.state,
            post.state,
            UnifiedCacheBetreeSystem::Label::Execute { req, reply },
        ),
        ensures ProgramModelTrait::next(
            pre,
            post,
            ProgramLabel::UserIO {
                op: ProgramUserOp::Execute { req, reply },
            },
        ),
    {
    }

    pub proof fn lift_accept_sync_step(
        pre: Self,
        post: Self,
        sync_req_id: crate::spec::MapSpec_t::SyncReqId,
    )
        requires UnifiedCacheBetreeSystem::State::next(
            pre.state,
            post.state,
            UnifiedCacheBetreeSystem::Label::AcceptSyncRequest {
                sync_req_id,
            },
        ),
        ensures ProgramModelTrait::next(
            pre,
            post,
            ProgramLabel::UserIO {
                op: ProgramUserOp::AcceptSyncRequest { sync_req_id },
            },
        ),
    {
    }

    pub proof fn lift_deliver_sync_step(
        pre: Self,
        post: Self,
        sync_req_id: crate::spec::MapSpec_t::SyncReqId,
    )
        requires UnifiedCacheBetreeSystem::State::next(
            pre.state,
            post.state,
            UnifiedCacheBetreeSystem::Label::DeliverSyncReply {
                sync_req_id,
            },
        ),
        ensures ProgramModelTrait::next(
            pre,
            post,
            ProgramLabel::UserIO {
                op: ProgramUserOp::DeliverSyncReply { sync_req_id },
            },
        ),
    {
    }

    pub proof fn lift_disk_step(
        pre: Self,
        post: Self,
        info: ProgramDiskInfo,
    )
        requires
            exists |step: UnifiedCacheBetreeSystem::Step| {
                &&& UnifiedCacheBetreeSystem::State::next_by(
                    pre.state,
                    post.state,
                    UnifiedCacheBetreeSystem::Label::Disk,
                    step,
                )
                &&& Self::disk_step_matches_info(
                    pre.state,
                    step,
                    info,
                )
            },
        ensures
            ProgramModelTrait::next(
                pre,
                post,
                ProgramLabel::DiskIO{info},
            ),
    {
    }
}

impl ProgramModelTrait for UnifiedCacheBetreeProgramModel {
    open spec fn is_mkfs(disk: DiskModel) -> bool {
        &&& DiskLayout::spec_new().mkfs(disk.content)
        &&& disk.content.dom() =~= set![spec_superblock_addr()]
        &&& abstract_superblock_raw_wf(
            disk.content[spec_superblock_addr()],
        )
        &&& parse_abstract_superblock(
            disk.content[spec_superblock_addr()],
        ) == empty_abstract_superblock_image()
        &&& disk.requests
            == Map::<ID, DiskRequest>::empty()
        &&& disk.responses
            == Map::<ID, DiskResponse>::empty()
    }

    open spec fn init(pre: Self) -> bool {
        UnifiedCacheBetreeSystem::State::init(pre.state)
    }

    open spec fn next(
        pre: Self,
        post: Self,
        lbl: ProgramLabel,
    ) -> bool {
        match lbl {
            ProgramLabel::UserIO{op} => match op {
                ProgramUserOp::Execute{req, reply} => {
                    UnifiedCacheBetreeSystem::State::next(
                        pre.state,
                        post.state,
                        UnifiedCacheBetreeSystem::Label::Execute{
                            req,
                            reply,
                        },
                    )
                },
                ProgramUserOp::AcceptSyncRequest{sync_req_id} => {
                    UnifiedCacheBetreeSystem::State::next(
                        pre.state,
                        post.state,
                        UnifiedCacheBetreeSystem::Label::
                            AcceptSyncRequest{sync_req_id},
                    )
                },
                ProgramUserOp::DeliverSyncReply{sync_req_id} => {
                    UnifiedCacheBetreeSystem::State::next(
                        pre.state,
                        post.state,
                        UnifiedCacheBetreeSystem::Label::
                            DeliverSyncReply{sync_req_id},
                    )
                },
            },
            ProgramLabel::DiskIO{info} => {
                Self::valid_disk_transition(pre, post, info)
            },
            ProgramLabel::Internal{} => {
                UnifiedCacheBetreeSystem::State::next(
                    pre.state,
                    post.state,
                    UnifiedCacheBetreeSystem::Label::Internal,
                )
            },
        }
    }
}

} // verus!
