// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Program-model wrapper for the staged AnotherAtomicState design.
//
// The trusted SystemModel composes this program state with AsyncDisk::State.
// AnotherAtomicState emits disk requests/responses through ProgramDiskInfo; the
// SystemModel takes the matching AsyncDisk step in the same ProgramDiskOp.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::implementation::AnotherAtomicState_v::{
    AnotherAtomicState, DiskEvent, InternalEvent, ProgramEvent,
};
use crate::implementation::AbstractSuperblock_v::{
    abstract_superblock_raw_wf, empty_abstract_superblock_image, parse_abstract_superblock,
};
use crate::implementation::DiskLayout_v::DiskLayout;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::spec::AsyncDisk_t::{DiskRequest, DiskResponse};
use crate::spec::MapSpec_t::ID;
use crate::trusted::ProgramModelTrait_t::{
    DiskModel, ProgramDiskInfo, ProgramLabel, ProgramModelTrait, ProgramUserOp,
};

verus! {

#[verifier::ext_equal]
pub struct AnotherProgramModel {
    pub state: AnotherAtomicState,
}

impl AnotherProgramModel {
    pub open spec fn valid_disk_transition(pre: Self, post: Self, info: ProgramDiskInfo) -> bool
    {
        exists |disk_event: DiskEvent| AnotherAtomicState::disk_transition(
            pre.state,
            post.state,
            disk_event,
            info.reqs,
            info.resps,
        )
    }

    pub open spec fn valid_internal_transition(pre: Self, post: Self) -> bool
    {
        exists |internal_event: InternalEvent| AnotherAtomicState::internal_transition(
            pre.state,
            post.state,
            internal_event,
        )
    }
}

impl ProgramModelTrait for AnotherProgramModel {
    open spec fn is_mkfs(disk: DiskModel) -> bool
    {
        &&& DiskLayout::spec_new().mkfs(disk.content)
        &&& abstract_superblock_raw_wf(disk.content[spec_superblock_addr()])
        &&& parse_abstract_superblock(disk.content[spec_superblock_addr()])
            == empty_abstract_superblock_image()
        &&& disk.requests == Map::<ID, DiskRequest>::empty()
        &&& disk.responses == Map::<ID, DiskResponse>::empty()
    }

    open spec fn init(pre: Self) -> bool
    {
        exists |cache_slots: nat, free_aus: Set<crate::disk::GenericDisk_v::AU>|
            free_aus.disjoint(AnotherAtomicState::reserved_aus()) &&
            pre.state == AnotherAtomicState::init(cache_slots, free_aus)
    }

    open spec fn next(pre: Self, post: Self, lbl: ProgramLabel) -> bool
    {
        match lbl {
            ProgramLabel::UserIO{op} => {
                match op {
                    ProgramUserOp::Execute{req, reply} => {
                        exists |program_event: ProgramEvent| AnotherAtomicState::execute_transition(
                            pre.state,
                            post.state,
                            req,
                            reply,
                            program_event,
                        )
                    },
                    ProgramUserOp::AcceptSyncRequest{sync_req_id} => {
                        AnotherAtomicState::accept_sync_request(pre.state, post.state, sync_req_id)
                    },
                    ProgramUserOp::DeliverSyncReply{sync_req_id} => {
                        AnotherAtomicState::deliver_sync_reply(pre.state, post.state, sync_req_id)
                    },
                }
            },
            ProgramLabel::DiskIO{info} => {
                Self::valid_disk_transition(pre, post, info)
            },
            ProgramLabel::Internal{} => {
                Self::valid_internal_transition(pre, post)
            },
        }
    }
}

} // verus!
