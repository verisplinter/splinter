// Staging bridge from SystemModel<ConcreteProgramModel> to the branch-aware
// CrashAwareCachingDiskSystem.
//
// This is the only place in the CrashAwareCachingDiskSystem path that knows how to project the lower
// physical state into journal, branch, and superblock component views.

#![allow(unused_imports)]

use vstd::prelude::*;

use crate::abstract_system::MsgHistory_v::MsgHistory;
use crate::implementation::AtomicState_v::AtomicState;
use crate::implementation::ConcreteProgramModel_v::ConcreteProgramModel;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::CrashAwareCachingDiskSystem_v::{CrashAwareCachingDiskSystem, SuperblockStore};
use crate::spec::AsyncDisk_t::{AsyncDisk, RawPage};
use crate::spec::MapSpec_t::{AsyncMap, EphemeralState, Reply, Request};
use crate::trusted::ProgramModelTrait_t::ProgramUserOp;
use crate::trusted::SystemModel_t::SystemModel;

verus!{

pub open spec fn superblock_disk_projection(disk: AsyncDisk::State) -> AsyncDisk::State
{
    AtomicState::disk_project(disk, set![spec_superblock_addr()])
}

pub open spec fn empty_raw_page() -> RawPage
{
    CrashAwareCachingDiskSystem::State::empty_superblock_page()
}

pub open spec fn persistent_superblock_projection(disk: AsyncDisk::State) -> RawPage
{
    if disk.content.dom().contains(spec_superblock_addr()) {
        disk.content[spec_superblock_addr()]
    } else {
        empty_raw_page()
    }
}

pub open spec fn in_flight_superblock_projection(atomic: AtomicState) -> Option<RawPage>
{
    if atomic.in_flight is Some {
        Option::Some(empty_raw_page())
    } else {
        Option::None
    }
}

pub open spec fn journal_disk_projection_without_superblock(
    atomic: AtomicState,
    disk: AsyncDisk::State,
) -> AsyncDisk::State
{
    AtomicState::disk_project(
        disk,
        disk.content.dom()
            .difference(atomic.branch_owned_addrs())
            .difference(set![spec_superblock_addr()]),
    )
}

pub open spec fn system_model_to_system_model_two(
    sm: SystemModel::State<ConcreteProgramModel>,
) -> CrashAwareCachingDiskSystem::State
{
    let atomic = sm.program.state;
    CrashAwareCachingDiskSystem::State {
        journal: CrashAwareCachingDiskSystem::State::empty_journal(),
        branch: CrashAwareCachingDiskSystem::State::empty_branch(),
        progress: EphemeralState{
            requests: Set::new(|req: Request| sm.requests.contains(req)),
            replies: Set::new(|reply: Reply| sm.replies.contains(reply)),
        },
        sync_reqs: atomic.sync_req_map,
        superblockstore: SuperblockStore::State{
            persistent: persistent_superblock_projection(sm.disk),
            in_flight: in_flight_superblock_projection(atomic),
            landed: false,
        },
        free_aus: Set::empty(),
    }
}

pub open spec fn system_model_to_system_model_two_label(
    pre: SystemModel::State<ConcreteProgramModel>,
    post: SystemModel::State<ConcreteProgramModel>,
    lbl: SystemModel::Label,
) -> CrashAwareCachingDiskSystem::Label
{
    match lbl {
        SystemModel::Label::AcceptRequest{req} => CrashAwareCachingDiskSystem::Label::Request{req},
        SystemModel::Label::DeliverReply{reply} => CrashAwareCachingDiskSystem::Label::Reply{reply},
        SystemModel::Label::AcceptSyncRequest{sync_req_id} =>
            CrashAwareCachingDiskSystem::Label::Noop,
        SystemModel::Label::DeliverSyncReply{sync_req_id} =>
            CrashAwareCachingDiskSystem::Label::Noop,
        SystemModel::Label::ProgramUIOp{op} => match op {
            ProgramUserOp::Execute{req, reply} =>
                CrashAwareCachingDiskSystem::Label::Execute{req, reply},
            ProgramUserOp::AcceptSyncRequest{sync_req_id} =>
                CrashAwareCachingDiskSystem::Label::ReqSync{sync_req_id},
            ProgramUserOp::DeliverSyncReply{sync_req_id} =>
                CrashAwareCachingDiskSystem::Label::ReplySync{sync_req_id},
        },
        SystemModel::Label::DiskInternal => {
            let caching_disk_system_pre = system_model_to_system_model_two(pre);
            let caching_disk_system_post = system_model_to_system_model_two(post);
            if !caching_disk_system_pre.superblock.landed && caching_disk_system_post.superblock.landed {
                CrashAwareCachingDiskSystem::Label::Sync
            } else {
                CrashAwareCachingDiskSystem::Label::Noop
            }
        },
        SystemModel::Label::Crash => CrashAwareCachingDiskSystem::Label::Crash,
        _ => CrashAwareCachingDiskSystem::Label::Noop,
    }
}

pub proof fn next_refines(
    pre: SystemModel::State<ConcreteProgramModel>,
    post: SystemModel::State<ConcreteProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::next(pre, post, lbl),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            system_model_to_system_model_two(pre),
            system_model_to_system_model_two(post),
            system_model_to_system_model_two_label(pre, post, lbl)),
        system_model_to_system_model_two(pre).inv()
            ==> system_model_to_system_model_two(post).inv(),
{
    assume(false); // staged: prove physical projection step simulation later
}

}
