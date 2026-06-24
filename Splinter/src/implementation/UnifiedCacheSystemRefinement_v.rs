// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Skeleton refinement boundary:
// SystemModel<UnifiedCacheProgramModel> -> CrashAwareCachingDiskSystem.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::multiset::Multiset;

use crate::implementation::AbstractSuperblock_v::{
    empty_abstract_superblock_image, marshal_abstract_superblock,
};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CrashAwareCachingDiskBranch_v::CrashAwareCachingDiskBranch;
use crate::implementation::CrashAwareCachingDiskJournal_v::CrashAwareCachingDiskJournal;
use crate::implementation::CrashAwareCachingDiskSystem_v::{
    CrashAwareCachingDiskSystem, SuperblockStore,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::UnifiedCacheBranchRefinement_v as UnifiedCacheBranchRefinement;
use crate::implementation::UnifiedCacheJournalRefinement_v as UnifiedCacheJournalRefinement;
use crate::implementation::UnifiedCacheProgramModel_v::UnifiedCacheProgramModel;
use crate::implementation::UnifiedCacheSystem_v::UnifiedCacheSystem;
use crate::spec::MapSpec_t::{EphemeralState, Reply, Request};
use crate::trusted::ProgramModelTrait_t::{ProgramModelTrait, ProgramUserOp};
use crate::trusted::SystemModel_t::SystemModel;

verus! {

pub open spec fn system_multiset_to_set_i<V>(m: Multiset<V>) -> Set<V>
{
    Set::new(|v| m.contains(v))
}

pub open spec fn unified_cache_progress_i(
    requests: Multiset<Request>,
    replies: Multiset<Reply>,
) -> EphemeralState
{
    EphemeralState{
        requests: system_multiset_to_set_i(requests),
        replies: system_multiset_to_set_i(replies),
    }
}

pub open spec fn unified_cache_superblock_write_pending(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    &&& model.program.state.in_flight is Some
    &&& model.disk.requests.contains_key(model.program.state.in_flight.unwrap().req_id)
    &&& model.disk.requests[model.program.state.in_flight.unwrap().req_id] is WriteReq
    &&& model.disk.requests[model.program.state.in_flight.unwrap().req_id]->to
        == spec_superblock_addr()
}

pub open spec fn unified_cache_in_flight_superblock_landed(
    state: UnifiedCacheSystem::State,
    disk: crate::trusted::ProgramModelTrait_t::DiskModel,
) -> bool
{
    &&& state.in_flight is Some
    &&& disk.content.contains_key(spec_superblock_addr())
    &&& disk.content[spec_superblock_addr()]
        == marshal_abstract_superblock(state.atomic_inflight_superblock_i())
}

pub open spec fn unified_cache_superblockstore_i(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> SuperblockStore::State
{
    let persistent = if model.disk.content.contains_key(spec_superblock_addr()) {
        model.disk.content[spec_superblock_addr()]
    } else {
        arbitrary()
    };
    let landed = unified_cache_in_flight_superblock_landed(model.program.state, model.disk);
    let pending_raw = if model.program.state.in_flight is Some {
        marshal_abstract_superblock(model.program.state.atomic_inflight_superblock_i())
    } else {
        arbitrary()
    };
    SuperblockStore::State{
        persistent,
        in_flight: if unified_cache_superblock_write_pending(model) && !landed {
            Option::Some(pending_raw)
        } else {
            Option::None
        },
        landed,
    }
}

pub open spec fn unified_cache_system_i(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> CrashAwareCachingDiskSystem::State
{
    CrashAwareCachingDiskSystem::State{
        journal: UnifiedCacheJournalRefinement::unified_cache_journal_i(
            UnifiedCacheJournalRefinement::unified_cache_journal_source(model),
        ),
        branch: UnifiedCacheBranchRefinement::unified_cache_branch_i(
            UnifiedCacheBranchRefinement::unified_cache_branch_source(model),
        ),
        progress: unified_cache_progress_i(model.requests, model.replies),
        sync_reqs: model.program.state.sync_req_map,
        superblockstore: unified_cache_superblockstore_i(model),
        free_aus: model.program.state.free_aus,
    }
}

pub open spec fn unified_cache_system_i_lbl(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
) -> CrashAwareCachingDiskSystem::Label
{
    match lbl {
        SystemModel::Label::AcceptRequest{req} => {
            CrashAwareCachingDiskSystem::Label::Request{req}
        },
        SystemModel::Label::DeliverReply{reply} => {
            CrashAwareCachingDiskSystem::Label::Reply{reply}
        },
        SystemModel::Label::AcceptSyncRequest{..}
        | SystemModel::Label::DeliverSyncReply{..} => {
            CrashAwareCachingDiskSystem::Label::Noop
        },
        SystemModel::Label::ProgramUIOp{op} => {
            match op {
                ProgramUserOp::Execute{req, reply} => {
                    CrashAwareCachingDiskSystem::Label::Execute{req, reply}
                },
                ProgramUserOp::AcceptSyncRequest{sync_req_id} => {
                    CrashAwareCachingDiskSystem::Label::ReqSync{sync_req_id}
                },
                ProgramUserOp::DeliverSyncReply{sync_req_id} => {
                    CrashAwareCachingDiskSystem::Label::ReplySync{sync_req_id}
                },
            }
        },
        SystemModel::Label::DiskInternal => {
            let pre_superblock = unified_cache_superblockstore_i(pre);
            let post_superblock = unified_cache_superblockstore_i(post);
            if !pre_superblock.landed && post_superblock.landed {
                CrashAwareCachingDiskSystem::Label::Sync
            } else {
                CrashAwareCachingDiskSystem::Label::Noop
            }
        },
        SystemModel::Label::Crash => {
            CrashAwareCachingDiskSystem::Label::Crash
        },
        SystemModel::Label::ProgramDiskOp{..}
        | SystemModel::Label::ProgramInternal
        | SystemModel::Label::Noop => {
            CrashAwareCachingDiskSystem::Label::Noop
        },
    }
}

pub open spec fn unified_cache_component_refinement_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    &&& UnifiedCacheJournalRefinement::inv(
        UnifiedCacheJournalRefinement::unified_cache_journal_source(model),
    )
    &&& UnifiedCacheBranchRefinement::inv(
        UnifiedCacheBranchRefinement::unified_cache_branch_source(model),
    )
}

pub open spec fn unified_cache_superblockstore_refinement_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    unified_cache_superblockstore_i(model).inv()
}

pub open spec fn inv(model: SystemModel::State<UnifiedCacheProgramModel>) -> bool
{
    &&& unified_cache_component_refinement_inv(model)
    &&& unified_cache_superblockstore_refinement_inv(model)
    &&& unified_cache_system_i(model).inv()
}

pub proof fn init_refines(pre: SystemModel::State<UnifiedCacheProgramModel>)
    requires
        SystemModel::State::initialize(pre, pre.program, pre.disk),
    ensures
        CrashAwareCachingDiskSystem::State::init(unified_cache_system_i(pre)),
        inv(pre),
{
    reveal(SystemModel::State::initialize);
    assert(UnifiedCacheProgramModel::is_mkfs(pre.disk));
    assert(UnifiedCacheProgramModel::init(pre.program));

    reveal(UnifiedCacheSystem::State::init);
    reveal(UnifiedCacheSystem::State::init_by);
    let config = choose |config: UnifiedCacheSystem::Config|
        UnifiedCacheSystem::State::init_by(pre.program.state, config);

    match config {
        UnifiedCacheSystem::Config::initialize(cache_slots, free_aus) => {
            assert(UnifiedCacheSystem::State::initialize(
                pre.program.state,
                cache_slots,
                free_aus,
            )) by {
                reveal(UnifiedCacheSystem::State::initialize);
            }
            reveal(UnifiedCacheSystem::State::initialize);

            let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
            let branch_src = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
            let dst = unified_cache_system_i(pre);
            let initial_superblock = CrashAwareCachingDiskSystem::State::empty_superblock_page();

            assert(journal_src.persistent_superblock_image_i()
                == empty_abstract_superblock_image()) by {
                assert(pre.disk.content.contains_key(spec_superblock_addr()));
                assert(UnifiedCacheJournalRefinement::async_disk_superblock_raw_i(
                    pre.disk.content,
                ) == pre.disk.content[spec_superblock_addr()]);
            }
            assert(UnifiedCacheJournalRefinement::async_disk_superblock_page_wf(
                pre.disk.content,
            ));
            assert(pre.disk.inv());
            assert(pre.program.state.cache.inv()) by {
                assert(Cache::State::initialize(pre.program.state.cache, cache_slots)) by {
                    reveal(Cache::State::initialize);
                }
                Cache::State::initialize_inductive(pre.program.state.cache, cache_slots);
            }
            assert(UnifiedCacheJournalRefinement::init_shared_facts(journal_src));
            assert(UnifiedCacheBranchRefinement::init_shared_facts(branch_src));

            UnifiedCacheJournalRefinement::init_refines(pre);
            UnifiedCacheBranchRefinement::init_refines(pre);

            assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(
                journal_src,
            ));
            assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(
                branch_src,
            ));
            assert(CrashAwareCachingDiskJournal::State::initialize(dst.journal)) by {
                assert(CrashAwareCachingDiskJournal::State::init(dst.journal));
                reveal(CrashAwareCachingDiskJournal::State::init);
                reveal(CrashAwareCachingDiskJournal::State::init_by);
                let journal_config = choose |config: CrashAwareCachingDiskJournal::Config|
                    CrashAwareCachingDiskJournal::State::init_by(dst.journal, config);
                match journal_config {
                    CrashAwareCachingDiskJournal::Config::initialize() => {
                        reveal(CrashAwareCachingDiskJournal::State::initialize);
                    },
                    CrashAwareCachingDiskJournal::Config::dummy_to_use_type_params(_) => {
                        assert(false);
                    },
                }
            }
            assert(CrashAwareCachingDiskBranch::State::initialize(dst.branch)) by {
                assert(CrashAwareCachingDiskBranch::State::init(dst.branch));
                reveal(CrashAwareCachingDiskBranch::State::init);
                reveal(CrashAwareCachingDiskBranch::State::init_by);
                let branch_config = choose |config: CrashAwareCachingDiskBranch::Config|
                    CrashAwareCachingDiskBranch::State::init_by(dst.branch, config);
                match branch_config {
                    CrashAwareCachingDiskBranch::Config::initialize() => {
                        reveal(CrashAwareCachingDiskBranch::State::initialize);
                    },
                    CrashAwareCachingDiskBranch::Config::dummy_to_use_type_params(_) => {
                        assert(false);
                    },
                }
            }
            assert(dst.progress == crate::spec::MapSpec_t::AsyncMap::State::init_ephemeral_state());
            assert(dst.sync_reqs == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty());
            assert(dst.superblockstore == SuperblockStore::State{
                persistent: initial_superblock,
                in_flight: Option::None,
                landed: false,
            }) by {
                assert(pre.program.state.in_flight is None);
                assert(!unified_cache_in_flight_superblock_landed(
                    pre.program.state,
                    pre.disk,
                ));
                assert(!unified_cache_superblock_write_pending(pre));
                assert(pre.disk.content[spec_superblock_addr()] == initial_superblock);
            }
            assert(dst.free_aus == free_aus);

            assert(CrashAwareCachingDiskSystem::State::initialize(
                dst,
                free_aus,
                initial_superblock,
                dst.journal,
                dst.branch,
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::initialize);
            }
            assert(CrashAwareCachingDiskSystem::State::init_by(
                dst,
                CrashAwareCachingDiskSystem::Config::initialize(
                    free_aus,
                    initial_superblock,
                    dst.journal,
                    dst.branch,
                ),
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::init_by);
            }
            reveal(CrashAwareCachingDiskSystem::State::init);
            CrashAwareCachingDiskSystem::State::initialize_inductive(
                dst,
                free_aus,
                initial_superblock,
                dst.journal,
                dst.branch,
            );

            assert(UnifiedCacheJournalRefinement::inv(journal_src));
            assert(UnifiedCacheBranchRefinement::inv(branch_src));
            assert(dst.inv());
            assert(inv(pre));
        },
        UnifiedCacheSystem::Config::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }
}

pub proof fn next_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::next(pre, post, lbl),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    reveal(SystemModel::State::next);
    reveal(SystemModel::State::next_by);

    let step = choose |step: SystemModel::Step<UnifiedCacheProgramModel>|
        SystemModel::State::next_by(pre, post, lbl, step);
    match step {
        SystemModel::Step::accept_request() => {
            assume(false);
        },
        SystemModel::Step::deliver_reply() => {
            assume(false);
        },
        SystemModel::Step::program_execute(new_program) => {
            assume(false);
        },
        SystemModel::Step::accept_sync_request() => {
            assume(false);
        },
        SystemModel::Step::program_accept_sync_request(new_program) => {
            assume(false);
        },
        SystemModel::Step::program_deliver_sync_reply(new_program) => {
            assume(false);
        },
        SystemModel::Step::deliver_sync_reply() => {
            assume(false);
        },
        SystemModel::Step::program_disk(new_program, new_disk) => {
            assume(false);
        },
        SystemModel::Step::program_internal(new_program) => {
            assume(false);
        },
        SystemModel::Step::disk_internal(new_disk) => {
            assume(false);
        },
        SystemModel::Step::crash(new_program, new_disk) => {
            assume(false);
        },
        SystemModel::Step::noop() => {
            assume(false);
        },
        SystemModel::Step::dummy_to_use_type_params(_) => {
            assume(false);
        },
    }
}

} // verus!
