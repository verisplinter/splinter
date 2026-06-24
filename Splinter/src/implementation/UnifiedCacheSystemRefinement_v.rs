// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Skeleton refinement boundary:
// SystemModel<UnifiedCacheProgramModel> -> CrashAwareCachingDiskSystem.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::assert_maps_equal;
use vstd::multiset::Multiset;

use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::disk::GenericDisk_v::{Address, AU};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, empty_abstract_superblock_image, marshal_abstract_superblock,
};
use crate::implementation::AnotherAtomicState_v::{AtomicBranchState, AtomicJournalState};
use crate::implementation::Cache_v::Cache;
use crate::implementation::CrashAwareCachingDiskBranch_v::CrashAwareCachingDiskBranch;
use crate::implementation::CrashAwareCachingDiskJournal_v::CrashAwareCachingDiskJournal;
use crate::implementation::CrashAwareCachingDiskSystem_v::{
    CrashAwareCachingDiskSystem, SuperblockStore, singleton_key_seq,
    singleton_message_seq,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::MultisetMapRelation_v::{
    multiset_map_singleton_ensures, multiset_to_map,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_disk_ops_begin_preserves_filled_page,
    cache_disk_ops_begin_refines_caching_disk_internal, cache_filled_addr, cache_filled_page,
    cache_disk_ops_end_refines_caching_disk_internal,
    cache_disk_ops_end_preserves_filled_page,
};
use crate::implementation::CachedBranch_v::LoadedPathReceipt;
use crate::implementation::CachingDiskBranch_v::to_branch_nodes;
use crate::implementation::CachingDisk_v::{CachingDisk, addresses_in_aus};
use crate::implementation::UnifiedCacheBranchRefinement_v as UnifiedCacheBranchRefinement;
use crate::implementation::UnifiedCacheJournalRefinement_v as UnifiedCacheJournalRefinement;
use crate::implementation::UnifiedCacheProgramModel_v::UnifiedCacheProgramModel;
use crate::implementation::UnifiedCacheSystem_v::UnifiedCacheSystem;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::MapSpec_t::{EphemeralState, ID, Input, Reply, Request};
use crate::spec::Messages_t::Message;
use crate::trusted::ProgramModelTrait_t::{
    DiskLabel, DiskModel, ProgramLabel, ProgramModelTrait, ProgramUserOp,
};
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

pub open spec fn system_model_progress_history_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    &&& forall |req: Request| #[trigger] model.requests.contains(req)
        ==> model.id_history.contains(req.id)
    &&& forall |reply: Reply| #[trigger] model.replies.contains(reply)
        ==> model.id_history.contains(reply.id)
}

pub open spec fn system_model_progress_unique_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    &&& forall |req: Request| #[trigger] model.requests.count(req) <= 1
    &&& forall |reply: Reply| #[trigger] model.replies.count(reply) <= 1
}

pub open spec fn system_model_request_id_unique_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    forall |req1: Request, req2: Request| {
        &&& #[trigger] model.requests.contains(req1)
        &&& #[trigger] model.requests.contains(req2)
        &&& req1.id == req2.id
    } ==> req1 == req2
}

pub open spec fn system_model_request_reply_disjoint_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    forall |req: Request, reply: Reply| {
        &&& #[trigger] model.requests.contains(req)
        &&& #[trigger] model.replies.contains(reply)
    } ==> req.id != reply.id
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

pub open spec fn unified_cache_cache_disk_response_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    forall |id: ID| {
        &&& #[trigger] model.disk.responses.contains_key(id)
        &&& model.program.state.outstanding_cache_reqs.contains_key(id)
    } ==> {
        let addr = model.program.state.outstanding_cache_reqs[id];
        let resp = model.disk.responses[id];
        &&& resp is ReadResp ==> {
            &&& model.disk.content.contains_key(addr)
            &&& resp->data == model.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& model.disk.content.contains_key(addr)
            &&& cache_filled_addr(model.program.state.cache, addr)
            &&& model.disk.content[addr] == cache_filled_page(model.program.state.cache, addr)
        }
    }
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

pub open spec fn unified_cache_ready_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    state.client_ready() ==> {
        &&& state.persistent_image is Some
        &&& state.journal.ready()
        &&& state.branch.metadata_loaded()
        &&& state.journal.journal.seq_end() == state.branch.seq_end()
    }
}

pub open spec fn unified_cache_durable_image_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    state.client_ready() ==> {
        &&& state.persistent_image is Some
        &&& state.journal.persistent_seq_end
            <= state.persistent_image.unwrap().journal_seq_end
    }
}

pub open spec fn inv(model: SystemModel::State<UnifiedCacheProgramModel>) -> bool
{
    &&& unified_cache_component_refinement_inv(model)
    &&& unified_cache_superblockstore_refinement_inv(model)
    &&& unified_cache_cache_disk_response_inv(model)
    &&& unified_cache_system_i(model).inv()
    &&& unified_cache_ready_inv(model)
    &&& unified_cache_durable_image_inv(model)
    &&& system_model_progress_history_inv(model)
    &&& system_model_progress_unique_inv(model)
    &&& system_model_request_id_unique_inv(model)
    &&& system_model_request_reply_disjoint_inv(model)
}

pub proof fn program_execute_progress_invs(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
)
    requires
        SystemModel::State::program_execute(pre, post, lbl, new_program),
        inv(pre),
        lbl is ProgramUIOp,
        lbl->op is Execute,
        lbl->op->req.id == lbl->op->reply.id,
    ensures
        system_model_progress_history_inv(post),
        system_model_progress_unique_inv(post),
        system_model_request_id_unique_inv(post),
        system_model_request_reply_disjoint_inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::program_execute);

    let req = lbl->op->req;
    let reply = lbl->op->reply;

    assert(system_model_progress_history_inv(post)) by {
        assert forall |r: Request| #[trigger] post.requests.contains(r)
            implies post.id_history.contains(r.id) by {
            assert(pre.requests.contains(r));
            assert(pre.id_history.contains(r.id));
        }
        assert forall |r: Reply| #[trigger] post.replies.contains(r)
            implies post.id_history.contains(r.id) by {
            if r == reply {
                assert(pre.id_history.contains(req.id));
            } else {
                assert(pre.replies.contains(r));
                assert(pre.id_history.contains(r.id));
            }
        }
    }
    assert(!pre.replies.contains(reply)) by {
        if pre.replies.contains(reply) {
            assert(pre.requests.contains(req));
            assert(system_model_request_reply_disjoint_inv(pre));
            assert(req.id != reply.id);
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post)) by {
        assert forall |r1: Request, r2: Request| {
            &&& #[trigger] post.requests.contains(r1)
            &&& #[trigger] post.requests.contains(r2)
            &&& r1.id == r2.id
        } implies r1 == r2 by {
            assert(pre.requests.contains(r1));
            assert(pre.requests.contains(r2));
            assert(r1 == r2);
        }
    }
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |r: Request, p: Reply| {
            &&& #[trigger] post.requests.contains(r)
            &&& #[trigger] post.replies.contains(p)
        } implies r.id != p.id by {
            assert(pre.requests.contains(r));
            if p == reply {
                if r.id == p.id {
                    assert(p.id == req.id);
                    assert(system_model_request_id_unique_inv(pre));
                    assert(r == req);
                    assert(!post.requests.contains(req));
                    assert(false);
                }
            } else {
                assert(pre.replies.contains(p));
                assert(r.id != p.id);
            }
        }
    }
}

pub proof fn journal_projection_aus_subset_system_journal_owned(
    model: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(model),
        model.program.state.client_ready(),
    ensures
        UnifiedCacheJournalRefinement::unified_cache_journal_source(model).journal_projection_aus()
            <= unified_cache_system_i(model).journal_owned_aus(),
{
    let src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    let system = unified_cache_system_i(model);
    let cj = src.journal_caching_disk_state_i();

    assert(unified_cache_ready_inv(model));
    assert(src.superblock_loaded());
    assert(src.journal.ready());
    assert(system.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(src));
    assert(system.journal.ephemeral is Known);
    assert(system.journal.ephemeral->v == cj);

    cj.loaded_index_values_accessible();
    assert forall |au: AU| #[trigger] src.journal_projection_aus().contains(au)
        implies system.journal_owned_aus().contains(au) by {
        assert(src.journal_projection_aus() == src.journal.owned_aus());
        if src.journal.loaded_index_aus().contains(au) {
            assert(cj.accessible_aus().contains(au));
        } else {
            assert(src.journal.mini_allocator.all_aus().contains(au));
            assert(cj.accessible_aus().contains(au));
        }
    }
}

pub proof fn branch_projection_aus_subset_system_branch_owned(
    model: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(model),
        model.program.state.client_ready(),
    ensures
        UnifiedCacheBranchRefinement::unified_cache_branch_source(model).branch_projection_aus()
            <= unified_cache_system_i(model).branch_owned_aus(),
{
    let src = UnifiedCacheBranchRefinement::unified_cache_branch_source(model);
    let system = unified_cache_system_i(model);
    let cb = src.branch_caching_disk_state_i();

    assert(unified_cache_ready_inv(model));
    assert(src.superblock_loaded());
    assert(src.branch.metadata_loaded());
    assert(system.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(src));
    assert(system.branch.ephemeral is Known);
    assert(system.branch.ephemeral->v == cb);

    cb.metadata_loaded_full_accessible_eq();
    assert forall |au: AU| #[trigger] src.branch_projection_aus().contains(au)
        implies system.branch_owned_aus().contains(au) by {
        assert(src.branch_projection_aus() == src.branch.owned_aus());
        assert(cb.accessible_aus().contains(au));
        assert(cb.full_accessible_aus().contains(au));
    }
}

pub proof fn branch_writes_disjoint_from_journal_projection(
    model: SystemModel::State<UnifiedCacheProgramModel>,
    writes: Set<Address>,
)
    requires
        inv(model),
        model.program.state.client_ready(),
        writes <= addresses_in_aus(
            UnifiedCacheBranchRefinement::unified_cache_branch_source(
                model,
            ).branch_projection_aus(),
        ),
    ensures
        writes.disjoint(addresses_in_aus(
            UnifiedCacheJournalRefinement::unified_cache_journal_source(
                model,
            ).journal_projection_aus(),
        )),
{
    let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    let branch_src = UnifiedCacheBranchRefinement::unified_cache_branch_source(model);
    let system = unified_cache_system_i(model);

    journal_projection_aus_subset_system_journal_owned(model);
    branch_projection_aus_subset_system_branch_owned(model);
    assert(system.allocation_wf());
    assert(system.component_disjoint());
    assert(system.journal_owned_aus().disjoint(system.branch_owned_aus()));

    assert(writes.disjoint(addresses_in_aus(journal_src.journal_projection_aus()))) by {
        assert forall |addr: Address| #[trigger] writes.contains(addr)
            implies !addresses_in_aus(journal_src.journal_projection_aus()).contains(addr) by {
            assert(addresses_in_aus(branch_src.branch_projection_aus()).contains(addr));
            if addresses_in_aus(journal_src.journal_projection_aus()).contains(addr) {
                assert(branch_src.branch_projection_aus().contains(addr.au));
                assert(journal_src.journal_projection_aus().contains(addr.au));
                assert(system.branch_owned_aus().contains(addr.au));
                assert(system.journal_owned_aus().contains(addr.au));
                assert(false);
            }
        }
    }
}

pub proof fn system_i_inv_next(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: CrashAwareCachingDiskSystem::Label,
)
    requires
        inv(pre),
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            lbl,
        ),
    ensures
        unified_cache_system_i(post).inv(),
{
    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.inv());
    CrashAwareCachingDiskSystem::State::inv_next(src, dst, lbl);
}

pub proof fn system_i_noop_next(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        inv(pre),
        unified_cache_system_i(post) == unified_cache_system_i(pre),
        unified_cache_system_i_lbl(pre, post, lbl) is Noop,
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        unified_cache_system_i(post).inv(),
{
    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);

    assert(dst == src);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::noop(),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        reveal(CrashAwareCachingDiskSystem::State::noop);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);
}

pub proof fn cache_resps_coherent_from_disk_response_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    resp_map: Map<ID, DiskResponse>,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        inv(pre),
        resp_map <= pre.disk.responses,
        resp_map.dom() <= pre.program.state.outstanding_cache_reqs.dom(),
        cache_resps == Map::new(
            |addr| pre.program.state.outstanding_cache_reqs.restrict(
                resp_map.dom(),
            ).invert().contains_key(addr),
            |addr| resp_map[
                pre.program.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert()[addr]
            ],
        ),
    ensures
        forall |addr: Address| #[trigger] cache_resps.contains_key(addr) ==> {
            &&& pre.disk.content.contains_key(addr)
            &&& cache_resps[addr] is ReadResp ==> cache_resps[addr]->data
                == pre.disk.content[addr]
            &&& cache_resps[addr] is WriteResp ==> {
                &&& cache_filled_addr(pre.program.state.cache, addr)
                &&& pre.disk.content[addr] == cache_filled_page(pre.program.state.cache, addr)
            }
        },
{
    let state = pre.program.state;
    let restricted = state.outstanding_cache_reqs.restrict(resp_map.dom());
    let finished = restricted.invert();

    assert forall |addr: Address| #[trigger] cache_resps.contains_key(addr) implies {
        &&& pre.disk.content.contains_key(addr)
        &&& cache_resps[addr] is ReadResp ==> cache_resps[addr]->data
            == pre.disk.content[addr]
        &&& cache_resps[addr] is WriteResp ==> {
            &&& cache_filled_addr(pre.program.state.cache, addr)
            &&& pre.disk.content[addr] == cache_filled_page(pre.program.state.cache, addr)
        }
    } by {
        assert(finished.contains_key(addr));
        assert(restricted.contains_value(addr)) by {
            assert(finished.contains_key(addr));
        }
        Cache::State::invert_contains_pair(restricted, addr);
        let id = finished[addr];
        assert(restricted.contains_pair(id, addr));
        assert(resp_map.contains_key(id));
        assert(state.outstanding_cache_reqs.contains_key(id));
        assert(state.outstanding_cache_reqs[id] == addr);
        assert(cache_resps[addr] == resp_map[id]);
        assert(pre.disk.responses.contains_key(id));
        assert(pre.disk.responses[id] == resp_map[id]);
        assert(unified_cache_cache_disk_response_inv(pre));
    }
}

pub proof fn cache_io_begin_preserves_cache_disk_response_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        inv(pre),
        post.disk.responses == pre.disk.responses,
        post.disk.content == pre.disk.content,
        req_map.dom().disjoint(pre.disk.responses.dom()),
        post.program.state.outstanding_cache_reqs == pre.program.state.outstanding_cache_reqs
            .union_prefer_right(Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr())),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
        ),
    ensures
        unified_cache_cache_disk_response_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    assert forall |id: ID| {
        &&& #[trigger] post.disk.responses.contains_key(id)
        &&& post.program.state.outstanding_cache_reqs.contains_key(id)
    } implies {
        let addr = post.program.state.outstanding_cache_reqs[id];
        let resp = post.disk.responses[id];
        &&& resp is ReadResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& resp->data == post.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& cache_filled_addr(post.program.state.cache, addr)
            &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
        }
    } by {
        assert(pre.disk.responses.contains_key(id));
        assert(!req_map.contains_key(id));
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(post_state.outstanding_cache_reqs[id]
            == pre_state.outstanding_cache_reqs[id]);
        let addr = pre_state.outstanding_cache_reqs[id];
        assert(unified_cache_cache_disk_response_inv(pre));
        assert(post.disk.responses[id] == pre.disk.responses[id]);
        assert(post.disk.content == pre.disk.content);
        if pre.disk.responses[id] is WriteResp {
            cache_disk_ops_begin_preserves_filled_page(
                pre_state.cache,
                post_state.cache,
                req_map.values(),
                addr,
            );
        }
    }
}

pub proof fn cache_io_end_preserves_cache_disk_response_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    resp_map: Map<ID, DiskResponse>,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        inv(pre),
        post.disk.responses == pre.disk.responses.remove_keys(resp_map.dom()),
        post.disk.content == pre.disk.content,
        post.program.state.outstanding_cache_reqs == pre.program.state.outstanding_cache_reqs
            .remove_keys(resp_map.dom()),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps},
        ),
    ensures
        unified_cache_cache_disk_response_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    assert forall |id: ID| {
        &&& #[trigger] post.disk.responses.contains_key(id)
        &&& post.program.state.outstanding_cache_reqs.contains_key(id)
    } implies {
        let addr = post.program.state.outstanding_cache_reqs[id];
        let resp = post.disk.responses[id];
        &&& resp is ReadResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& resp->data == post.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& cache_filled_addr(post.program.state.cache, addr)
            &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
        }
    } by {
        assert(!resp_map.contains_key(id));
        assert(pre.disk.responses.contains_key(id));
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(post_state.outstanding_cache_reqs[id]
            == pre_state.outstanding_cache_reqs[id]);
        let addr = pre_state.outstanding_cache_reqs[id];
        assert(unified_cache_cache_disk_response_inv(pre));
        assert(post.disk.responses[id] == pre.disk.responses[id]);
        assert(post.disk.content == pre.disk.content);
        if pre.disk.responses[id] is WriteResp {
            cache_disk_ops_end_preserves_filled_page(
                pre_state.cache,
                post_state.cache,
                cache_resps,
                addr,
            );
        }
    }
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
            assert(!pre.program.state.client_ready());
            assert(unified_cache_durable_image_inv(pre));
            assert(inv(pre));
        },
        UnifiedCacheSystem::Config::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }
}

pub proof fn accept_request_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::accept_request(pre, post, lbl),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::accept_request);

    assert(lbl is AcceptRequest);
    let req = lbl->req;

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);

    assert(dst.progress.requests == src.progress.requests.insert(req));
    assert(!src.progress.requests.contains(req));
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskSystem::Label::Request{req},
        CrashAwareCachingDiskSystem::Step::accept_request(),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        reveal(CrashAwareCachingDiskSystem::State::accept_request);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    assert(system_model_progress_history_inv(post)) by {
        assert forall |r: Request| #[trigger] post.requests.contains(r)
            implies post.id_history.contains(r.id) by {
            if r == req {
                assert(post.id_history.contains(req.id));
            } else {
                assert(pre.requests.contains(r));
                assert(pre.id_history.contains(r.id));
                assert(post.id_history.contains(r.id));
            }
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post)) by {
        assert forall |r1: Request, r2: Request| {
            &&& #[trigger] post.requests.contains(r1)
            &&& #[trigger] post.requests.contains(r2)
            &&& r1.id == r2.id
        } implies r1 == r2 by {
            if r1 == req || r2 == req {
                assert(pre.fresh_id(req.id));
                if r1 == req && r2 != req {
                    assert(pre.requests.contains(r2));
                    assert(pre.id_history.contains(r2.id));
                    assert(false);
                } else if r2 == req && r1 != req {
                    assert(pre.requests.contains(r1));
                    assert(pre.id_history.contains(r1.id));
                    assert(false);
                }
            } else {
                assert(pre.requests.contains(r1));
                assert(pre.requests.contains(r2));
                assert(r1 == r2);
            }
        }
    }
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |r: Request, p: Reply| {
            &&& #[trigger] post.requests.contains(r)
            &&& #[trigger] post.replies.contains(p)
        } implies r.id != p.id by {
            if r == req {
                assert(pre.fresh_id(req.id));
                assert(pre.replies.contains(p));
                assert(pre.id_history.contains(p.id));
            } else {
                assert(pre.requests.contains(r));
                assert(pre.replies.contains(p));
                assert(r.id != p.id);
            }
        }
    }
    assert(post.program == pre.program);
    assert(unified_cache_durable_image_inv(post));
    assert(inv(post));
}

pub proof fn deliver_reply_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::deliver_reply(),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::next_by);

    assert(lbl is DeliverReply);
    let reply = lbl->reply;

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);

    assert(dst.progress.replies == src.progress.replies.remove(reply));
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskSystem::Label::Reply{reply},
        CrashAwareCachingDiskSystem::Step::deliver_reply(),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        reveal(CrashAwareCachingDiskSystem::State::deliver_reply);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    assert(system_model_progress_history_inv(post)) by {
        assert forall |r: Reply| #[trigger] post.replies.contains(r)
            implies post.id_history.contains(r.id) by {
            assert(pre.replies.contains(r));
            assert(pre.id_history.contains(r.id));
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post)) by {
        assert forall |r1: Request, r2: Request| {
            &&& #[trigger] post.requests.contains(r1)
            &&& #[trigger] post.requests.contains(r2)
            &&& r1.id == r2.id
        } implies r1 == r2 by {
            assert(pre.requests.contains(r1));
            assert(pre.requests.contains(r2));
            assert(r1 == r2);
        }
    }
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |r: Request, p: Reply| {
            &&& #[trigger] post.requests.contains(r)
            &&& #[trigger] post.replies.contains(p)
        } implies r.id != p.id by {
            assert(pre.requests.contains(r));
            assert(pre.replies.contains(p));
            assert(r.id != p.id);
        }
    }
    assert(post.program == pre.program);
    assert(unified_cache_durable_image_inv(post));
    assert(inv(post));
}

pub proof fn program_execute_noop_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
)
    requires
        SystemModel::State::program_execute(pre, post, lbl, new_program),
        inv(pre),
        lbl is ProgramUIOp,
        lbl->op is Execute,
        lbl->op->req.input is NoopInput,
        UnifiedCacheSystem::State::execute_noop(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Execute{
                req: lbl->op->req,
                reply: lbl->op->reply,
            },
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::program_execute);
    reveal(UnifiedCacheSystem::State::execute_noop);

    let req = lbl->op->req;
    let reply = lbl->op->reply;
    let target_lbl = CrashAwareCachingDiskSystem::Label::Execute{req, reply};
    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);

    assert(src.progress.requests.contains(req));
    assert(!src.progress.replies.contains(reply)) by {
        if src.progress.replies.contains(reply) {
            assert(pre.replies.contains(reply));
            assert(system_model_request_reply_disjoint_inv(pre));
            assert(req.id != reply.id);
        }
    }
    assert(dst.progress.requests == src.progress.requests.remove(req));
    assert(dst.progress.replies == src.progress.replies.insert(reply));
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::execute_noop(),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        reveal(CrashAwareCachingDiskSystem::State::execute_noop);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);

    assert(req.id == reply.id);
    program_execute_progress_invs(pre, post, lbl, new_program);
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post.program.state == pre.program.state);
    }
    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    system_i_inv_next(pre, post, target_lbl);
    assert(inv(post));
}

pub proof fn program_execute_put_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_branch: AtomicBranchState::State,
)
    requires
        SystemModel::State::program_execute(pre, post, lbl, new_program),
        inv(pre),
        lbl is ProgramUIOp,
        lbl->op is Execute,
        lbl->op->req.input is PutInput,
        UnifiedCacheSystem::State::execute_put(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Execute{
                req: lbl->op->req,
                reply: lbl->op->reply,
            },
            new_cache,
            new_journal,
            receipt,
            init_root,
            reads,
            writes,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::program_execute);
    reveal(UnifiedCacheSystem::State::execute_put);

    let req = lbl->op->req;
    let reply = lbl->op->reply;
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let source_lbl = UnifiedCacheSystem::Label::Execute{req, reply};
    let target_lbl = CrashAwareCachingDiskSystem::Label::Execute{req, reply};
    let key = req.input.arrow_PutInput_key();
    let value = req.input.arrow_PutInput_value();
    let msg = Message::Define{value};
    let keyed_message = KeyedMessage{key, message: msg};
    let records = MsgHistory::singleton_at(pre_state.branch.seq_end(), keyed_message);
    let keys = singleton_key_seq(key);
    let msgs = singleton_message_seq(msg);
    let cache_lbl = Cache::Label::Access{reads, writes};
    let journal_atomic_lbl = AtomicJournalState::Label::Put{messages: records};
    let branch_atomic_lbl = AtomicBranchState::Label::Append{
        keys,
        msgs,
        receipt,
        init_root,
        read_nodes: to_branch_nodes(reads),
        write_nodes: to_branch_nodes(writes),
    };

    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(pre_state.client_ready());
    assert(unified_cache_ready_inv(pre));
    assert(journal_pre.superblock_loaded());
    assert(branch_pre.superblock_loaded());
    assert(journal_pre.journal.ready());
    assert(branch_pre.branch.metadata_loaded());
    assert(AtomicJournalState::State::next(
        pre_state.journal,
        post_state.journal,
        journal_atomic_lbl,
    ));
    assert(AtomicBranchState::State::next(
        pre_state.branch,
        post_state.branch,
        branch_atomic_lbl,
    ));

    UnifiedCacheJournalRefinement::put_preserves_projection_aus(
        journal_pre,
        journal_post,
        records,
    );
    AtomicBranchState::State::append_effect(pre_state.branch, post_state.branch, branch_atomic_lbl);
    assert(post_state.in_flight == pre_state.in_flight);
    assert(post_state.journal.in_flight == pre_state.journal.in_flight);
    assert(post_state.branch.in_flight == pre_state.branch.in_flight);
    assert(journal_post.in_flight_image == journal_pre.in_flight_image) by {
        if pre_state.in_flight is Some {
            assert(post_state.atomic_inflight_superblock_i()
                == pre_state.atomic_inflight_superblock_i());
        }
    }
    assert(branch_post.in_flight_image == branch_pre.in_flight_image) by {
        if pre_state.in_flight is Some {
            assert(post_state.atomic_inflight_superblock_i()
                == pre_state.atomic_inflight_superblock_i());
        }
    }

    UnifiedCacheBranchRefinement::append_refines(
        branch_pre,
        branch_post,
        keys,
        msgs,
        receipt,
        init_root,
        reads,
        writes,
    );
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(writes.dom() <= addresses_in_aus(branch_pre.branch_projection_aus()));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    branch_writes_disjoint_from_journal_projection(pre, writes.dom());
    journal_pre.journal_caching_disk_i_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        reads,
        writes,
    );
    assert(journal_post.journal_caching_disk_i() == journal_pre.journal_caching_disk_i());

    UnifiedCacheJournalRefinement::put_refines(journal_pre, journal_post, records);
    assert(UnifiedCacheJournalRefinement::inv(journal_post));

    assert(src.branch.ephemeral is Known);
    assert(src.branch.ephemeral->v == branch_pre.branch_caching_disk_state_i());
    assert(src.branch_lsn() == pre_state.branch.seq_end());
    assert(records == MsgHistory::singleton_at(src.branch_lsn(), keyed_message));
    assert(keys == singleton_key_seq(key));
    assert(msgs == singleton_message_seq(msg));

    assert(src.progress.requests.contains(req));
    assert(!src.progress.replies.contains(reply)) by {
        if src.progress.replies.contains(reply) {
            assert(pre.replies.contains(reply));
            assert(system_model_request_reply_disjoint_inv(pre));
            assert(req.id != reply.id);
        }
    }
    assert(dst.progress.requests == src.progress.requests.remove(req));
    assert(dst.progress.replies == src.progress.replies.insert(reply));

    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::put(dst.journal, dst.branch),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        reveal(CrashAwareCachingDiskSystem::State::put);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);

    assert(req.id == reply.id);
    program_execute_progress_invs(pre, post, lbl, new_program);
    assert(unified_cache_ready_inv(post)) by {
        if post_state.client_ready() {
            assert(pre_state.client_ready());
            assert(post_state.persistent_image == pre_state.persistent_image);
            assert(post_state.persistent_image is Some);
            assert(post_state.journal.ready());
            assert(post_state.branch.metadata_loaded());
            assert(post_state.journal.journal.seq_end() == records.seq_end);
            assert(post_state.branch.seq_end() == pre_state.branch.seq_end() + keys.len());
            assert(keys.len() == 1);
            assert(records.seq_end == pre_state.branch.seq_end() + 1);
            assert(post_state.journal.journal.seq_end() == post_state.branch.seq_end());
        }
    }
    assert(unified_cache_durable_image_inv(post)) by {
        if post_state.client_ready() {
            assert(unified_cache_durable_image_inv(pre));
            assert(post_state.persistent_image == pre_state.persistent_image);
            assert(post_state.journal.persistent_seq_end
                == pre_state.journal.persistent_seq_end);
        }
    }
    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    system_i_inv_next(pre, post, target_lbl);
    assert(inv(post));
}

pub proof fn program_execute_query_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_cache: Cache::State,
    msg: crate::spec::Messages_t::Message,
    receipts: Seq<crate::implementation::CachedBranch_v::LoadedPathReceipt>,
    reads: Map<crate::disk::GenericDisk_v::Address, crate::spec::AsyncDisk_t::RawPage>,
)
    requires
        SystemModel::State::program_execute(pre, post, lbl, new_program),
        inv(pre),
        lbl is ProgramUIOp,
        lbl->op is Execute,
        lbl->op->req.input is QueryInput,
        UnifiedCacheSystem::State::execute_query(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Execute{
                req: lbl->op->req,
                reply: lbl->op->reply,
            },
            new_cache,
            msg,
            receipts,
            reads,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::program_execute);
    reveal(UnifiedCacheSystem::State::execute_query);

    let req = lbl->op->req;
    let reply = lbl->op->reply;
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let source_lbl = UnifiedCacheSystem::Label::Execute{req, reply};
    let target_lbl = CrashAwareCachingDiskSystem::Label::Execute{req, reply};
    let key = req.input.arrow_QueryInput_key();
    let value = reply.output.arrow_QueryOutput_value();
    let cache_lbl = Cache::Label::Access{
        reads,
        writes: Map::empty(),
    };

    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);
    journal_pre.inv_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        reads,
        Map::empty(),
    );
    assert(UnifiedCacheJournalRefinement::inv(journal_post));

    assert(reads.dom() == crate::implementation::AnotherAtomicState_v::query_receipts_read_addrs(
        receipts,
        receipts.len() as nat,
    ));
    UnifiedCacheBranchRefinement::query_refines(
        branch_pre,
        branch_post,
        key,
        value,
        msg,
        receipts,
        reads,
    );
    assert(UnifiedCacheBranchRefinement::inv(branch_post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.progress.requests.contains(req));
    assert(!src.progress.replies.contains(reply)) by {
        if src.progress.replies.contains(reply) {
            assert(pre.replies.contains(reply));
            assert(system_model_request_reply_disjoint_inv(pre));
            assert(req.id != reply.id);
        }
    }
    assert(dst.progress.requests == src.progress.requests.remove(req));
    assert(dst.progress.replies == src.progress.replies.insert(reply));

    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::query(dst.branch),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        reveal(CrashAwareCachingDiskSystem::State::query);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);

    assert(req.id == reply.id);
    program_execute_progress_invs(pre, post, lbl, new_program);
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post)) by {
        if post.program.state.client_ready() {
            assert(unified_cache_durable_image_inv(pre));
            assert(post.program.state.persistent_image == pre.program.state.persistent_image);
            assert(post.program.state.journal == pre.program.state.journal);
        }
    }
    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    system_i_inv_next(pre, post, target_lbl);
    assert(inv(post));
}

pub proof fn program_execute_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_execute(new_program),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    reveal(SystemModel::State::next_by);
    assert(lbl is ProgramUIOp);
    assert(lbl->op is Execute);
    assert(SystemModel::State::program_execute(pre, post, lbl, new_program));
    let req = lbl->op->req;
    let reply = lbl->op->reply;
    let source_lbl = UnifiedCacheSystem::Label::Execute{req, reply};
    assert(UnifiedCacheProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::UserIO{op: lbl->op},
    ));
    assert(UnifiedCacheSystem::State::next(
        pre.program.state,
        post.program.state,
        source_lbl,
    ));
    reveal(UnifiedCacheSystem::State::next);
    reveal(UnifiedCacheSystem::State::next_by);
    let unified_step = choose |step: UnifiedCacheSystem::Step|
        UnifiedCacheSystem::State::next_by(
            pre.program.state,
            post.program.state,
            source_lbl,
            step,
        );
    match req.input {
        Input::NoopInput => {
            match unified_step {
                UnifiedCacheSystem::Step::execute_noop() => {
                    assert(UnifiedCacheSystem::State::execute_noop(
                        pre.program.state,
                        post.program.state,
                        source_lbl,
                    )) by {
                        reveal(UnifiedCacheSystem::State::execute_noop);
                    }
                    program_execute_noop_refines(pre, post, lbl, new_program);
                },
                _ => {
                    assert(false);
                },
            }
        },
        Input::PutInput{..} => {
            match unified_step {
                UnifiedCacheSystem::Step::execute_put(
                    new_cache,
                    new_journal,
                    receipt,
                    init_root,
                    reads,
                    writes,
                    new_branch,
                ) => {
                    assert(UnifiedCacheSystem::State::execute_put(
                        pre.program.state,
                        post.program.state,
                        source_lbl,
                        new_cache,
                        new_journal,
                        receipt,
                        init_root,
                        reads,
                        writes,
                        new_branch,
                    ));
                    program_execute_put_refines(
                        pre,
                        post,
                        lbl,
                        new_program,
                        new_cache,
                        new_journal,
                        receipt,
                        init_root,
                        reads,
                        writes,
                        new_branch,
                    );
                },
                _ => {
                    assert(false);
                },
            }
        },
        Input::QueryInput{..} => {
            match unified_step {
                UnifiedCacheSystem::Step::execute_query(new_cache, msg, receipts, reads) => {
                    assert(UnifiedCacheSystem::State::execute_query(
                        pre.program.state,
                        post.program.state,
                        source_lbl,
                        new_cache,
                        msg,
                        receipts,
                        reads,
                    ));
                    program_execute_query_refines(
                        pre,
                        post,
                        lbl,
                        new_program,
                        new_cache,
                        msg,
                        receipts,
                        reads,
                    );
                },
                _ => {
                    assert(false);
                },
            }
        },
    }
}

pub proof fn accept_sync_request_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::accept_sync_request(),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::accept_sync_request(pre, post, lbl));
    reveal(SystemModel::State::accept_sync_request);

    assert(lbl is AcceptSyncRequest);
    let sync_req_id = match lbl {
        SystemModel::Label::AcceptSyncRequest{sync_req_id} => sync_req_id,
        _ => {
            assert(false);
            arbitrary()
        },
    };
    assert(unified_cache_system_i_lbl(pre, post, lbl) == CrashAwareCachingDiskSystem::Label::Noop);

    assert(post.program == pre.program);
    assert(post.disk == pre.disk);
    assert(post.requests == pre.requests);
    assert(post.replies == pre.replies);
    assert(post.sync_replies == pre.sync_replies);
    assert(post.id_history == pre.id_history.insert(sync_req_id));
    assert(unified_cache_system_i(post) == unified_cache_system_i(pre));
    system_i_noop_next(pre, post, lbl);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post));
    assert(system_model_progress_history_inv(post)) by {
        assert forall |req: Request| #[trigger] post.requests.contains(req)
            implies post.id_history.contains(req.id) by {
            assert(pre.requests.contains(req));
            assert(pre.id_history.contains(req.id));
        }
        assert forall |reply: Reply| #[trigger] post.replies.contains(reply)
            implies post.id_history.contains(reply.id) by {
            assert(pre.replies.contains(reply));
            assert(pre.id_history.contains(reply.id));
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post)) by {
        assert forall |req1: Request, req2: Request| {
            &&& #[trigger] post.requests.contains(req1)
            &&& #[trigger] post.requests.contains(req2)
            &&& req1.id == req2.id
        } implies req1 == req2 by {
            assert(pre.requests.contains(req1));
            assert(pre.requests.contains(req2));
            assert(req1 == req2);
        }
    }
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |req: Request, reply: Reply| {
            &&& #[trigger] post.requests.contains(req)
            &&& #[trigger] post.replies.contains(reply)
        } implies req.id != reply.id by {
            assert(pre.requests.contains(req));
            assert(pre.replies.contains(reply));
            assert(req.id != reply.id);
        }
    }
    assert(inv(post));
}

pub proof fn program_accept_sync_request_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_accept_sync_request(new_program),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::program_accept_sync_request(pre, post, lbl, new_program));
    reveal(SystemModel::State::program_accept_sync_request);

    assert(lbl is ProgramUIOp);
    assert(lbl->op is AcceptSyncRequest);
    let sync_req_id = match lbl->op {
        ProgramUserOp::AcceptSyncRequest{sync_req_id} => sync_req_id,
        _ => {
            assert(false);
            arbitrary()
        },
    };
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let source_lbl = UnifiedCacheSystem::Label::AcceptSyncRequest{sync_req_id};
    let target_lbl = CrashAwareCachingDiskSystem::Label::ReqSync{sync_req_id};
    let end_lsn = pre_state.branch.seq_end();

    assert(UnifiedCacheProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::UserIO{op: lbl->op},
    ));
    assert(UnifiedCacheSystem::State::next(pre_state, post_state, source_lbl));
    reveal(UnifiedCacheSystem::State::next);
    reveal(UnifiedCacheSystem::State::next_by);
    let unified_step = choose |step: UnifiedCacheSystem::Step|
        UnifiedCacheSystem::State::next_by(pre_state, post_state, source_lbl, step);
    match unified_step {
        UnifiedCacheSystem::Step::accept_sync_request() => {
            assert(UnifiedCacheSystem::State::accept_sync_request(
                pre_state,
                post_state,
                source_lbl,
            )) by {
                reveal(UnifiedCacheSystem::State::accept_sync_request);
            }
        },
        _ => {
            assert(false);
        },
    }

    assert(pre_state.client_ready());
    assert(unified_cache_ready_inv(pre));
    assert(pre_state.journal.ready());
    assert(pre_state.branch.metadata_loaded());
    assert(pre_state.journal.journal.seq_end() == pre_state.branch.seq_end());
    assert(post_state == UnifiedCacheSystem::State{
        sync_req_map: pre_state.sync_req_map.insert(sync_req_id, end_lsn),
        ..pre_state
    });

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_post == journal_pre);
    assert(journal_pre.superblock_loaded());
    assert(journal_pre.journal.ready());
    assert(end_lsn == journal_pre.journal.journal.seq_end());
    UnifiedCacheJournalRefinement::query_end_lsn_self_refines(journal_pre, end_lsn);
    assert(UnifiedCacheJournalRefinement::inv(journal_post));

    assert(branch_post == branch_pre);
    assert(UnifiedCacheBranchRefinement::inv(branch_post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.branch.ephemeral is Known);
    assert(src.branch.ephemeral->v == branch_pre.branch_caching_disk_state_i());
    assert(src.branch_lsn() == end_lsn);
    assert(!src.sync_reqs.dom().contains(sync_req_id));
    assert(dst.sync_reqs == src.sync_reqs.insert(sync_req_id, src.branch_lsn()));
    assert(dst.journal == src.journal);
    assert(dst.branch == src.branch);
    assert(dst.progress == src.progress);
    assert(dst.superblockstore == src.superblockstore);
    assert(dst.free_aus == src.free_aus);

    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::req_sync(),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        reveal(CrashAwareCachingDiskSystem::State::req_sync);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
    }
    assert(system_model_progress_history_inv(post)) by {
        assert forall |req: Request| #[trigger] post.requests.contains(req)
            implies post.id_history.contains(req.id) by {
            assert(pre.requests.contains(req));
            assert(pre.id_history.contains(req.id));
        }
        assert forall |reply: Reply| #[trigger] post.replies.contains(reply)
            implies post.id_history.contains(reply.id) by {
            assert(pre.replies.contains(reply));
            assert(pre.id_history.contains(reply.id));
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post)) by {
        assert forall |req1: Request, req2: Request| {
            &&& #[trigger] post.requests.contains(req1)
            &&& #[trigger] post.requests.contains(req2)
            &&& req1.id == req2.id
        } implies req1 == req2 by {
            assert(pre.requests.contains(req1));
            assert(pre.requests.contains(req2));
            assert(req1 == req2);
        }
    }
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |req: Request, reply: Reply| {
            &&& #[trigger] post.requests.contains(req)
            &&& #[trigger] post.replies.contains(reply)
        } implies req.id != reply.id by {
            assert(pre.requests.contains(req));
            assert(pre.replies.contains(reply));
            assert(req.id != reply.id);
        }
    }
    system_i_inv_next(pre, post, target_lbl);
    assert(inv(post));
}

pub proof fn program_deliver_sync_reply_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_deliver_sync_reply(new_program),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::program_deliver_sync_reply(pre, post, lbl, new_program));
    reveal(SystemModel::State::program_deliver_sync_reply);

    assert(lbl is ProgramUIOp);
    assert(lbl->op is DeliverSyncReply);
    let sync_req_id = match lbl->op {
        ProgramUserOp::DeliverSyncReply{sync_req_id} => sync_req_id,
        _ => {
            assert(false);
            arbitrary()
        },
    };
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let source_lbl = UnifiedCacheSystem::Label::DeliverSyncReply{sync_req_id};
    let target_lbl = CrashAwareCachingDiskSystem::Label::ReplySync{sync_req_id};
    let sync_lsn = pre_state.sync_req_map[sync_req_id];

    assert(UnifiedCacheProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::UserIO{op: lbl->op},
    ));
    assert(UnifiedCacheSystem::State::next(pre_state, post_state, source_lbl));
    reveal(UnifiedCacheSystem::State::next);
    reveal(UnifiedCacheSystem::State::next_by);
    let unified_step = choose |step: UnifiedCacheSystem::Step|
        UnifiedCacheSystem::State::next_by(pre_state, post_state, source_lbl, step);
    match unified_step {
        UnifiedCacheSystem::Step::deliver_sync_reply() => {
            assert(UnifiedCacheSystem::State::deliver_sync_reply(
                pre_state,
                post_state,
                source_lbl,
            )) by {
                reveal(UnifiedCacheSystem::State::deliver_sync_reply);
            }
        },
        _ => {
            assert(false);
        },
    }

    assert(pre_state.client_ready());
    assert(pre_state.sync_req_map.contains_key(sync_req_id));
    assert(sync_lsn <= pre_state.journal.persistent_seq_end);
    assert(post_state == UnifiedCacheSystem::State{
        sync_req_map: pre_state.sync_req_map.remove(sync_req_id),
        ..pre_state
    });

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_post == journal_pre);
    assert(unified_cache_durable_image_inv(pre));
    assert(journal_pre.superblock_loaded());
    assert(UnifiedCacheJournalRefinement::unified_cache_journal_i(
        journal_pre,
    ).persistent.metadata().seq_end == pre_state.persistent_image.unwrap().journal_seq_end);
    assert(sync_lsn <= pre_state.persistent_image.unwrap().journal_seq_end);
    assert(sync_lsn <= UnifiedCacheJournalRefinement::unified_cache_journal_i(
        journal_pre,
    ).persistent.metadata().seq_end);
    UnifiedCacheJournalRefinement::query_lsn_persistence_self_refines(journal_pre, sync_lsn);
    assert(UnifiedCacheJournalRefinement::inv(journal_post));

    assert(branch_post == branch_pre);
    assert(UnifiedCacheBranchRefinement::inv(branch_post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.sync_reqs.dom().contains(sync_req_id));
    assert(sync_lsn == src.sync_reqs[sync_req_id]);
    assert(dst.sync_reqs == src.sync_reqs.remove(sync_req_id));
    assert(dst.journal == src.journal);
    assert(dst.branch == src.branch);
    assert(dst.progress == src.progress);
    assert(dst.superblockstore == src.superblockstore);
    assert(dst.free_aus == src.free_aus);

    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::reply_sync(),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
        reveal(CrashAwareCachingDiskSystem::State::reply_sync);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
    }
    assert(system_model_progress_history_inv(post)) by {
        assert forall |req: Request| #[trigger] post.requests.contains(req)
            implies post.id_history.contains(req.id) by {
            assert(pre.requests.contains(req));
            assert(pre.id_history.contains(req.id));
        }
        assert forall |reply: Reply| #[trigger] post.replies.contains(reply)
            implies post.id_history.contains(reply.id) by {
            assert(pre.replies.contains(reply));
            assert(pre.id_history.contains(reply.id));
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post)) by {
        assert forall |req1: Request, req2: Request| {
            &&& #[trigger] post.requests.contains(req1)
            &&& #[trigger] post.requests.contains(req2)
            &&& req1.id == req2.id
        } implies req1 == req2 by {
            assert(pre.requests.contains(req1));
            assert(pre.requests.contains(req2));
            assert(req1 == req2);
        }
    }
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |req: Request, reply: Reply| {
            &&& #[trigger] post.requests.contains(req)
            &&& #[trigger] post.replies.contains(reply)
        } implies req.id != reply.id by {
            assert(pre.requests.contains(req));
            assert(pre.replies.contains(reply));
            assert(req.id != reply.id);
        }
    }
    system_i_inv_next(pre, post, target_lbl);
    assert(inv(post));
}

pub proof fn deliver_sync_reply_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::deliver_sync_reply(),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::deliver_sync_reply(pre, post, lbl));
    reveal(SystemModel::State::deliver_sync_reply);

    assert(lbl is DeliverSyncReply);
    assert(unified_cache_system_i_lbl(pre, post, lbl) == CrashAwareCachingDiskSystem::Label::Noop);

    assert(post.program == pre.program);
    assert(post.disk == pre.disk);
    assert(post.requests == pre.requests);
    assert(post.replies == pre.replies);
    assert(post.sync_requests == pre.sync_requests);
    assert(post.id_history == pre.id_history);
    assert(unified_cache_system_i(post) == unified_cache_system_i(pre));
    system_i_noop_next(pre, post, lbl);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post));
    assert(system_model_progress_history_inv(post)) by {
        assert forall |req: Request| #[trigger] post.requests.contains(req)
            implies post.id_history.contains(req.id) by {
            assert(pre.requests.contains(req));
            assert(pre.id_history.contains(req.id));
        }
        assert forall |reply: Reply| #[trigger] post.replies.contains(reply)
            implies post.id_history.contains(reply.id) by {
            assert(pre.replies.contains(reply));
            assert(pre.id_history.contains(reply.id));
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post)) by {
        assert forall |req1: Request, req2: Request| {
            &&& #[trigger] post.requests.contains(req1)
            &&& #[trigger] post.requests.contains(req2)
            &&& req1.id == req2.id
        } implies req1 == req2 by {
            assert(pre.requests.contains(req1));
            assert(pre.requests.contains(req2));
            assert(req1 == req2);
        }
    }
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |req: Request, reply: Reply| {
            &&& #[trigger] post.requests.contains(req)
            &&& #[trigger] post.replies.contains(reply)
        } implies req.id != reply.id by {
            assert(pre.requests.contains(req));
            assert(pre.replies.contains(reply));
            assert(req.id != reply.id);
        }
    }
    assert(inv(post));
}

pub proof fn program_disk_initiate_recovery_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    req_id: ID,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk),
        inv(pre),
        UnifiedCacheProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheSystem::Step::initiate_recovery(req_id, reqs, resps),
            lbl->info,
        ),
        UnifiedCacheSystem::State::initiate_recovery(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            req_id,
            reqs,
            resps,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };
    let read_req = DiskRequest::ReadReq{from: spec_superblock_addr()};
    let req_map = Map::empty().insert(req_id, read_req);

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheSystem::State::initiate_recovery);

    assert(lbl is ProgramDiskOp);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs == Multiset::empty().insert((req_id, read_req)));
    assert(resps.is_empty());
    multiset_map_singleton_ensures(req_id, read_req);
    assert(multiset_to_map(reqs) == req_map);
    assert(multiset_to_map(resps) == Map::<ID, DiskResponse>::empty()) by {
        assert_maps_equal!(
            multiset_to_map(resps),
            Map::<ID, DiskResponse>::empty(),
            id => {
                if multiset_to_map(resps).contains_key(id) {
                    let pr = choose |pr| #[trigger] resps.contains(pr) && pr.0 == id;
                    assert(resps.contains(pr));
                    assert(false);
                }
            }
        );
    }
    assert(disk_lbl->requests == req_map);
    assert(disk_lbl->responses == Map::<ID, DiskResponse>::empty());
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(pre.disk, post.disk, disk_lbl)) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
        match disk_step {
            AsyncDisk::Step::disk_ops() => {},
            _ => { assert(false); },
        }
    }
    assert(post.disk.content == pre.disk.content) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    assert(post.disk.responses == pre.disk.responses) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    assert(post.disk.requests == pre.disk.requests.union_prefer_right(req_map)) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    crate::spec::AsyncDisk_t::inv_next(pre.disk, post.disk, disk_lbl);
    assert(post.disk.inv());

    assert(post_state == UnifiedCacheSystem::State{
        recovery_state: RecoveryState::AwaitingSuperblock,
        ..pre_state
    });
    assert(post_state.cache == pre_state.cache);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    assert(post_state.journal == pre_state.journal);
    assert(post_state.branch == pre_state.branch);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.in_flight == pre_state.in_flight);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(!post_state.client_ready());

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_pre.same_except_cache_and_disk(journal_post));
    assert(branch_pre.same_except_cache_and_disk(branch_post));
    assert(journal_post.cache == journal_pre.cache);
    assert(branch_post.cache == branch_pre.cache);
    assert(journal_post.disk.content == journal_pre.disk.content);
    assert(branch_post.disk.content == branch_pre.disk.content);
    journal_pre.unchanged_by_same_cache_and_disk_content(journal_post);
    branch_pre.unchanged_by_same_cache_and_disk_content(branch_post);
    assert(UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post)
        == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post)
        == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(unified_cache_component_refinement_inv(post));

    assert(unified_cache_system_i(post) == unified_cache_system_i(pre)) by {
        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        assert(dst.journal == src.journal);
        assert(dst.branch == src.branch);
        assert(dst.progress == src.progress);
        assert(dst.sync_reqs == src.sync_reqs);
        assert(dst.free_aus == src.free_aus);
        assert(dst.superblockstore == src.superblockstore) by {
            assert(post_state.in_flight == pre_state.in_flight);
            assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
            if pre_state.in_flight is Some {
                let in_flight_req_id = pre_state.in_flight.unwrap().req_id;
                if pre.disk.requests.contains_key(in_flight_req_id) {
                    assert(!req_map.contains_key(in_flight_req_id)) by {
                        reveal(AsyncDisk::State::disk_ops);
                    }
                    assert(post.disk.requests[in_flight_req_id]
                        == pre.disk.requests[in_flight_req_id]);
                } else if post.disk.requests.contains_key(in_flight_req_id) {
                    assert(req_map.contains_key(in_flight_req_id));
                    assert(post.disk.requests[in_flight_req_id] == req_map[in_flight_req_id]);
                    assert(post.disk.requests[in_flight_req_id] is ReadReq);
                    assert(!unified_cache_superblock_write_pending(post));
                }
                assert(unified_cache_superblock_write_pending(post)
                    == unified_cache_superblock_write_pending(pre));
            } else {
                assert(!unified_cache_superblock_write_pending(pre));
                assert(!unified_cache_superblock_write_pending(post));
            }
        }
    }
    system_i_noop_next(pre, post, lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post));
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert(unified_cache_cache_disk_response_inv(pre));
        assert forall |id: ID| {
            &&& #[trigger] post.disk.responses.contains_key(id)
            &&& post_state.outstanding_cache_reqs.contains_key(id)
        } implies {
            let addr = post_state.outstanding_cache_reqs[id];
            let resp = post.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& post.disk.content.contains_key(addr)
                &&& resp->data == post.disk.content[addr]
            }
            &&& resp is WriteResp ==> {
                &&& post.disk.content.contains_key(addr)
                &&& cache_filled_addr(post_state.cache, addr)
                &&& post.disk.content[addr] == cache_filled_page(post_state.cache, addr)
            }
        } by {
            assert(pre.disk.responses.contains_key(id));
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
        }
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(inv(post));
}

pub proof fn program_disk_superblock_recovery_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    req_id: ID,
    raw_page: RawPage,
    image: AbstractSuperblockImage,
    new_journal: AtomicJournalState::State,
    new_branch: AtomicBranchState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk),
        inv(pre),
        UnifiedCacheSystem::State::superblock_recovery(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            req_id,
            raw_page,
            image,
            new_journal,
            new_branch,
            reqs,
            resps,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
}

pub proof fn program_disk_execute_sync_begin_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    req_id: ID,
    image: AbstractSuperblockImage,
    journal_reads: Map<Address, RawPage>,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
    new_branch: AtomicBranchState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk),
        inv(pre),
        UnifiedCacheSystem::State::execute_sync_begin(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            req_id,
            image,
            journal_reads,
            new_cache,
            new_journal,
            new_branch,
            reqs,
            resps,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
}

pub proof fn program_disk_execute_sync_prepared_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    req: DiskRequest,
    new_journal: AtomicJournalState::State,
    new_branch: AtomicBranchState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk),
        inv(pre),
        UnifiedCacheSystem::State::execute_sync_prepared(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            req,
            new_journal,
            new_branch,
            reqs,
            resps,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
}

pub proof fn program_disk_execute_sync_end_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    journal_discarded_aus: Set<AU>,
    new_journal: AtomicJournalState::State,
    new_branch: AtomicBranchState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk),
        inv(pre),
        UnifiedCacheSystem::State::execute_sync_end(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            journal_discarded_aus,
            new_journal,
            new_branch,
            reqs,
            resps,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
}

pub proof fn program_disk_cache_io_begin_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    req_map: Map<ID, DiskRequest>,
    new_cache: Cache::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk),
        inv(pre),
        UnifiedCacheProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheSystem::Step::cache_io_begin(req_map, new_cache, reqs, resps),
            lbl->info,
        ),
        UnifiedCacheSystem::State::cache_io_begin(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            req_map,
            new_cache,
            reqs,
            resps,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheSystem::State::cache_io_begin);

    assert(lbl is ProgramDiskOp);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    } == disk_lbl);
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(multiset_to_map(reqs) == req_map);
    assert(disk_lbl->requests == req_map);
    assert(AsyncDisk::State::disk_ops(pre.disk, post.disk, disk_lbl)) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
        match disk_step {
            AsyncDisk::Step::disk_ops() => {},
            _ => { assert(false); },
        }
    }
    assert(post.disk.requests == pre.disk.requests.union_prefer_right(req_map)) by {
        reveal(AsyncDisk::State::disk_ops);
    }

    assert(post.disk.content == pre.disk.content) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    crate::spec::AsyncDisk_t::inv_next(pre.disk, post.disk, disk_lbl);
    assert(post.disk.inv());

    let updated = Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
    let new_outstanding = pre_state.outstanding_cache_reqs.union_prefer_right(updated);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        outstanding_cache_reqs: new_outstanding,
        ..pre_state
    });
    assert(post_state.recovery_state == pre_state.recovery_state);
    assert(post_state.journal == pre_state.journal);
    assert(post_state.branch == pre_state.branch);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.in_flight == pre_state.in_flight);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_req_map == pre_state.sync_req_map);

    let cache_lbl = Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()};
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_pre.same_except_cache_and_disk(journal_post));
    assert(branch_pre.same_except_cache_and_disk(branch_post));
    assert(journal_post.disk.content == journal_pre.disk.content);
    assert(branch_post.disk.content == branch_pre.disk.content);

    if journal_pre.superblock_loaded() {
        assert(branch_pre.superblock_loaded());
        journal_pre.loaded_cache_disk_ops_begin_refines_journal_internal(
            journal_post,
            req_map.values(),
        );
        branch_pre.loaded_cache_disk_ops_begin_refines_branch_internal(
            branch_post,
            req_map.values(),
        );

        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(
            journal_post,
        ));
        assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(
            journal_pre,
        ));
        assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(
            branch_post,
        ));
        assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(
            branch_pre,
        ));
        assert(CrashAwareCachingDiskJournal::State::next(
            src.journal,
            dst.journal,
            CrashAwareCachingDiskJournal::Label::Internal,
        ));
        assert(CrashAwareCachingDiskBranch::State::next(
            src.branch,
            dst.branch,
            CrashAwareCachingDiskBranch::Label::Internal,
        ));
        assert(dst.progress == src.progress);
        assert(dst.sync_reqs == src.sync_reqs);
        assert(dst.free_aus == src.free_aus);
        assert(dst.superblockstore == src.superblockstore) by {
            assert(post_state.in_flight == pre_state.in_flight);
            assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
            if pre_state.in_flight is Some {
                let req_id = pre_state.in_flight.unwrap().req_id;
                if pre.disk.requests.contains_key(req_id) {
                    assert(!req_map.contains_key(req_id)) by {
                        reveal(AsyncDisk::State::disk_ops);
                    }
                    assert(post.disk.requests[req_id] == pre.disk.requests[req_id]);
                } else if post.disk.requests.contains_key(req_id) {
                    assert(req_map.contains_key(req_id)) by {
                        assert(post.disk.requests == pre.disk.requests.union_prefer_right(req_map));
                    }
                    assert(req_map.contains_key(req_id));
                    assert(post.disk.requests[req_id] == req_map[req_id]);
                    assert(updated.contains_key(req_id));
                    assert(updated[req_id] != spec_superblock_addr());
                    assert(post.disk.requests[req_id].addr() != spec_superblock_addr());
                    if unified_cache_superblock_write_pending(post) {
                        assert(post.disk.requests[req_id] is WriteReq);
                        assert(post.disk.requests[req_id]->to == spec_superblock_addr());
                        assert(post.disk.requests[req_id].addr() == spec_superblock_addr());
                        assert(false);
                    }
                }
                assert(unified_cache_superblock_write_pending(post)
                    == unified_cache_superblock_write_pending(pre));
            } else {
                assert(!unified_cache_superblock_write_pending(pre));
                assert(!unified_cache_superblock_write_pending(post));
            }
        }
        assert(CrashAwareCachingDiskSystem::State::component_internals(
            src,
            dst,
            target_lbl,
            dst.journal,
            dst.branch,
        )) by {
            reveal(CrashAwareCachingDiskSystem::State::component_internals);
        }
        assert(CrashAwareCachingDiskSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskSystem::Step::component_internals(dst.journal, dst.branch),
        )) by {
            reveal(CrashAwareCachingDiskSystem::State::next_by);
        }
        reveal(CrashAwareCachingDiskSystem::State::next);
        assert(unified_cache_component_refinement_inv(post));
        assert(unified_cache_superblockstore_refinement_inv(post));
        system_i_inv_next(pre, post, target_lbl);
    } else {
        assert(!branch_pre.superblock_loaded());
        assert(journal_post.persistent_image is None);
        assert(branch_post.persistent_image is None);
        assert(journal_post.persistent_journal_i() == journal_pre.persistent_journal_i()) by {
            assert(journal_post.disk.content == journal_pre.disk.content);
        }
        assert(branch_post.persistent_branch_i() == branch_pre.persistent_branch_i()) by {
            assert(branch_post.disk.content == branch_pre.disk.content);
        }
        assert(journal_post.i() == journal_pre.i()) by {
            assert(journal_post.ephemeral_journal_i() == journal_pre.ephemeral_journal_i());
            assert(journal_post.frozen_journal_metadata_i()
                == journal_pre.frozen_journal_metadata_i());
        }
        assert(branch_post.i() == branch_pre.i()) by {
            assert(branch_post.ephemeral_branch_i() == branch_pre.ephemeral_branch_i());
            assert(branch_post.frozen_branch_metadata_i()
                == branch_pre.frozen_branch_metadata_i());
        }
        assert(UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post)
            == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
        assert(UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post)
            == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));

        assert(journal_post.inv()) by {
            assert(journal_post.journal.wf());
            assert(journal_post.persistent_superblock_image_i()
                == journal_pre.persistent_superblock_image_i()) by {
                assert(journal_post.disk.content == journal_pre.disk.content);
            }
            assert(journal_post.persistent_superblock_image_i().wf());
            assert(journal_post.cache.inv()) by {
                Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);
            }
            assert(journal_post.disk.inv());
            let aus = journal_pre.journal_projection_aus();
            cache_disk_ops_begin_refines_caching_disk_internal(
                pre_state.cache,
                post_state.cache,
                pre.disk,
                aus,
                req_map.values(),
            );
            assert(journal_post.journal_projection_aus() =~= aus);
            assert(CachingDisk::State::next(
                journal_pre.journal_caching_disk_i(),
                journal_post.journal_caching_disk_i(),
                CachingDisk::Label::Internal{},
            ));
            CachingDisk::State::inv_next(
                journal_pre.journal_caching_disk_i(),
                journal_post.journal_caching_disk_i(),
                CachingDisk::Label::Internal{},
            );
        }
        assert(branch_post.inv()) by {
            assert(branch_post.branch.wf());
            assert(branch_post.persistent_superblock_image_i()
                == branch_pre.persistent_superblock_image_i()) by {
                assert(branch_post.disk.content == branch_pre.disk.content);
            }
            assert(branch_post.persistent_superblock_image_i().wf());
            assert(branch_post.cache.inv()) by {
                Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);
            }
            assert(branch_post.disk.inv());
            let aus = branch_pre.branch_projection_aus();
            cache_disk_ops_begin_refines_caching_disk_internal(
                pre_state.cache,
                post_state.cache,
                pre.disk,
                aus,
                req_map.values(),
            );
            assert(branch_post.branch_projection_aus() =~= aus);
            assert(CachingDisk::State::next(
                branch_pre.branch_caching_disk_i(),
                branch_post.branch_caching_disk_i(),
                CachingDisk::Label::Internal{},
            ));
            CachingDisk::State::inv_next(
                branch_pre.branch_caching_disk_i(),
                branch_post.branch_caching_disk_i(),
                CachingDisk::Label::Internal{},
            );
        }
        assert(journal_post.semantic_inv());
        assert(branch_post.semantic_inv());
        assert(UnifiedCacheJournalRefinement::inv(journal_post));
        assert(UnifiedCacheBranchRefinement::inv(branch_post));

        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        assert(dst == src) by {
            assert(dst.journal == src.journal);
            assert(dst.branch == src.branch);
            assert(dst.progress == src.progress);
            assert(dst.sync_reqs == src.sync_reqs);
            assert(dst.free_aus == src.free_aus);
            assert(dst.superblockstore == src.superblockstore) by {
                assert(post_state.in_flight == pre_state.in_flight);
                assert(pre_state.in_flight is None);
                assert(!unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
                assert(!unified_cache_in_flight_superblock_landed(post_state, post.disk));
                assert(!unified_cache_superblock_write_pending(pre));
                assert(!unified_cache_superblock_write_pending(post));
                assert(post.disk.content == pre.disk.content);
            }
        }
        system_i_noop_next(pre, post, lbl);
    }

    assert(unified_cache_ready_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
        assert(post_state.branch == pre_state.branch);
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
    }
    assert(post.disk.responses == pre.disk.responses) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    assert(req_map.dom().disjoint(pre.disk.responses.dom())) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    cache_io_begin_preserves_cache_disk_response_inv(pre, post, req_map);
    assert(unified_cache_cache_disk_response_inv(post));
    assert(system_model_progress_history_inv(post)) by {
        assert forall |req: Request| #[trigger] post.requests.contains(req)
            implies post.id_history.contains(req.id) by {
            assert(pre.requests.contains(req));
            assert(pre.id_history.contains(req.id));
        }
        assert forall |reply: Reply| #[trigger] post.replies.contains(reply)
            implies post.id_history.contains(reply.id) by {
            assert(pre.replies.contains(reply));
            assert(pre.id_history.contains(reply.id));
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(inv(post));
}

pub proof fn program_disk_cache_io_end_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    resp_map: Map<ID, DiskResponse>,
    new_cache: Cache::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk),
        inv(pre),
        UnifiedCacheProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheSystem::Step::cache_io_end(resp_map, new_cache, reqs, resps),
            lbl->info,
        ),
        UnifiedCacheSystem::State::cache_io_end(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            resp_map,
            new_cache,
            reqs,
            resps,
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheSystem::State::cache_io_end);

    assert(lbl is ProgramDiskOp);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(resp_map.dom() <= pre_state.outstanding_cache_reqs.dom());
    assert(multiset_to_map(resps) == resp_map);
    assert(disk_lbl->responses == resp_map);
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(pre.disk, post.disk, disk_lbl)) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(pre.disk, post.disk, disk_lbl, step);
        match disk_step {
            AsyncDisk::Step::disk_ops() => {},
            _ => { assert(false); },
        }
    }
    assert(post.disk.content == pre.disk.content) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    assert(post.disk.requests == pre.disk.requests) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    assert(post.disk.responses == pre.disk.responses.remove_keys(resp_map.dom())) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    assert(resp_map <= pre.disk.responses) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    crate::spec::AsyncDisk_t::inv_next(pre.disk, post.disk, disk_lbl);
    assert(post.disk.inv());

    let new_outstanding = pre_state.outstanding_cache_reqs.remove_keys(resp_map.dom());
    let finished = pre_state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
    let cache_resps = Map::new(
        |addr| finished.contains_key(addr),
        |addr| resp_map[finished[addr]],
    );
    cache_resps_coherent_from_disk_response_inv(pre, resp_map, cache_resps);
    let cache_lbl = Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps};
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        outstanding_cache_reqs: new_outstanding,
        ..pre_state
    });
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(post_state.recovery_state == pre_state.recovery_state);
    assert(post_state.journal == pre_state.journal);
    assert(post_state.branch == pre_state.branch);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.in_flight == pre_state.in_flight);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_req_map == pre_state.sync_req_map);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_pre.same_except_cache_and_disk(journal_post));
    assert(branch_pre.same_except_cache_and_disk(branch_post));
    assert(journal_post.disk.content == journal_pre.disk.content);
    assert(branch_post.disk.content == branch_pre.disk.content);

    if journal_pre.superblock_loaded() {
        assert(branch_pre.superblock_loaded());
        journal_pre.loaded_cache_disk_ops_end_refines_journal_internal(
            journal_post,
            cache_resps,
        );
        branch_pre.loaded_cache_disk_ops_end_refines_branch_internal(
            branch_post,
            cache_resps,
        );

        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        assert(CrashAwareCachingDiskJournal::State::next(
            src.journal,
            dst.journal,
            CrashAwareCachingDiskJournal::Label::Internal,
        ));
        assert(CrashAwareCachingDiskBranch::State::next(
            src.branch,
            dst.branch,
            CrashAwareCachingDiskBranch::Label::Internal,
        ));
        assert(dst.progress == src.progress);
        assert(dst.sync_reqs == src.sync_reqs);
        assert(dst.free_aus == src.free_aus);
        assert(dst.superblockstore == src.superblockstore) by {
            assert(post_state.in_flight == pre_state.in_flight);
            assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
            assert(post.disk.requests == pre.disk.requests);
            assert(unified_cache_superblock_write_pending(post)
                == unified_cache_superblock_write_pending(pre));
        }
        assert(CrashAwareCachingDiskSystem::State::component_internals(
            src,
            dst,
            target_lbl,
            dst.journal,
            dst.branch,
        )) by {
            reveal(CrashAwareCachingDiskSystem::State::component_internals);
        }
        assert(CrashAwareCachingDiskSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskSystem::Step::component_internals(dst.journal, dst.branch),
        )) by {
            reveal(CrashAwareCachingDiskSystem::State::next_by);
        }
        reveal(CrashAwareCachingDiskSystem::State::next);
        assert(unified_cache_component_refinement_inv(post));
        assert(unified_cache_superblockstore_refinement_inv(post));
        system_i_inv_next(pre, post, target_lbl);
    } else {
        assert(!branch_pre.superblock_loaded());
        assert(journal_post.persistent_image is None);
        assert(branch_post.persistent_image is None);
        assert(journal_post.persistent_journal_i() == journal_pre.persistent_journal_i()) by {
            assert(journal_post.disk.content == journal_pre.disk.content);
        }
        assert(branch_post.persistent_branch_i() == branch_pre.persistent_branch_i()) by {
            assert(branch_post.disk.content == branch_pre.disk.content);
        }
        assert(journal_post.i() == journal_pre.i()) by {
            assert(journal_post.ephemeral_journal_i() == journal_pre.ephemeral_journal_i());
            assert(journal_post.frozen_journal_metadata_i()
                == journal_pre.frozen_journal_metadata_i());
        }
        assert(branch_post.i() == branch_pre.i()) by {
            assert(branch_post.ephemeral_branch_i() == branch_pre.ephemeral_branch_i());
            assert(branch_post.frozen_branch_metadata_i()
                == branch_pre.frozen_branch_metadata_i());
        }
        assert(journal_post.inv()) by {
            assert(journal_post.journal.wf());
            assert(journal_post.persistent_superblock_image_i()
                == journal_pre.persistent_superblock_image_i()) by {
                assert(journal_post.disk.content == journal_pre.disk.content);
            }
            assert(journal_post.persistent_superblock_image_i().wf());
            assert(journal_post.cache.inv()) by {
                Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);
            }
            assert(journal_post.disk.inv());
            let aus = journal_pre.journal_projection_aus();
            cache_disk_ops_end_refines_caching_disk_internal(
                pre_state.cache,
                post_state.cache,
                pre.disk,
                aus,
                cache_resps,
            );
            assert(journal_post.journal_projection_aus() =~= aus);
            assert(CachingDisk::State::next(
                journal_pre.journal_caching_disk_i(),
                journal_post.journal_caching_disk_i(),
                CachingDisk::Label::Internal{},
            ));
            CachingDisk::State::inv_next(
                journal_pre.journal_caching_disk_i(),
                journal_post.journal_caching_disk_i(),
                CachingDisk::Label::Internal{},
            );
        }
        assert(branch_post.inv()) by {
            assert(branch_post.branch.wf());
            assert(branch_post.persistent_superblock_image_i()
                == branch_pre.persistent_superblock_image_i()) by {
                assert(branch_post.disk.content == branch_pre.disk.content);
            }
            assert(branch_post.persistent_superblock_image_i().wf());
            assert(branch_post.cache.inv()) by {
                Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);
            }
            assert(branch_post.disk.inv());
            let aus = branch_pre.branch_projection_aus();
            cache_disk_ops_end_refines_caching_disk_internal(
                pre_state.cache,
                post_state.cache,
                pre.disk,
                aus,
                cache_resps,
            );
            assert(branch_post.branch_projection_aus() =~= aus);
            assert(CachingDisk::State::next(
                branch_pre.branch_caching_disk_i(),
                branch_post.branch_caching_disk_i(),
                CachingDisk::Label::Internal{},
            ));
            CachingDisk::State::inv_next(
                branch_pre.branch_caching_disk_i(),
                branch_post.branch_caching_disk_i(),
                CachingDisk::Label::Internal{},
            );
        }
        assert(journal_post.semantic_inv());
        assert(branch_post.semantic_inv());
        assert(UnifiedCacheJournalRefinement::inv(journal_post));
        assert(UnifiedCacheBranchRefinement::inv(branch_post));

        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        assert(dst == src) by {
            assert(dst.journal == src.journal);
            assert(dst.branch == src.branch);
            assert(dst.progress == src.progress);
            assert(dst.sync_reqs == src.sync_reqs);
            assert(dst.free_aus == src.free_aus);
            assert(dst.superblockstore == src.superblockstore) by {
                assert(post_state.in_flight == pre_state.in_flight);
                assert(pre_state.in_flight is None);
                assert(!unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
                assert(!unified_cache_in_flight_superblock_landed(post_state, post.disk));
                assert(!unified_cache_superblock_write_pending(pre));
                assert(!unified_cache_superblock_write_pending(post));
                assert(post.disk.content == pre.disk.content);
            }
        }
        system_i_noop_next(pre, post, lbl);
    }

    assert(unified_cache_ready_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
        assert(post_state.branch == pre_state.branch);
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
    }
    cache_io_end_preserves_cache_disk_response_inv(pre, post, resp_map, cache_resps);
    assert(unified_cache_cache_disk_response_inv(post));
    assert(system_model_progress_history_inv(post)) by {
        assert forall |req: Request| #[trigger] post.requests.contains(req)
            implies post.id_history.contains(req.id) by {
            assert(pre.requests.contains(req));
            assert(pre.id_history.contains(req.id));
        }
        assert forall |reply: Reply| #[trigger] post.replies.contains(reply)
            implies post.id_history.contains(reply.id) by {
            assert(pre.replies.contains(reply));
            assert(pre.id_history.contains(reply.id));
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(inv(post));
}

pub proof fn program_disk_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_disk(new_program, new_disk),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk));
    reveal(SystemModel::State::program_disk);

    assert(lbl is ProgramDiskOp);
    assert(UnifiedCacheProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::DiskIO{info: lbl->info},
    ));
    assert(post.program == new_program);
    assert(UnifiedCacheProgramModel::valid_disk_transition(
        pre.program,
        post.program,
        lbl->info,
    ));
    let unified_step = choose |step: UnifiedCacheSystem::Step| {
        &&& UnifiedCacheSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            step,
        )
        &&& UnifiedCacheProgramModel::disk_step_matches_info(pre.program.state, step, lbl->info)
    };
    assert(UnifiedCacheSystem::State::next_by(
        pre.program.state,
        post.program.state,
        UnifiedCacheSystem::Label::Disk,
        unified_step,
    ));
    assert(UnifiedCacheProgramModel::disk_step_matches_info(
        pre.program.state,
        unified_step,
        lbl->info,
    ));
    reveal(UnifiedCacheSystem::State::next_by);
    match unified_step {
        UnifiedCacheSystem::Step::initiate_recovery(req_id, reqs, resps) => {
            assert(UnifiedCacheSystem::State::initiate_recovery(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Disk,
                req_id,
                reqs,
                resps,
            ));
            program_disk_initiate_recovery_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                req_id,
                reqs,
                resps,
            );
        },
        UnifiedCacheSystem::Step::superblock_recovery(
            req_id,
            raw_page,
            image,
            new_journal,
            new_branch,
            reqs,
            resps,
        ) => {
            assert(UnifiedCacheSystem::State::superblock_recovery(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Disk,
                req_id,
                raw_page,
                image,
                new_journal,
                new_branch,
                reqs,
                resps,
            ));
            program_disk_superblock_recovery_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                req_id,
                raw_page,
                image,
                new_journal,
                new_branch,
                reqs,
                resps,
            );
        },
        UnifiedCacheSystem::Step::execute_sync_begin(
            req_id,
            image,
            journal_reads,
            new_cache,
            new_journal,
            new_branch,
            reqs,
            resps,
        ) => {
            assert(UnifiedCacheSystem::State::execute_sync_begin(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Disk,
                req_id,
                image,
                journal_reads,
                new_cache,
                new_journal,
                new_branch,
                reqs,
                resps,
            ));
            program_disk_execute_sync_begin_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                req_id,
                image,
                journal_reads,
                new_cache,
                new_journal,
                new_branch,
                reqs,
                resps,
            );
        },
        UnifiedCacheSystem::Step::execute_sync_prepared(
            req,
            new_journal,
            new_branch,
            reqs,
            resps,
        ) => {
            assert(UnifiedCacheSystem::State::execute_sync_prepared(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Disk,
                req,
                new_journal,
                new_branch,
                reqs,
                resps,
            ));
            program_disk_execute_sync_prepared_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                req,
                new_journal,
                new_branch,
                reqs,
                resps,
            );
        },
        UnifiedCacheSystem::Step::execute_sync_end(
            journal_discarded_aus,
            new_journal,
            new_branch,
            reqs,
            resps,
        ) => {
            assert(UnifiedCacheSystem::State::execute_sync_end(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Disk,
                journal_discarded_aus,
                new_journal,
                new_branch,
                reqs,
                resps,
            ));
            program_disk_execute_sync_end_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                journal_discarded_aus,
                new_journal,
                new_branch,
                reqs,
                resps,
            );
        },
        UnifiedCacheSystem::Step::cache_io_begin(req_map, new_cache, reqs, resps) => {
            assert(UnifiedCacheSystem::State::cache_io_begin(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Disk,
                req_map,
                new_cache,
                reqs,
                resps,
            ));
            program_disk_cache_io_begin_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                req_map,
                new_cache,
                reqs,
                resps,
            );
        },
        UnifiedCacheSystem::Step::cache_io_end(resp_map, new_cache, reqs, resps) => {
            assert(UnifiedCacheSystem::State::cache_io_end(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Disk,
                resp_map,
                new_cache,
                reqs,
                resps,
            ));
            program_disk_cache_io_end_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                resp_map,
                new_cache,
                reqs,
                resps,
            );
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn program_internal_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_internal(new_program),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
}

pub proof fn disk_internal_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::disk_internal(new_disk),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
}

pub proof fn crash_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::crash(new_program, new_disk),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
}

pub proof fn noop_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::noop(),
        ),
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
}

pub proof fn dummy_to_use_type_params_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        inv(pre),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    assume(false);
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
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::next);
    reveal(SystemModel::State::next_by);

    let step = choose |step: SystemModel::Step<UnifiedCacheProgramModel>|
        SystemModel::State::next_by(pre, post, lbl, step);
    match step {
        SystemModel::Step::accept_request() => {
            assert(SystemModel::State::accept_request(pre, post, lbl));
            accept_request_refines(pre, post, lbl);
        },
        SystemModel::Step::deliver_reply() => {
            deliver_reply_refines(pre, post, lbl);
        },
        SystemModel::Step::program_execute(new_program) => {
            program_execute_refines(pre, post, lbl, new_program);
        },
        SystemModel::Step::accept_sync_request() => {
            accept_sync_request_refines(pre, post, lbl);
        },
        SystemModel::Step::program_accept_sync_request(new_program) => {
            program_accept_sync_request_refines(pre, post, lbl, new_program);
        },
        SystemModel::Step::program_deliver_sync_reply(new_program) => {
            program_deliver_sync_reply_refines(pre, post, lbl, new_program);
        },
        SystemModel::Step::deliver_sync_reply() => {
            deliver_sync_reply_refines(pre, post, lbl);
        },
        SystemModel::Step::program_disk(new_program, new_disk) => {
            program_disk_refines(pre, post, lbl, new_program, new_disk);
        },
        SystemModel::Step::program_internal(new_program) => {
            program_internal_refines(pre, post, lbl, new_program);
        },
        SystemModel::Step::disk_internal(new_disk) => {
            disk_internal_refines(pre, post, lbl, new_disk);
        },
        SystemModel::Step::crash(new_program, new_disk) => {
            crash_refines(pre, post, lbl, new_program, new_disk);
        },
        SystemModel::Step::noop() => {
            noop_refines(pre, post, lbl);
        },
        SystemModel::Step::dummy_to_use_type_params(_) => {
            dummy_to_use_type_params_refines(pre, post, lbl);
        },
    }
}

} // verus!
