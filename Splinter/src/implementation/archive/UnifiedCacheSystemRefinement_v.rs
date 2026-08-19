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
use crate::abstract_system::StampedMap_v::LSN;
use crate::allocation_layer::BranchTypes_v::Summary;
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::allocation_layer::MiniAllocator_v::MiniAllocator;
use crate::betree::LinkedBranch_v::SplitArg;
use crate::disk::GenericDisk_v::{
    Address, AU, Pointer, addrs_with_different_au, set_addrs_disjoint_aus, to_aus,
    to_aus_domain,
};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, abstract_superblock_raw_wf,
    empty_abstract_superblock_image, parse_abstract_superblock, superblock_matches,
};
use crate::implementation::AtomicBranchState_v::{AtomicBranchImage, AtomicBranchState};
use crate::implementation::AtomicJournalState_v::AtomicJournalState;
use crate::implementation::Cache_v::{addr_maps_to_req, Cache, Entry, Slot, Status};
use crate::implementation::CrashAwareCachingDiskBranch_v::{
    CrashAwareCachingDiskBranch, PersistentCachingDiskBranch,
};
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    CachingDiskJournalImage, CrashAwareCachingDiskJournal, PersistentCachingDiskJournal,
};
use crate::implementation::CrashAwareCachingDiskSystem_v::{
    CrashAwareCachingDiskSystem, SuperblockStore, singleton_key_seq,
    singleton_message_seq,
};
use crate::implementation::CrashAwareCachingDiskSystemRefinement_v as CachingDiskSystemRefinement;
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::MultisetMapRelation_v::{
    multiset_map_singleton, multiset_map_singleton_ensures, multiset_to_map,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_internal_refines_caching_disk_internal,
    cache_internal_post_filled_addr_was_pre_filled,
    cache_internal_preserves_empty_projection,
    cache_internal_preserves_clean_filled_addr,
    cache_internal_preserves_protected_entries,
    caching_disk_i_domains_wf_from_sources,
    caching_disk_i as adapter_caching_disk_i,
    caching_disk_i_inv_from_clean_cache_coupling,
    cache_disk_ops_begin_preserves_filled_page,
    cache_disk_ops_begin_refines_caching_disk_internal, cache_filled_addr, cache_filled_page,
    cache_status_i,
    cache_disk_ops_end_refines_caching_disk_internal,
    cache_disk_ops_end_preserves_filled_page,
    async_disk_process_write_refines_projected_internal,
    async_disk_process_write_preserves_readable,
    disk_has_pending_id,
    filled_cache_pages, filled_cache_status, outstanding_cache_io_wf, project_cache_pages,
    project_cache_status, project_persistent,
};
use crate::implementation::CachedBranch_v::{
    CachedBranch, LoadedPathReceipt, loaded_append_write_nodes,
    loaded_initialize_write_nodes,
};
use crate::implementation::CachingDiskBranch_v::{
    active_loaded_nodes_follow_readable_writes,
    active_loaded_nodes_submap_visible_from_readable_visible,
    branch_summary_reads_valid, loaded_branch_summary_agrees,
    loaded_branch_summary_agrees_at, loaded_branch_summary_agrees_domain_contains,
    loaded_branch_summary_agrees_from_forall, CachingDiskBranch,
    CachingDiskBranchImage, CachingDiskBranchMetadata,
    empty_caching_disk_branch_image_summary_aus_empty, root_aus_up_to, root_aus_up_to_contains,
    mini_allocator_allocated_addrs, sealed_summary_aus_between, to_branch_nodes,
};
use crate::implementation::CachingDisk_v::{CachingDisk, PageStatus, addresses_in_aus};
use crate::implementation::UnifiedCacheBranchRefinement_v as UnifiedCacheBranchRefinement;
use crate::implementation::UnifiedCacheJournalRefinement_v as UnifiedCacheJournalRefinement;
use crate::implementation::UnifiedCacheProgramModel_v::UnifiedCacheProgramModel;
use crate::implementation::UnifiedCacheSystem_v::{
    AtomicSyncPhase, UnifiedCacheSystem,
    cache_filled_addr_raw, cache_filled_page_raw,
};
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::spec::AsyncDisk_t::{AsyncDisk, DiskRequest, DiskResponse, RawPage};
use crate::spec::KeyType_t::Key;
use crate::spec::MapSpec_t::{EphemeralState, ID, Input, Reply, Request, SyncReqId};
use crate::spec::Messages_t::Message;
use crate::trusted::ProgramModelTrait_t::{
    DiskLabel, DiskModel, ProgramLabel, ProgramModelTrait, ProgramUserOp,
};
use crate::trusted::SystemModel_t::SystemModel;

verus! {

pub closed spec fn system_multiset_to_set_i<V>(m: Multiset<V>) -> Set<V>
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

pub closed spec fn system_model_progress_history_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    &&& forall |req: Request| #[trigger] model.requests.contains(req)
        ==> model.id_history.contains(req.id)
    &&& forall |reply: Reply| #[trigger] model.replies.contains(reply)
        ==> model.id_history.contains(reply.id)
}

pub closed spec fn system_model_progress_unique_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    &&& forall |req: Request| #[trigger] model.requests.count(req) <= 1
    &&& forall |reply: Reply| #[trigger] model.replies.count(reply) <= 1
}

pub closed spec fn system_model_request_id_unique_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    forall |req1: Request, req2: Request| {
        &&& #[trigger] model.requests.contains(req1)
        &&& #[trigger] model.requests.contains(req2)
        &&& req1.id == req2.id
    } ==> req1 == req2
}

pub closed spec fn system_model_request_reply_disjoint_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    forall |req: Request, reply: Reply| {
        &&& #[trigger] model.requests.contains(req)
        &&& #[trigger] model.replies.contains(reply)
    } ==> req.id != reply.id
}

pub closed spec fn unified_cache_superblock_write_pending(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let phase = model.program.state.sync_phase;
    &&& phase is SuperblockWriteIssued
    &&& model.disk.requests.contains_key(phase->req_id)
    &&& model.disk.requests[phase->req_id] is WriteReq
    &&& model.disk.requests[phase->req_id]->to == spec_superblock_addr()
}

pub closed spec fn unified_cache_cache_disk_response_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    forall |id: ID| {
        &&& #[trigger] model.disk.responses.contains_key(id)
        &&& model.program.state.outstanding_cache_reqs.contains_key(id)
    } ==> {
        let addr = model.program.state.outstanding_cache_reqs[id];
        let resp = model.disk.responses[id];
        &&& addr.wf()
        &&& resp is ReadResp ==> {
            &&& resp->data == model.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& model.disk.content.contains_key(addr)
            &&& cache_filled_addr(model.program.state.cache, addr)
            &&& model.disk.content[addr] == cache_filled_page(model.program.state.cache, addr)
        }
    }
}

pub closed spec fn unified_cache_shared_cache_disk_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    &&& forall |addr: Address| #[trigger] filled_cache_pages(state.cache).contains_key(addr)
        ==> addr.wf()
    &&& forall |addr: Address| #[trigger] model.disk.content.contains_key(addr)
        && addr != spec_superblock_addr()
        ==> addr.wf()
    &&& forall |addr: Address| {
        &&& #[trigger] filled_cache_status(state.cache).contains_key(addr)
        &&& filled_cache_status(state.cache)[addr] == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& model.disk.content.contains_key(addr)
    } ==> {
        &&& model.disk.content[addr] == cache_filled_page(state.cache, addr)
    }
}

pub closed spec fn unified_cache_cache_request_wf(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    &&& state.outstanding_cache_reqs.is_injective()
    &&& !state.outstanding_cache_reqs.contains_value(spec_superblock_addr())
    &&& state.outstanding_cache_reqs.values() <= state.cache.lookup_map.dom()
    &&& forall |id: ID| #[trigger] state.outstanding_cache_reqs.contains_key(id) ==> {
        let addr = state.outstanding_cache_reqs[id];
        let slot = state.cache.lookup_map[addr];
        match state.cache.entries[slot] {
            Entry::Loading{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && state.cache.status_map[slot] is Writeback,
            _ => false,
        }
    }
}

pub closed spec fn unified_cache_outstanding_cache_reqs_disk_backed_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    outstanding_cache_io_wf(state.cache, model.disk, state.outstanding_cache_reqs)
}

pub closed spec fn unified_cache_recovery_superblock_io_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    let branch_src = UnifiedCacheBranchRefinement::unified_cache_branch_source(model);
    (state.recovery_state is Begin || state.recovery_state is AwaitingSuperblock) ==> {
        &&& state.persistent_image is None
        &&& state.sync_phase is None
        &&& state.sync_req_map == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty()
        &&& state.outstanding_cache_reqs == Map::<ID, Address>::empty()
        &&& state.outstanding_cache_reqs.dom().disjoint(model.disk.responses.dom())
        &&& journal_src.journal_caching_disk_i().cache == Map::<Address, RawPage>::empty()
        &&& journal_src.journal_caching_disk_i().status == Map::<Address, PageStatus>::empty()
        &&& branch_src.branch_caching_disk_i().cache == Map::<Address, RawPage>::empty()
        &&& branch_src.branch_caching_disk_i().status == Map::<Address, PageStatus>::empty()
        &&& branch_src.persistent_branch_image_i().loadable()
        &&& branch_src.persistent_branch_image_i().stack_wf()
        &&& project_cache_pages(
            state.cache,
            UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
                model.disk.content,
                branch_src.persistent_superblock_image_i().branch_roots,
            ),
        ) == Map::<Address, RawPage>::empty()
        &&& project_cache_status(
            state.cache,
            UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
                model.disk.content,
                branch_src.persistent_superblock_image_i().branch_roots,
            ),
        ) == Map::<Address, PageStatus>::empty()
        &&& forall |id: ID| {
            &&& #[trigger] model.disk.requests.contains_key(id)
            &&& !state.outstanding_cache_reqs.contains_key(id)
        } ==> {
            &&& model.disk.requests[id] is ReadReq
            &&& model.disk.requests[id]->from == spec_superblock_addr()
        }
        &&& forall |id: ID| {
            &&& #[trigger] model.disk.responses.contains_key(id)
            &&& !state.outstanding_cache_reqs.contains_key(id)
        } ==> {
            &&& model.disk.responses[id] is ReadResp
            &&& model.disk.content.contains_key(spec_superblock_addr())
            &&& model.disk.responses[id]->data == model.disk.content[spec_superblock_addr()]
        }
    }
}

pub closed spec fn unified_cache_in_flight_superblock_landed(
    state: UnifiedCacheSystem::State,
    disk: crate::trusted::ProgramModelTrait_t::DiskModel,
) -> bool
{
    let phase = state.sync_phase;
    &&& phase is SuperblockWriteIssued
    &&& !state.outstanding_cache_reqs.contains_key(phase->req_id)
    &&& disk.responses.contains_key(phase->req_id)
    &&& disk.responses[phase->req_id] is WriteResp
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
    let pending_raw = if unified_cache_superblock_write_pending(model) {
        model.disk.requests[model.program.state.sync_phase->req_id]->data
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

pub closed spec fn unified_cache_component_refinement_inv(
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

pub closed spec fn unified_cache_superblockstore_refinement_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    unified_cache_superblockstore_i(model).inv()
}

pub proof fn inv_implies_journal_source_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(model),
    ensures
        UnifiedCacheJournalRefinement::inv(
            UnifiedCacheJournalRefinement::unified_cache_journal_source(model),
        ),
{
    assert(unified_cache_component_refinement_inv(model));
}

pub proof fn inv_implies_branch_source_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(model),
    ensures
        UnifiedCacheBranchRefinement::inv(
            UnifiedCacheBranchRefinement::unified_cache_branch_source(model),
        ),
{
    assert(unified_cache_component_refinement_inv(model));
}

pub proof fn post_superblock_journal_source_facts(
    model: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(model),
        !(model.program.state.recovery_state is Begin),
        !(model.program.state.recovery_state is AwaitingSuperblock),
    ensures
        UnifiedCacheJournalRefinement::inv(
            UnifiedCacheJournalRefinement::unified_cache_journal_source(model),
        ),
        UnifiedCacheJournalRefinement::unified_cache_journal_source(model).superblock_loaded(),
        UnifiedCacheJournalRefinement::unified_cache_journal_source(model)
            .journal_caching_disk_state_i().refinement_inv(),
{
    let state = model.program.state;
    let src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    inv_implies_journal_source_inv(model);
    assert(UnifiedCacheJournalRefinement::inv(src));
    assert(src.inv());
    assert(src.semantic_inv());
    assert(unified_cache_recovery_metadata_inv(model));
    if state.recovery_state is SuperblockAvailable {
        assert(state.persistent_image is Some);
    } else if state.recovery_state is MetadataLoadComplete {
        assert(state.persistent_image is Some);
    } else {
        assert(state.recovery_state is RecoveryComplete);
        assert(state.persistent_image is Some);
    }
    assert(src.superblock_loaded());
    assert(src.ephemeral_journal_i()
        == crate::implementation::CrashAwareCachingDiskJournal_v::EphemeralCachingDiskJournal::Known{
            v: src.journal_caching_disk_state_i(),
        });
    assert(src.i().ephemeral is Known);
    assert(src.i().ephemeral->v == src.journal_caching_disk_state_i());
    assert(src.i().refinement_inv());
    assert(src.i().semantic_inv());
    assert(src.journal_caching_disk_state_i().refinement_inv());
}

pub closed spec fn unified_cache_ready_inv(
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

pub closed spec fn unified_cache_recovery_branch_metadata_agrees(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    let roots = state.branch.image.sealed_roots;
    let nodes = to_branch_nodes(model.disk.content);
    &&& state.branch.mini_allocator == MiniAllocator::empty()
    &&& state.branch.image == state.branch.persistent_image
    &&& branch_summary_reads_valid(roots, nodes)
    &&& loaded_branch_summary_agrees(roots, nodes, state.branch.branch_summary)
}

pub closed spec fn unified_cache_before_metadata_load_complete(
    state: UnifiedCacheSystem::State,
) -> bool
{
    ||| state.recovery_state is Begin
    ||| state.recovery_state is AwaitingSuperblock
    ||| state.recovery_state is SuperblockAvailable
}

pub closed spec fn cache_all_filled_clean(cache: Cache::State) -> bool
{
    forall |addr: Address| #[trigger] filled_cache_status(cache).contains_key(addr)
        ==> filled_cache_status(cache)[addr] == PageStatus::Clean
}

pub closed spec fn unified_cache_recovery_cache_quiescent_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    unified_cache_before_metadata_load_complete(state) ==> {
        &&& forall |id: ID| #[trigger] model.disk.requests.contains_key(id)
            ==> model.disk.requests[id] is ReadReq
        &&& cache_all_filled_clean(state.cache)
    }
}

pub proof fn recovery_valid_read_matches_disk(
    model: SystemModel::State<UnifiedCacheProgramModel>,
    addr: Address,
    data: RawPage,
)
    requires
        inv(model),
        unified_cache_before_metadata_load_complete(model.program.state),
        model.program.state.cache.valid_read(addr, data),
        addr != spec_superblock_addr(),
        model.disk.content.contains_key(addr),
    ensures
        model.disk.content.contains_key(addr),
        data == model.disk.content[addr],
{
    let state = model.program.state;
    assert(state.cache.inv());
    state.cache.build_lookup_map_ensures();
    assert(state.cache.build_lookup_map_props(state.cache.lookup_map));
    assert(cache_filled_addr(state.cache, addr));
    assert(data == cache_filled_page(state.cache, addr));
    assert(state.cache.status_map.contains_key(state.cache.lookup_map[addr]));
    assert(filled_cache_status(state.cache).contains_key(addr));
    assert(unified_cache_recovery_cache_quiescent_inv(model));
    assert(filled_cache_status(state.cache)[addr] == PageStatus::Clean);
    assert(unified_cache_shared_cache_disk_inv(model));
    assert(model.disk.content.contains_key(addr));
    assert(model.disk.content[addr] == cache_filled_page(state.cache, addr));
}

pub proof fn recovery_superblock_response_facts(
    model: SystemModel::State<UnifiedCacheProgramModel>,
    id: ID,
    resp: DiskResponse,
)
    requires
        inv(model),
        model.program.state.recovery_state is AwaitingSuperblock,
        model.disk.responses.contains_key(id),
        model.disk.responses[id] == resp,
    ensures
        model.program.state.outstanding_cache_reqs == Map::<ID, Address>::empty(),
        resp is ReadResp,
        model.disk.content.contains_key(spec_superblock_addr()),
        resp->data == model.disk.content[spec_superblock_addr()],
        abstract_superblock_raw_wf(resp->data),
{
    let state = model.program.state;
    assert(unified_cache_recovery_superblock_io_inv(model));
    assert(state.outstanding_cache_reqs == Map::<ID, Address>::empty());
    assert(!state.outstanding_cache_reqs.contains_key(id));
    assert(model.disk.responses[id] is ReadResp);
    assert(model.disk.content.contains_key(spec_superblock_addr()));
    assert(model.disk.responses[id]->data == model.disk.content[spec_superblock_addr()]);

    assert(unified_cache_component_refinement_inv(model));
    let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    assert(UnifiedCacheJournalRefinement::inv(journal_src));
    assert(UnifiedCacheJournalRefinement::async_disk_superblock_page_wf(model.disk.content));
    assert(abstract_superblock_raw_wf(model.disk.content[spec_superblock_addr()]));
}

pub proof fn loaded_branch_summary_agrees_insert_root(
    roots: Seq<Address>,
    disk_nodes: crate::implementation::CachedBranch_v::LoadedBranch,
    read_nodes: crate::implementation::CachedBranch_v::LoadedBranch,
    summary: Map<AU, Summary>,
    root: Address,
)
    requires
        set_addrs_disjoint_aus(roots.to_set()),
        branch_summary_reads_valid(roots, disk_nodes),
        loaded_branch_summary_agrees(roots, disk_nodes, summary),
        roots.contains(root),
        crate::implementation::CachedBranch_v::root_summary_read_valid(root, read_nodes),
        crate::implementation::CachedBranch_v::root_summary_from_read(root, read_nodes)
            == crate::implementation::CachedBranch_v::root_summary_from_read(root, disk_nodes),
    ensures
        loaded_branch_summary_agrees(
            roots,
            disk_nodes,
            summary.insert(
                root.au,
                crate::implementation::CachedBranch_v::root_summary_from_read(root, read_nodes),
            ),
        ),
{
    let post_summary = summary.insert(
        root.au,
        crate::implementation::CachedBranch_v::root_summary_from_read(root, read_nodes),
    );
    let root_idx = choose |i: int| 0 <= i < roots.len() && roots[i] == root;
    root_aus_up_to_contains(roots, roots.len() as nat, root_idx);
    assert(root_aus_up_to(roots, roots.len() as nat).contains(root.au));

    assert(post_summary.dom() <= root_aus_up_to(roots, roots.len() as nat)) by {
        assert forall |au: AU| #[trigger] post_summary.dom().contains(au)
            implies root_aus_up_to(roots, roots.len() as nat).contains(au) by {
            if au == root.au {
            } else {
                assert(summary.dom().contains(au));
                loaded_branch_summary_agrees_domain_contains(roots, disk_nodes, summary, au);
            }
        }
    }

    assert forall |i: int| #![trigger roots[i]]
        0 <= i < roots.len() && post_summary.contains_key(roots[i].au)
        implies {
            &&& crate::implementation::CachedBranch_v::root_summary_read_valid(
                roots[i],
                disk_nodes,
            )
            &&& post_summary[roots[i].au]
                == crate::implementation::CachedBranch_v::root_summary_from_read(
                    roots[i],
                    disk_nodes,
                )
        } by {
        assert(crate::implementation::CachedBranch_v::root_summary_read_valid(
            roots[i],
            disk_nodes,
        ));
        if roots[i].au == root.au {
            assert(roots[i] == root) by {
                if roots[i] != root {
                    assert(roots.to_set().contains(roots[i]));
                    assert(roots.to_set().contains(root));
                    assert(addrs_with_different_au(roots[i], root));
                    assert(roots[i].au != root.au);
                    assert(false);
                }
            }
            assert(post_summary[roots[i].au]
                == crate::implementation::CachedBranch_v::root_summary_from_read(root, read_nodes));
            assert(crate::implementation::CachedBranch_v::root_summary_from_read(root, read_nodes)
                == crate::implementation::CachedBranch_v::root_summary_from_read(root, disk_nodes));
        } else {
            assert(summary.contains_key(roots[i].au));
            loaded_branch_summary_agrees_at(roots, disk_nodes, summary, i);
            assert(post_summary[roots[i].au] == summary[roots[i].au]);
        }
    }
    loaded_branch_summary_agrees_from_forall(roots, disk_nodes, post_summary);
}

pub closed spec fn unified_cache_recovery_metadata_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    &&& state.recovery_state is SuperblockAvailable ==> {
        &&& state.persistent_image is Some
        &&& unified_cache_recovery_branch_metadata_agrees(model)
    }
    &&& state.recovery_state is MetadataLoadComplete ==> {
        &&& state.persistent_image is Some
        &&& state.journal.ready()
        &&& state.branch.metadata_loaded()
    }
    &&& state.recovery_state is RecoveryComplete ==> {
        &&& state.persistent_image is Some
        &&& state.journal.ready()
        &&& state.branch.metadata_loaded()
        &&& state.journal.journal.seq_end() == state.branch.seq_end()
    }
    &&& !(state.recovery_state is RecoveryComplete) ==> {
        &&& state.sync_phase is None
        &&& state.sync_req_map == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty()
    }
}

pub proof fn allocation_metadata_loaded_facts(
    model: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(model),
        model.program.state.allocation_metadata_loaded(),
    ensures
        model.program.state.persistent_image is Some,
        model.program.state.journal_metadata_loaded(),
        model.program.state.branch_metadata_loaded(),
        UnifiedCacheJournalRefinement::unified_cache_journal_source(model).superblock_loaded(),
        UnifiedCacheJournalRefinement::unified_cache_journal_source(model).journal.ready(),
        UnifiedCacheBranchRefinement::unified_cache_branch_source(model).superblock_loaded(),
        UnifiedCacheBranchRefinement::unified_cache_branch_source(model).branch.metadata_loaded(),
{
    let state = model.program.state;
    assert(unified_cache_recovery_metadata_inv(model));
    if state.recovery_state is MetadataLoadComplete {
        assert(state.persistent_image is Some);
        assert(state.journal.ready());
        assert(state.branch.metadata_loaded());
    } else {
        assert(state.recovery_state is RecoveryComplete);
        assert(state.persistent_image is Some);
        assert(state.journal.ready());
        assert(state.branch.metadata_loaded());
    }
    let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    let branch_src = UnifiedCacheBranchRefinement::unified_cache_branch_source(model);
    assert(journal_src.persistent_image == state.persistent_image);
    assert(branch_src.persistent_image == state.persistent_image);
}

pub closed spec fn unified_cache_durable_image_inv(
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

pub closed spec fn unified_cache_sync_phase_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    &&& state.sync_phase is Started ==> {
        &&& !state.journal.prepared
        &&& !state.branch.prepared
    }
    &&& state.sync_phase is SuperblockWriteIssued ==> {
        let phase = state.sync_phase;
        &&& !state.outstanding_cache_reqs.contains_key(phase->req_id)
        &&& (unified_cache_superblock_write_pending(model) || {
            &&& model.disk.responses.contains_key(phase->req_id)
            &&& model.disk.responses[phase->req_id] is WriteResp
        })
    }
}

pub closed spec fn unified_cache_non_cache_write_request_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    forall |id: ID| {
        &&& #[trigger] model.disk.requests.contains_key(id)
        &&& model.disk.requests[id] is WriteReq
        &&& !state.outstanding_cache_reqs.contains_key(id)
    } ==> {
        let phase = state.sync_phase;
        &&& phase is SuperblockWriteIssued
        &&& id == phase->req_id
        &&& model.disk.requests[id]->to == spec_superblock_addr()
    }
}

pub closed spec fn unified_cache_superblock_write_request_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    state.sync_phase is SuperblockWriteIssued && unified_cache_superblock_write_pending(model)
        ==> {
            let phase = state.sync_phase;
            let req = model.disk.requests[phase->req_id];
            &&& superblock_matches(req->data, state.atomic_inflight_superblock_i())
            &&& state.atomic_inflight_superblock_i().wf()
        }
}

pub closed spec fn unified_cache_superblock_image_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
) -> bool
{
    let state = model.program.state;
    let image = parse_abstract_superblock(model.disk.content[spec_superblock_addr()]);
    &&& unified_cache_in_flight_superblock_landed(state, model.disk) ==>
        image == state.atomic_inflight_superblock_i()
    &&& state.persistent_image is Some
        && !unified_cache_in_flight_superblock_landed(state, model.disk) ==>
        image == state.persistent_image.unwrap()
}

pub open spec fn inv(model: SystemModel::State<UnifiedCacheProgramModel>) -> bool
{
    &&& unified_cache_component_refinement_inv(model)
    &&& unified_cache_superblockstore_refinement_inv(model)
    &&& unified_cache_cache_disk_response_inv(model)
    &&& unified_cache_shared_cache_disk_inv(model)
    &&& unified_cache_cache_request_wf(model)
    &&& unified_cache_outstanding_cache_reqs_disk_backed_inv(model)
    &&& unified_cache_recovery_superblock_io_inv(model)
    &&& unified_cache_recovery_cache_quiescent_inv(model)
    &&& unified_cache_system_i(model).inv()
    &&& unified_cache_recovery_metadata_inv(model)
    &&& unified_cache_ready_inv(model)
    &&& unified_cache_durable_image_inv(model)
    &&& unified_cache_sync_phase_inv(model)
    &&& unified_cache_non_cache_write_request_inv(model)
    &&& unified_cache_superblock_write_request_inv(model)
    &&& unified_cache_superblock_image_inv(model)
    &&& system_model_progress_history_inv(model)
    &&& system_model_progress_unique_inv(model)
    &&& system_model_request_id_unique_inv(model)
    &&& system_model_request_reply_disjoint_inv(model)
}

pub proof fn inv_implies_caching_disk_refinement_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(model),
    ensures
        CachingDiskSystemRefinement::refinement_inv(unified_cache_system_i(model)),
{
    let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    let branch_src = UnifiedCacheBranchRefinement::unified_cache_branch_source(model);
    let system = unified_cache_system_i(model);

    assert(unified_cache_component_refinement_inv(model));
    assert(system.inv());
    assert(system.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(
        journal_src,
    ));
    assert(system.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(
        branch_src,
    ));
    CachingDiskSystemRefinement::refinement_inv_from_parts(system);
}

pub proof fn inv_implies_cache_inv(model: SystemModel::State<UnifiedCacheProgramModel>)
    requires
        inv(model),
    ensures
        model.program.state.cache.inv(),
{
    let src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    assert(unified_cache_component_refinement_inv(model));
    assert(UnifiedCacheJournalRefinement::inv(src));
    assert(src.inv());
    assert(src.cache == model.program.state.cache);
    assert(model.program.state.cache.inv());
}

pub proof fn inv_implies_ready_seq_end_alignment(
    model: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(model),
        model.program.state.client_ready(),
    ensures
        model.program.state.persistent_image is Some,
        model.program.state.journal.ready(),
        model.program.state.branch.metadata_loaded(),
        model.program.state.journal.journal.seq_end()
            == model.program.state.branch.seq_end(),
{
    assert(unified_cache_ready_inv(model));
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
        model.program.state.allocation_metadata_loaded(),
    ensures
        UnifiedCacheJournalRefinement::unified_cache_journal_source(model).journal_projection_aus()
            <= unified_cache_system_i(model).journal_owned_aus(),
{
    let src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    let system = unified_cache_system_i(model);
    let cj = src.journal_caching_disk_state_i();

    allocation_metadata_loaded_facts(model);
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
        model.program.state.allocation_metadata_loaded(),
    ensures
        UnifiedCacheBranchRefinement::unified_cache_branch_source(model).branch_projection_aus()
            <= unified_cache_system_i(model).branch_owned_aus(),
{
    let src = UnifiedCacheBranchRefinement::unified_cache_branch_source(model);
    let system = unified_cache_system_i(model);
    let cb = src.branch_caching_disk_state_i();

    allocation_metadata_loaded_facts(model);
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

pub proof fn journal_fill_aus_shared_projection_inv_from_system_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
    aus: Set<AU>,
)
    requires
        inv(model),
        model.program.state.allocation_metadata_loaded(),
        aus <= model.program.state.free_aus,
    ensures
        UnifiedCacheJournalRefinement::unified_cache_journal_source(
            model,
        ).journal_fill_aus_shared_projection_inv(aus),
{
    let state = model.program.state;
    let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(model);
    let system = unified_cache_system_i(model);
    let owned_aus = journal_src.journal_projection_aus() + aus;

    journal_projection_aus_subset_system_journal_owned(model);
    assert(system.allocation_wf());
    assert(system.component_disjoint());
    assert(system.free_aus == state.free_aus);
    assert(state.free_aus.disjoint(system.component_owned_aus()));
    assert(system.component_owned_aus().contains(spec_superblock_addr().au));
    assert(owned_aus.disjoint(CrashAwareCachingDiskSystem::State::reserved_aus())) by {
        assert forall |au: AU| #[trigger] owned_aus.contains(au)
            implies !CrashAwareCachingDiskSystem::State::reserved_aus().contains(au) by {
            if journal_src.journal_projection_aus().contains(au) {
                assert(journal_src.journal_projection_aus() <= system.journal_owned_aus());
                assert(system.journal_owned_aus().contains(au));
                assert(system.component_owned_aus().contains(au));
            } else {
                assert(aus.contains(au));
                assert(state.free_aus.contains(au));
                assert(!system.component_owned_aus().contains(au));
            }
        }
    }
    assert forall |addr: Address| #[trigger] filled_cache_status(state.cache).contains_key(addr)
        && filled_cache_status(state.cache)[addr] == PageStatus::Clean
        && addresses_in_aus(owned_aus).contains(addr)
        && project_persistent(model.disk, owned_aus).contains_key(addr)
        implies {
            &&& model.disk.content[addr] == cache_filled_page(state.cache, addr)
        } by {
        assert(owned_aus.contains(addr.au));
        assert(model.disk.content.contains_key(addr));
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(CrashAwareCachingDiskSystem::State::reserved_aus().contains(addr.au));
                assert(false);
            }
        }
        assert(unified_cache_shared_cache_disk_inv(model));
    }
    assert forall |addr: Address| {
        &&& #[trigger] model.disk.content.contains_key(addr)
        &&& addresses_in_aus(owned_aus).contains(addr)
    } implies addr.wf() by {
        assert(owned_aus.contains(addr.au));
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(CrashAwareCachingDiskSystem::State::reserved_aus().contains(addr.au));
                assert(false);
            }
        }
        assert(unified_cache_shared_cache_disk_inv(model));
    }
    caching_disk_i_inv_from_clean_cache_coupling(state.cache, model.disk, owned_aus);
    caching_disk_i_domains_wf_from_sources(state.cache, model.disk, owned_aus);
    assert(journal_src.journal_fill_aus_shared_projection_inv(aus));
}

pub proof fn branch_fill_aus_shared_projection_inv_from_system_inv(
    model: SystemModel::State<UnifiedCacheProgramModel>,
    aus: Set<AU>,
)
    requires
        inv(model),
        model.program.state.allocation_metadata_loaded(),
        aus <= model.program.state.free_aus,
    ensures
        UnifiedCacheBranchRefinement::unified_cache_branch_source(
            model,
        ).branch_fill_aus_shared_projection_inv(aus),
{
    let state = model.program.state;
    let branch_src = UnifiedCacheBranchRefinement::unified_cache_branch_source(model);
    let system = unified_cache_system_i(model);
    let owned_aus = branch_src.branch_projection_aus() + aus;

    branch_projection_aus_subset_system_branch_owned(model);
    assert(system.allocation_wf());
    assert(system.component_disjoint());
    assert(system.free_aus == state.free_aus);
    assert(state.free_aus.disjoint(system.component_owned_aus()));
    assert(system.component_owned_aus().contains(spec_superblock_addr().au));
    assert(owned_aus.disjoint(CrashAwareCachingDiskSystem::State::reserved_aus())) by {
        assert forall |au: AU| #[trigger] owned_aus.contains(au)
            implies !CrashAwareCachingDiskSystem::State::reserved_aus().contains(au) by {
            if branch_src.branch_projection_aus().contains(au) {
                assert(branch_src.branch_projection_aus() <= system.branch_owned_aus());
                assert(system.branch_owned_aus().contains(au));
                assert(system.component_owned_aus().contains(au));
            } else {
                assert(aus.contains(au));
                assert(state.free_aus.contains(au));
                assert(!system.component_owned_aus().contains(au));
            }
        }
    }
    assert forall |addr: Address| #[trigger] filled_cache_status(state.cache).contains_key(addr)
        && filled_cache_status(state.cache)[addr] == PageStatus::Clean
        && addresses_in_aus(owned_aus).contains(addr)
        && project_persistent(model.disk, owned_aus).contains_key(addr)
        implies {
            &&& model.disk.content[addr] == cache_filled_page(state.cache, addr)
        } by {
        assert(owned_aus.contains(addr.au));
        assert(model.disk.content.contains_key(addr));
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(CrashAwareCachingDiskSystem::State::reserved_aus().contains(addr.au));
                assert(false);
            }
        }
        assert(unified_cache_shared_cache_disk_inv(model));
    }
    assert forall |addr: Address| {
        &&& #[trigger] model.disk.content.contains_key(addr)
        &&& addresses_in_aus(owned_aus).contains(addr)
    } implies addr.wf() by {
        assert(owned_aus.contains(addr.au));
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(CrashAwareCachingDiskSystem::State::reserved_aus().contains(addr.au));
                assert(false);
            }
        }
        assert(unified_cache_shared_cache_disk_inv(model));
    }
    caching_disk_i_inv_from_clean_cache_coupling(state.cache, model.disk, owned_aus);
    caching_disk_i_domains_wf_from_sources(state.cache, model.disk, owned_aus);
    assert(branch_src.branch_fill_aus_shared_projection_inv(aus));
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
        unified_cache_system_i(pre).inv(),
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
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    assert(src.inv());
    assert(dst.inv());
}

pub proof fn cache_internal_preserves_all_filled_clean(
    pre_cache: Cache::State,
    post_cache: Cache::State,
)
    requires
        pre_cache.inv(),
        Cache::State::next(pre_cache, post_cache, Cache::Label::Internal{}),
        cache_all_filled_clean(pre_cache),
    ensures
        cache_all_filled_clean(post_cache),
{
    Cache::State::inv_next(pre_cache, post_cache, Cache::Label::Internal{});
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
        step,
    );

    assert forall |addr: Address| #[trigger] filled_cache_status(post_cache).contains_key(addr)
        implies filled_cache_status(post_cache)[addr] == PageStatus::Clean by {
        let post_slot = post_cache.lookup_map[addr];
        assert(cache_filled_addr(post_cache, addr));
        match step {
            Cache::Step::reserve(new_slots_mapping) => {
                assert(Cache::State::reserve(
                    pre_cache,
                    post_cache,
                    Cache::Label::Internal{},
                    new_slots_mapping,
                )) by {
                }
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                );
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                assert(post_cache.status_map == pre_cache.status_map);
                assert(!updated_entries.contains_key(post_slot)) by {
                    if updated_entries.contains_key(post_slot) {
                        assert(post_cache.entries[post_slot] == Entry::Reserved{
                            addr: new_slots_mapping[post_slot],
                        });
                        assert(post_cache.entries[post_slot] is Filled);
                        assert(false);
                    }
                }
                assert(!new_slots_mapping.invert().contains_key(addr)) by {
                    if new_slots_mapping.invert().contains_key(addr) {
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        let new_slot = new_slots_mapping.invert()[addr];
                        assert(new_slots_mapping.contains_pair(new_slot, addr));
                        assert(post_cache.lookup_map[addr] == new_slot);
                        assert(updated_entries.contains_key(new_slot));
                        assert(false);
                    }
                }
                assert(post_cache.lookup_map
                    == pre_cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                assert(pre_cache.lookup_map.contains_key(addr));
                assert(pre_cache.lookup_map[addr] == post_slot);
                assert(pre_cache.entries[post_slot] == post_cache.entries[post_slot]);
                assert(pre_cache.status_map[post_slot] == post_cache.status_map[post_slot]);
            },
            Cache::Step::evict(evicted_slots) => {
                assert(Cache::State::evict(
                    pre_cache,
                    post_cache,
                    Cache::Label::Internal{},
                    evicted_slots,
                )) by {
                }
                let evicted_addrs = Map::new(
                    |slot: Slot| evicted_slots.contains(slot),
                    |slot: Slot| pre_cache.entries[slot].get_addr(),
                ).values();
                assert(post_cache.lookup_map == pre_cache.lookup_map.remove_keys(evicted_addrs));
                assert(!evicted_addrs.contains(addr)) by {
                    if evicted_addrs.contains(addr) {
                        assert(!post_cache.lookup_map.contains_key(addr));
                        assert(false);
                    }
                }
                assert(pre_cache.lookup_map.contains_key(addr));
                assert(pre_cache.lookup_map[addr] == post_slot);
                assert(!evicted_slots.contains(post_slot)) by {
                    if evicted_slots.contains(post_slot) {
                        assert(evicted_addrs.contains(addr));
                        assert(false);
                    }
                }
                let updated_entries = Map::new(
                    |slot| evicted_slots.contains(slot),
                    |slot| Entry::Empty,
                );
                let updated_status_map = Map::new(
                    |slot| evicted_slots.contains(slot),
                    |slot| Status::NotFilled,
                );
                assert(post_cache.entries == pre_cache.entries.union_prefer_right(updated_entries));
                assert(post_cache.status_map
                    == pre_cache.status_map.union_prefer_right(updated_status_map));
                assert(!updated_entries.contains_key(post_slot));
                assert(!updated_status_map.contains_key(post_slot));
                assert(pre_cache.entries[post_slot] == post_cache.entries[post_slot]);
                assert(pre_cache.status_map[post_slot] == post_cache.status_map[post_slot]);
            },
            Cache::Step::noop() => {
                assert(Cache::State::noop(pre_cache, post_cache, Cache::Label::Internal{})) by {
                }
                assert(post_cache == pre_cache);
            },
            _ => {
                assert(false);
            },
        }
        assert(filled_cache_status(pre_cache).contains_key(addr));
        assert(cache_status_i(post_cache, addr) == cache_status_i(pre_cache, addr));
        assert(filled_cache_status(post_cache)[addr] == filled_cache_status(pre_cache)[addr]);
        assert(filled_cache_status(pre_cache)[addr] == PageStatus::Clean);
    }
}

pub proof fn cache_disk_ops_begin_preserves_all_filled_clean_and_read_requests(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    req_map: Map<ID, DiskRequest>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(
            pre_cache,
            post_cache,
            Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
        ),
        cache_all_filled_clean(pre_cache),
    ensures
        cache_all_filled_clean(post_cache),
        forall |id: ID| #[trigger] req_map.contains_key(id) ==> req_map[id] is ReadReq,
{
    let lbl = Cache::Label::DiskOps{
        requests: req_map.values(),
        responses: Map::<Address, DiskResponse>::empty(),
    };
    Cache::State::inv_next(pre_cache, post_cache, lbl);
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_cache,
        post_cache,
        lbl,
        step,
    );

    match step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert(Cache::State::load_initiate(pre_cache, post_cache, lbl, new_slots_mapping)) by {
            }
        },
        Cache::Step::writeback_initiate() => {
            assert(Cache::State::writeback_initiate(pre_cache, post_cache, lbl)) by {
            }
            assert(!req_map.values().is_empty());
            let req = choose |req: DiskRequest| req_map.values().contains(req);
            assert(req_map.values().contains(req));
            assert(pre_cache.valid_writeback_requests(req_map.values()));
            assert(req is WriteReq);
            let addr = req->to;
            let slot = pre_cache.lookup_map[addr];
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.entries[slot] == Entry::Filled{addr, data: req->data});
            assert(pre_cache.status_map[slot] is Dirty);
            assert(filled_cache_status(pre_cache).contains_key(addr));
            assert(cache_status_i(pre_cache, addr) == PageStatus::Dirty);
            assert(filled_cache_status(pre_cache)[addr] == PageStatus::Dirty);
            assert(filled_cache_status(pre_cache)[addr] == PageStatus::Clean);
            assert(false);
        },
        _ => {
            assert(false);
        },
    }

    assert forall |id: ID| #[trigger] req_map.contains_key(id)
        implies req_map[id] is ReadReq by {
        match step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                assert(req_map.values().contains(req_map[id]));
            },
            Cache::Step::writeback_initiate() => {
                assert(false);
            },
            _ => {
                assert(false);
            },
        }
    }

    assert forall |addr: Address| #[trigger] filled_cache_status(post_cache).contains_key(addr)
        implies filled_cache_status(post_cache)[addr] == PageStatus::Clean by {
        let post_slot = post_cache.lookup_map[addr];
        assert(cache_filled_addr(post_cache, addr));
        match step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                assert(Cache::State::load_initiate(pre_cache, post_cache, lbl, new_slots_mapping));
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                );
                assert(!new_slots_mapping.invert().contains_key(addr)) by {
                    if new_slots_mapping.invert().contains_key(addr) {
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        let new_slot = new_slots_mapping.invert()[addr];
                        assert(new_slots_mapping.contains_pair(new_slot, addr));
                        assert(post_cache.lookup_map[addr] == new_slot);
                        assert(updated_entries.contains_key(new_slot));
                        assert(post_cache.entries
                            == pre_cache.entries.union_prefer_right(updated_entries));
                        assert(post_cache.entries[new_slot] == Entry::Loading{addr});
                        assert(post_cache.entries[post_slot] is Filled);
                        assert(false);
                    }
                }
                assert(post_cache.lookup_map
                    == pre_cache.lookup_map.union_prefer_right(new_slots_mapping.invert()));
                assert(pre_cache.lookup_map.contains_key(addr));
                assert(pre_cache.lookup_map[addr] == post_slot);
                assert(!updated_entries.contains_key(post_slot));
                assert(post_cache.entries
                    == pre_cache.entries.union_prefer_right(updated_entries));
                assert(post_cache.entries[post_slot] == pre_cache.entries[post_slot]);
                assert(post_cache.status_map == pre_cache.status_map);
                assert(pre_cache.status_map[post_slot] == post_cache.status_map[post_slot]);
            },
            Cache::Step::writeback_initiate() => {
                assert(false);
            },
            _ => {
                assert(false);
            },
        }
        assert(filled_cache_status(pre_cache).contains_key(addr));
        assert(cache_status_i(post_cache, addr) == cache_status_i(pre_cache, addr));
        assert(filled_cache_status(post_cache)[addr] == filled_cache_status(pre_cache)[addr]);
        assert(filled_cache_status(pre_cache)[addr] == PageStatus::Clean);
    }
}

pub proof fn cache_disk_ops_end_preserves_all_filled_clean(
    pre_cache: Cache::State,
    post_cache: Cache::State,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        pre_cache.inv(),
        Cache::State::next(
            pre_cache,
            post_cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps},
        ),
        cache_all_filled_clean(pre_cache),
    ensures
        cache_all_filled_clean(post_cache),
{
    let lbl = Cache::Label::DiskOps{
        requests: Set::<DiskRequest>::empty(),
        responses: cache_resps,
    };
    Cache::State::inv_next(pre_cache, post_cache, lbl);
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_cache,
        post_cache,
        lbl,
        step,
    );

    match step {
        Cache::Step::load_complete() => {
            assert(Cache::State::load_complete(pre_cache, post_cache, lbl)) by {
            }
        },
        Cache::Step::writeback_complete() => {
            assert(Cache::State::writeback_complete(pre_cache, post_cache, lbl)) by {
            }
            assert(!cache_resps.is_empty());
            let addr = choose |addr: Address| cache_resps.contains_key(addr);
            assert(cache_resps.contains_key(addr));
            assert(pre_cache.valid_writeback_responses(cache_resps));
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.entries[pre_cache.lookup_map[addr]] is Filled);
            assert(pre_cache.status_map[pre_cache.lookup_map[addr]] is Writeback);
            assert(filled_cache_status(pre_cache).contains_key(addr));
            assert(cache_status_i(pre_cache, addr) == PageStatus::Writeback);
            assert(filled_cache_status(pre_cache)[addr] == PageStatus::Writeback);
            assert(filled_cache_status(pre_cache)[addr] == PageStatus::Clean);
            assert(false);
        },
        _ => {
            assert(false);
        },
    }

    assert forall |addr: Address| #[trigger] filled_cache_status(post_cache).contains_key(addr)
        implies filled_cache_status(post_cache)[addr] == PageStatus::Clean by {
        let post_slot = post_cache.lookup_map[addr];
        assert(cache_filled_addr(post_cache, addr));
        match step {
            Cache::Step::load_complete() => {
                assert(Cache::State::load_complete(pre_cache, post_cache, lbl));
                let slot_addr_map = pre_cache.lookup_map.restrict(cache_resps.dom()).invert();
                let updated_entries = Map::new(
                    |slot| slot_addr_map.contains_key(slot),
                    |slot| Entry::Filled{
                        addr: slot_addr_map[slot],
                        data: cache_resps[slot_addr_map[slot]]->data,
                    },
                );
                let updated_status_map = Map::new(
                    |slot: Slot| slot_addr_map.contains_key(slot),
                    |slot: Slot| Status::Clean,
                );
                if cache_resps.contains_key(addr) {
                    assert(post_cache.lookup_map == pre_cache.lookup_map);
                    assert(pre_cache.lookup_map.contains_key(addr));
                    assert(pre_cache.lookup_map[addr] == post_slot);
                    assert(slot_addr_map.contains_key(post_slot)) by {
                        if !slot_addr_map.contains_key(post_slot) {
                            assert(cache_resps.contains_key(addr));
                            assert(pre_cache.lookup_map.restrict(cache_resps.dom()).contains_pair(
                                addr,
                                post_slot,
                            ));
                            assert(false);
                        }
                    }
                    assert(updated_status_map.contains_key(post_slot));
                    assert(post_cache.status_map
                        == pre_cache.status_map.union_prefer_right(updated_status_map));
                    assert(post_cache.status_map[post_slot] == Status::Clean);
                    assert(cache_status_i(post_cache, addr) == PageStatus::Clean);
                } else {
                    assert(post_cache.lookup_map == pre_cache.lookup_map);
                    assert(pre_cache.lookup_map.contains_key(addr));
                    assert(pre_cache.lookup_map[addr] == post_slot);
                    assert(!slot_addr_map.contains_key(post_slot)) by {
                        if slot_addr_map.contains_key(post_slot) {
                            assert(cache_resps.contains_key(slot_addr_map[post_slot]));
                            assert(slot_addr_map[post_slot] == addr);
                            assert(false);
                        }
                    }
                    assert(!updated_entries.contains_key(post_slot));
                    assert(!updated_status_map.contains_key(post_slot));
                    assert(post_cache.entries
                        == pre_cache.entries.union_prefer_right(updated_entries));
                    assert(post_cache.status_map
                        == pre_cache.status_map.union_prefer_right(updated_status_map));
                    assert(post_cache.entries[post_slot] == pre_cache.entries[post_slot]);
                    assert(post_cache.status_map[post_slot] == pre_cache.status_map[post_slot]);
                    assert(filled_cache_status(pre_cache).contains_key(addr));
                    assert(cache_status_i(post_cache, addr) == cache_status_i(pre_cache, addr));
                    assert(filled_cache_status(post_cache)[addr]
                        == filled_cache_status(pre_cache)[addr]);
                    assert(filled_cache_status(pre_cache)[addr] == PageStatus::Clean);
                }
            },
            Cache::Step::writeback_complete() => {
                assert(false);
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn cache_access_preserves_cache_request_wf(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
    ensures
        unified_cache_cache_request_wf(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let cache_lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();

    assert(post_state.outstanding_cache_reqs.is_injective());
    assert(!post_state.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
    assert(post_state.outstanding_cache_reqs.values() <= post_state.cache.lookup_map.dom()) by {
        assert forall |addr: Address| #[trigger] post_state.outstanding_cache_reqs.values().contains(addr)
            implies post_state.cache.lookup_map.dom().contains(addr) by {
            let id = choose |id: ID| #![auto] {
                &&& post_state.outstanding_cache_reqs.contains_key(id)
                &&& post_state.outstanding_cache_reqs[id] == addr
            };
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
            assert(pre_state.cache.lookup_map.dom().contains(addr));
            assert(pre_state.cache.lookup_map.contains_key(addr));
            assert(!writes.contains_key(addr)) by {
                if writes.contains_key(addr) {
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                        Cache::Step::access(),
                    ));
                    assert(pre_state.cache.valid_write(addr));
                    let slot = pre_state.cache.lookup_map[addr];
                    match pre_state.cache.entries[slot] {
                        Entry::Loading{addr: entry_addr} => {
                            assert(entry_addr == addr);
                            assert(false);
                        },
                        Entry::Filled{addr: entry_addr, data} => {
                            assert(entry_addr == addr);
                            assert(pre_state.cache.status_map[slot] is Writeback);
                            assert(false);
                        },
                        _ => {
                            assert(false);
                        },
                    }
                }
            }
            Cache::State::access_unwritten_addr_unchanged(
                pre_state.cache,
                post_state.cache,
                reads,
                writes,
                addr,
            );
        }
    }
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.contains_key(id) implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let slot = post_state.cache.lookup_map[addr];
        match post_state.cache.entries[slot] {
            Entry::Loading{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && post_state.cache.status_map[slot] is Writeback,
            _ => false,
        }
    } by {
        let addr = post_state.outstanding_cache_reqs[id];
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(pre_state.outstanding_cache_reqs[id] == addr);
        assert(pre_state.cache.lookup_map.contains_key(addr));
        assert(!writes.contains_key(addr)) by {
            if writes.contains_key(addr) {
                reveal(Cache::State::next);
                reveal(Cache::State::next_by);
                assert(Cache::State::next_by(
                    pre_state.cache,
                    post_state.cache,
                    cache_lbl,
                    Cache::Step::access(),
                ));
                assert(pre_state.cache.valid_write(addr));
                let slot = pre_state.cache.lookup_map[addr];
                match pre_state.cache.entries[slot] {
                    Entry::Loading{addr: entry_addr} => {
                        assert(entry_addr == addr);
                        assert(false);
                    },
                    Entry::Filled{addr: entry_addr, data} => {
                        assert(entry_addr == addr);
                        assert(pre_state.cache.status_map[slot] is Writeback);
                        assert(false);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        }
        Cache::State::access_unwritten_addr_unchanged(
            pre_state.cache,
            post_state.cache,
            reads,
            writes,
            addr,
        );
        let pre_slot = pre_state.cache.lookup_map[addr];
        let post_slot = post_state.cache.lookup_map[addr];
        assert(post_slot == pre_slot);
        match pre_state.cache.entries[pre_slot] {
            Entry::Loading{addr: entry_addr} => {
                assert(entry_addr == addr);
                assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[pre_slot]);
            },
            Entry::Filled{addr: entry_addr, data} => {
                assert(entry_addr == addr);
                assert(pre_state.cache.status_map[pre_slot] is Writeback);
                assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[pre_slot]);
                assert(post_state.cache.status_map[post_slot] == pre_state.cache.status_map[pre_slot]);
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn cache_access_preserves_cache_disk_response_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        unified_cache_cache_disk_response_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.disk.content == pre.disk.content,
        post.disk.responses == pre.disk.responses,
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
    ensures
        unified_cache_cache_disk_response_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let cache_lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();

    assert forall |id: ID| {
        &&& #[trigger] post.disk.responses.contains_key(id)
        &&& post.program.state.outstanding_cache_reqs.contains_key(id)
    } implies {
        let addr = post.program.state.outstanding_cache_reqs[id];
        let resp = post.disk.responses[id];
        &&& resp is ReadResp ==> {
            &&& resp->data == post.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& cache_filled_addr(post.program.state.cache, addr)
            &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
        }
    } by {
        assert(pre.disk.responses.contains_key(id));
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(post_state.outstanding_cache_reqs[id] == pre_state.outstanding_cache_reqs[id]);
        let addr = pre_state.outstanding_cache_reqs[id];
        assert(post.disk.responses[id] == pre.disk.responses[id]);
        assert(post.disk.content == pre.disk.content);
        assert(unified_cache_cache_disk_response_inv(pre));
        if pre.disk.responses[id] is WriteResp {
            assert(cache_filled_addr(pre_state.cache, addr));
            let slot = pre_state.cache.lookup_map[addr];
            assert(pre_state.cache.entries[slot] is Filled);
            assert(match pre_state.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && pre_state.cache.status_map[slot] is Writeback,
                _ => false,
            });
            assert(pre_state.cache.status_map[slot] is Writeback);
            assert(!writes.contains_key(addr)) by {
                if writes.contains_key(addr) {
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                        Cache::Step::access(),
                    ));
                    assert(pre_state.cache.valid_write(addr));
                    assert(false);
                }
            }
            Cache::State::access_unwritten_addr_unchanged(
                pre_state.cache,
                post_state.cache,
                reads,
                writes,
                addr,
            );
            assert(cache_filled_addr(post_state.cache, addr));
            assert(cache_filled_page(post_state.cache, addr)
                == cache_filled_page(pre_state.cache, addr));
        }
    }
}

pub proof fn cache_access_preserves_outstanding_cache_reqs_disk_backed(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        unified_cache_outstanding_cache_reqs_disk_backed_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.disk.requests == pre.disk.requests,
        post.disk.responses == pre.disk.responses,
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
    ensures
        unified_cache_outstanding_cache_reqs_disk_backed_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let cache_lbl = Cache::Label::Access{reads, writes};
    cache_access_preserves_cache_request_wf(pre, post, reads, writes);

    assert(post_state.outstanding_cache_reqs.is_injective());
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        implies disk_has_pending_id(post.disk, id) by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(disk_has_pending_id(pre.disk, id));
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map.contains_key(addr)
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]] is Filled
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]]->data == req->data
            &&& post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == Status::Writeback{}
        }
    } by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        assert(post_state.outstanding_cache_reqs[id] == pre_state.outstanding_cache_reqs[id]);
        assert(post.disk.requests[id] == pre.disk.requests[id]);
        let addr = pre_state.outstanding_cache_reqs[id];
        let req = pre.disk.requests[id];
        assert(req.addr() == addr);
        if req is WriteReq {
            assert(pre_state.cache.lookup_map.contains_key(addr));
            let pre_slot = pre_state.cache.lookup_map[addr];
            assert(pre_state.cache.entries[pre_slot] is Filled);
            assert(pre_state.cache.entries[pre_slot]->data == req->data);
            assert(pre_state.cache.status_map[pre_slot] == Status::Writeback{});
            assert(!writes.contains_key(addr)) by {
                if writes.contains_key(addr) {
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                        Cache::Step::access(),
                    ));
                    assert(pre_state.cache.valid_write(addr));
                    assert(false);
                }
            }
            Cache::State::access_unwritten_addr_unchanged(
                pre_state.cache,
                post_state.cache,
                reads,
                writes,
                addr,
            );
            assert(post_state.cache.lookup_map[addr] == pre_slot);
            assert(post_state.cache.entries[post_state.cache.lookup_map[addr]]
                == pre_state.cache.entries[pre_slot]);
            assert(post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == pre_state.cache.status_map[pre_slot]);
        }
    }
}

pub proof fn cache_access_preserves_shared_cache_disk_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_shared_cache_disk_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.disk.content == pre.disk.content,
        writes.dom() <= Set::new(|addr: Address| addr.wf()),
    ensures
        unified_cache_shared_cache_disk_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let cache_lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre_state.cache, post_state.cache, cache_lbl);
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step|
        Cache::State::next_by(pre_state.cache, post_state.cache, cache_lbl, step);
    match step {
        Cache::Step::access() => {},
        _ => {
            assert(false);
        },
    }

    assert forall |addr: Address| #[trigger] filled_cache_pages(post_state.cache).contains_key(addr)
        implies addr.wf() by {
        assert(cache_filled_addr(post_state.cache, addr));
        if writes.contains_key(addr) {
            assert(writes.dom().contains(addr));
        } else {
            Cache::State::access_unwritten_addr_unchanged(
                pre_state.cache,
                post_state.cache,
                reads,
                writes,
                addr,
            );
            assert(cache_filled_addr(pre_state.cache, addr));
            assert(filled_cache_pages(pre_state.cache).contains_key(addr));
            assert(unified_cache_shared_cache_disk_inv(pre));
        }
    }
    assert forall |addr: Address| #[trigger] post.disk.content.contains_key(addr)
        && addr != spec_superblock_addr()
        implies addr.wf() by {
        assert(pre.disk.content.contains_key(addr));
        assert(unified_cache_shared_cache_disk_inv(pre));
    }
    assert forall |addr: Address| {
        &&& #[trigger] filled_cache_status(post_state.cache).contains_key(addr)
        &&& filled_cache_status(post_state.cache)[addr] == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& post.disk.content.contains_key(addr)
    } implies post.disk.content[addr] == cache_filled_page(post_state.cache, addr) by {
        assert(cache_filled_addr(post_state.cache, addr));
        if writes.contains_key(addr) {
            assert(Cache::State::access(pre_state.cache, post_state.cache, cache_lbl));
            let slot = pre_state.cache.lookup_map[addr];
            assert(pre_state.cache.valid_write(addr));
            assert(pre_state.cache.lookup_map.contains_key(addr));
            let restricted = pre_state.cache.lookup_map.restrict(writes.dom());
            assert(restricted.contains_key(addr));
            assert(restricted[addr] == slot);
            assert(restricted.values().contains(slot));
            assert(pre_state.cache.write_updated_status(writes).contains_key(slot));
            assert(post_state.cache.status_map[slot] == Status::Dirty);
            assert(post_state.cache.lookup_map[addr] == slot) by {
                assert(post_state.cache.build_lookup_map_props(post_state.cache.lookup_map));
            }
            assert(cache_status_i(post_state.cache, addr) == PageStatus::Dirty);
            assert(filled_cache_status(post_state.cache)[addr] == PageStatus::Dirty);
            assert(false);
        } else {
            Cache::State::access_unwritten_addr_unchanged(
                pre_state.cache,
                post_state.cache,
                reads,
                writes,
                addr,
            );
            assert(cache_filled_addr(pre_state.cache, addr));
            assert(filled_cache_status(pre_state.cache).contains_key(addr));
            assert(filled_cache_status(pre_state.cache)[addr] == PageStatus::Clean);
            assert(cache_filled_page(post_state.cache, addr)
                == cache_filled_page(pre_state.cache, addr));
            assert(unified_cache_shared_cache_disk_inv(pre));
            assert(pre.disk.content.contains_key(addr));
            assert(pre.disk.content[addr] == cache_filled_page(pre_state.cache, addr));
        }
    }
}

pub proof fn cache_io_begin_preserves_shared_cache_disk_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_shared_cache_disk_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
        ),
        post.disk.content == pre.disk.content,
    ensures
        unified_cache_shared_cache_disk_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let lbl = Cache::Label::DiskOps{
        requests: req_map.values(),
        responses: Map::<Address, DiskResponse>::empty(),
    };
    Cache::State::inv_next(pre_state.cache, post_state.cache, lbl);
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step|
        Cache::State::next_by(pre_state.cache, post_state.cache, lbl, step);
    match step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert(Cache::State::load_initiate(
                pre_state.cache,
                post_state.cache,
                lbl,
                new_slots_mapping,
            )) by {
            }
        },
        Cache::Step::writeback_initiate() => {
            assert(Cache::State::writeback_initiate(pre_state.cache, post_state.cache, lbl)) by {
            }
        },
        _ => {
            assert(false);
        },
    }

    assert forall |addr: Address| #[trigger] filled_cache_pages(post_state.cache).contains_key(addr)
        implies addr.wf() by {
        assert(cache_filled_addr(post_state.cache, addr));
        match step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                assert(Cache::State::load_initiate(
                    pre_state.cache,
                    post_state.cache,
                    lbl,
                    new_slots_mapping,
                ));
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                );
                let post_slot = post_state.cache.lookup_map[addr];
                assert(!new_slots_mapping.invert().contains_key(addr)) by {
                    if new_slots_mapping.invert().contains_key(addr) {
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        let new_slot = new_slots_mapping.invert()[addr];
                        assert(new_slots_mapping.contains_pair(new_slot, addr));
                        assert(post_state.cache.lookup_map[addr] == new_slot);
                        assert(updated_entries.contains_key(new_slot));
                        assert(post_state.cache.entries
                            == pre_state.cache.entries.union_prefer_right(updated_entries));
                        assert(post_state.cache.entries[new_slot] == Entry::Loading{addr});
                        assert(post_state.cache.entries[post_slot] is Filled);
                        assert(false);
                    }
                }
                assert(pre_state.cache.lookup_map.contains_key(addr));
                assert(pre_state.cache.lookup_map[addr] == post_slot);
                assert(!updated_entries.contains_key(post_slot));
                assert(post_state.cache.entries
                    == pre_state.cache.entries.union_prefer_right(updated_entries));
                assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[post_slot]);
                assert(cache_filled_addr(pre_state.cache, addr));
                assert(filled_cache_pages(pre_state.cache).contains_key(addr));
                assert(unified_cache_shared_cache_disk_inv(pre));
            },
            Cache::Step::writeback_initiate() => {
                assert(Cache::State::writeback_initiate(pre_state.cache, post_state.cache, lbl));
                assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                assert(post_state.cache.entries == pre_state.cache.entries);
                assert(cache_filled_addr(pre_state.cache, addr));
                assert(filled_cache_pages(pre_state.cache).contains_key(addr));
                assert(unified_cache_shared_cache_disk_inv(pre));
            },
            _ => {
                assert(false);
            },
        }
    }
    assert forall |addr: Address| #[trigger] post.disk.content.contains_key(addr)
        && addr != spec_superblock_addr()
        implies addr.wf() by {
        assert(pre.disk.content.contains_key(addr));
        assert(unified_cache_shared_cache_disk_inv(pre));
    }
    assert forall |addr: Address| {
        &&& #[trigger] filled_cache_status(post_state.cache).contains_key(addr)
        &&& filled_cache_status(post_state.cache)[addr] == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& post.disk.content.contains_key(addr)
    } implies post.disk.content[addr] == cache_filled_page(post_state.cache, addr) by {
        assert(cache_filled_addr(post_state.cache, addr));
        match step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                assert(Cache::State::load_initiate(
                    pre_state.cache,
                    post_state.cache,
                    lbl,
                    new_slots_mapping,
                ));
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Loading{addr: new_slots_mapping[slot]},
                );
                let post_slot = post_state.cache.lookup_map[addr];
                assert(!new_slots_mapping.invert().contains_key(addr)) by {
                    if new_slots_mapping.invert().contains_key(addr) {
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        let new_slot = new_slots_mapping.invert()[addr];
                        assert(new_slots_mapping.contains_pair(new_slot, addr));
                        assert(post_state.cache.lookup_map[addr] == new_slot);
                        assert(updated_entries.contains_key(new_slot));
                        assert(post_state.cache.entries
                            == pre_state.cache.entries.union_prefer_right(updated_entries));
                        assert(post_state.cache.entries[new_slot] == Entry::Loading{addr});
                        assert(post_state.cache.entries[post_slot] is Filled);
                        assert(false);
                    }
                }
                assert(pre_state.cache.lookup_map.contains_key(addr));
                assert(pre_state.cache.lookup_map[addr] == post_slot);
                assert(!updated_entries.contains_key(post_slot));
                assert(post_state.cache.entries
                    == pre_state.cache.entries.union_prefer_right(updated_entries));
                assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[post_slot]);
                assert(post_state.cache.status_map == pre_state.cache.status_map);
                assert(cache_filled_addr(pre_state.cache, addr));
                assert(filled_cache_status(pre_state.cache).contains_key(addr));
                assert(filled_cache_status(pre_state.cache)[addr] == PageStatus::Clean);
                assert(cache_filled_page(post_state.cache, addr)
                    == cache_filled_page(pre_state.cache, addr));
                assert(unified_cache_shared_cache_disk_inv(pre));
            },
            Cache::Step::writeback_initiate() => {
                assert(Cache::State::writeback_initiate(pre_state.cache, post_state.cache, lbl));
                let writeback_slots = Map::new(
                    |req: DiskRequest| req_map.values().contains(req),
                    |req: DiskRequest| pre_state.cache.lookup_map[req->to],
                ).values();
                let post_slot = post_state.cache.lookup_map[addr];
                assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                assert(post_state.cache.entries == pre_state.cache.entries);
                assert(!writeback_slots.contains(post_slot)) by {
                    if writeback_slots.contains(post_slot) {
                        let updated_status_map = Map::new(
                            |slot: Slot| writeback_slots.contains(slot),
                            |slot: Slot| Status::Writeback{},
                        );
                        assert(updated_status_map.contains_key(post_slot));
                        assert(post_state.cache.status_map
                            == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                        assert(post_state.cache.status_map[post_slot] is Writeback);
                        assert(cache_status_i(post_state.cache, addr) == PageStatus::Writeback);
                        assert(filled_cache_status(post_state.cache)[addr] == PageStatus::Writeback);
                        assert(false);
                    }
                }
                let updated_status_map = Map::new(
                    |slot: Slot| writeback_slots.contains(slot),
                    |slot: Slot| Status::Writeback{},
                );
                assert(!updated_status_map.contains_key(post_slot));
                assert(post_state.cache.status_map
                    == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                assert(post_state.cache.status_map[post_slot]
                    == pre_state.cache.status_map[post_slot]);
                assert(cache_filled_addr(pre_state.cache, addr));
                assert(filled_cache_status(pre_state.cache).contains_key(addr));
                assert(filled_cache_status(pre_state.cache)[addr] == PageStatus::Clean);
                assert(cache_filled_page(post_state.cache, addr)
                    == cache_filled_page(pre_state.cache, addr));
                assert(unified_cache_shared_cache_disk_inv(pre));
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn cache_io_end_preserves_shared_cache_disk_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_shared_cache_disk_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps},
        ),
        post.disk.content == pre.disk.content,
        !cache_resps.contains_key(spec_superblock_addr()),
        cache_resps.dom() <= Set::new(|addr: Address| addr.wf()),
        forall |addr: Address| #[trigger] cache_resps.contains_key(addr) ==> {
            &&& cache_resps[addr] is ReadResp ==> {
                pre.disk.content.contains_key(addr) ==> cache_resps[addr]->data
                    == pre.disk.content[addr]
            }
            &&& cache_resps[addr] is WriteResp ==> {
                &&& pre.disk.content.contains_key(addr)
                &&& cache_filled_addr(pre.program.state.cache, addr)
                &&& pre.disk.content[addr] == cache_filled_page(pre.program.state.cache, addr)
            }
        },
    ensures
        unified_cache_shared_cache_disk_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let lbl = Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps};
    Cache::State::inv_next(pre_state.cache, post_state.cache, lbl);
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step|
        Cache::State::next_by(pre_state.cache, post_state.cache, lbl, step);
    match step {
        Cache::Step::load_complete() => {
            assert(Cache::State::load_complete(pre_state.cache, post_state.cache, lbl)) by {
            }
        },
        Cache::Step::writeback_complete() => {
            assert(Cache::State::writeback_complete(pre_state.cache, post_state.cache, lbl)) by {
            }
        },
        _ => {
            assert(false);
        },
    }

    assert forall |addr: Address| #[trigger] filled_cache_pages(post_state.cache).contains_key(addr)
        implies addr.wf() by {
        assert(cache_filled_addr(post_state.cache, addr));
        match step {
            Cache::Step::load_complete() => {
                assert(Cache::State::load_complete(pre_state.cache, post_state.cache, lbl));
                if cache_resps.contains_key(addr) {
                    assert(addr.wf());
                } else {
                    let post_slot = post_state.cache.lookup_map[addr];
                    assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                    assert(pre_state.cache.lookup_map.contains_key(addr));
                    assert(pre_state.cache.lookup_map[addr] == post_slot);
                    let slot_addr_map = pre_state.cache.lookup_map.restrict(cache_resps.dom()).invert();
                    let updated_entries = Map::new(
                        |slot| slot_addr_map.contains_key(slot),
                        |slot| Entry::Filled{
                            addr: slot_addr_map[slot],
                            data: cache_resps[slot_addr_map[slot]]->data,
                        },
                    );
                    assert(!slot_addr_map.contains_key(post_slot)) by {
                        if slot_addr_map.contains_key(post_slot) {
                            assert(cache_resps.contains_key(slot_addr_map[post_slot]));
                            assert(slot_addr_map[post_slot] == addr);
                            assert(false);
                        }
                    }
                    assert(!updated_entries.contains_key(post_slot));
                    assert(post_state.cache.entries
                        == pre_state.cache.entries.union_prefer_right(updated_entries));
                    assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[post_slot]);
                    assert(cache_filled_addr(pre_state.cache, addr));
                    assert(filled_cache_pages(pre_state.cache).contains_key(addr));
                    assert(unified_cache_shared_cache_disk_inv(pre));
                }
            },
            Cache::Step::writeback_complete() => {
                assert(Cache::State::writeback_complete(pre_state.cache, post_state.cache, lbl));
                assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                assert(post_state.cache.entries == pre_state.cache.entries);
                assert(cache_filled_addr(pre_state.cache, addr));
                assert(filled_cache_pages(pre_state.cache).contains_key(addr));
                assert(unified_cache_shared_cache_disk_inv(pre));
            },
            _ => {
                assert(false);
            },
        }
    }
    assert forall |addr: Address| #[trigger] post.disk.content.contains_key(addr)
        && addr != spec_superblock_addr()
        implies addr.wf() by {
        assert(pre.disk.content.contains_key(addr));
        assert(unified_cache_shared_cache_disk_inv(pre));
    }
    assert forall |addr: Address| {
        &&& #[trigger] filled_cache_status(post_state.cache).contains_key(addr)
        &&& filled_cache_status(post_state.cache)[addr] == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& post.disk.content.contains_key(addr)
    } implies post.disk.content[addr] == cache_filled_page(post_state.cache, addr) by {
        assert(cache_filled_addr(post_state.cache, addr));
        match step {
            Cache::Step::load_complete() => {
                assert(Cache::State::load_complete(pre_state.cache, post_state.cache, lbl));
                if cache_resps.contains_key(addr) {
                    assert(cache_resps[addr] is ReadResp);
                    assert(pre.disk.content.contains_key(addr));
                    let post_slot = post_state.cache.lookup_map[addr];
                    assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                    let slot_addr_map = pre_state.cache.lookup_map.restrict(cache_resps.dom()).invert();
                    assert(slot_addr_map.contains_key(post_slot)) by {
                        if !slot_addr_map.contains_key(post_slot) {
                            let updated_status_map = Map::new(
                                |slot: Slot| slot_addr_map.contains_key(slot),
                                |slot: Slot| Status::Clean,
                            );
                            assert(post_state.cache.status_map
                                == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                            assert(post_state.cache.status_map[post_slot]
                                == pre_state.cache.status_map[post_slot]);
                            assert(pre_state.cache.valid_load_responses(cache_resps));
                            assert(pre_state.cache.entries[post_slot] is Loading);
                            assert(false);
                        }
                    }
                    assert(slot_addr_map[post_slot] == addr);
                    let updated_entries = Map::new(
                        |slot| slot_addr_map.contains_key(slot),
                        |slot| Entry::Filled{
                            addr: slot_addr_map[slot],
                            data: cache_resps[slot_addr_map[slot]]->data,
                        },
                    );
                    assert(updated_entries.contains_key(post_slot));
                    assert(post_state.cache.entries
                        == pre_state.cache.entries.union_prefer_right(updated_entries));
                    assert(post_state.cache.entries[post_slot] == Entry::Filled{
                        addr,
                        data: cache_resps[addr]->data,
                    });
                    assert(cache_filled_page(post_state.cache, addr) == cache_resps[addr]->data);
                    assert(cache_resps[addr]->data == pre.disk.content[addr]);
                } else {
                    let post_slot = post_state.cache.lookup_map[addr];
                    assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                    assert(pre_state.cache.lookup_map.contains_key(addr));
                    assert(pre_state.cache.lookup_map[addr] == post_slot);
                    let slot_addr_map = pre_state.cache.lookup_map.restrict(cache_resps.dom()).invert();
                    let updated_entries = Map::new(
                        |slot| slot_addr_map.contains_key(slot),
                        |slot| Entry::Filled{
                            addr: slot_addr_map[slot],
                            data: cache_resps[slot_addr_map[slot]]->data,
                        },
                    );
                    let updated_status_map = Map::new(
                        |slot: Slot| slot_addr_map.contains_key(slot),
                        |slot: Slot| Status::Clean,
                    );
                    assert(!slot_addr_map.contains_key(post_slot)) by {
                        if slot_addr_map.contains_key(post_slot) {
                            assert(cache_resps.contains_key(slot_addr_map[post_slot]));
                            assert(slot_addr_map[post_slot] == addr);
                            assert(false);
                        }
                    }
                    assert(!updated_entries.contains_key(post_slot));
                    assert(!updated_status_map.contains_key(post_slot));
                    assert(post_state.cache.entries
                        == pre_state.cache.entries.union_prefer_right(updated_entries));
                    assert(post_state.cache.status_map
                        == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                    assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[post_slot]);
                    assert(post_state.cache.status_map[post_slot]
                        == pre_state.cache.status_map[post_slot]);
                    assert(cache_filled_addr(pre_state.cache, addr));
                    assert(filled_cache_status(pre_state.cache).contains_key(addr));
                    assert(filled_cache_status(pre_state.cache)[addr] == PageStatus::Clean);
                    assert(cache_filled_page(post_state.cache, addr)
                        == cache_filled_page(pre_state.cache, addr));
                    assert(unified_cache_shared_cache_disk_inv(pre));
                    assert(pre.disk.content.contains_key(addr));
                }
            },
            Cache::Step::writeback_complete() => {
                assert(Cache::State::writeback_complete(pre_state.cache, post_state.cache, lbl));
                assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                assert(post_state.cache.entries == pre_state.cache.entries);
                if cache_resps.contains_key(addr) {
                    assert(cache_resps[addr] is WriteResp);
                    assert(pre.disk.content.contains_key(addr));
                    assert(pre.disk.content[addr] == cache_filled_page(pre_state.cache, addr));
                    cache_disk_ops_end_preserves_filled_page(
                        pre_state.cache,
                        post_state.cache,
                        cache_resps,
                        addr,
                    );
                    assert(cache_filled_page(post_state.cache, addr)
                        == cache_filled_page(pre_state.cache, addr));
                } else {
                    let post_slot = post_state.cache.lookup_map[addr];
                    let resp_slots = pre_state.cache.lookup_map.restrict(cache_resps.dom()).values();
                    let updated_status_map = Map::new(
                        |slot: Slot| resp_slots.contains(slot),
                        |slot: Slot| Status::Clean,
                    );
                    assert(!resp_slots.contains(post_slot)) by {
                        if resp_slots.contains(post_slot) {
                            let resp_addr = choose |resp_addr: Address| #![auto]
                                cache_resps.contains_key(resp_addr)
                                    && pre_state.cache.lookup_map[resp_addr] == post_slot;
                            assert(pre_state.cache.lookup_map[resp_addr]
                                == pre_state.cache.lookup_map[addr]);
                            assert(pre_state.cache.lookup_map.is_injective());
                            assert(resp_addr == addr);
                            assert(false);
                        }
                    }
                    assert(!updated_status_map.contains_key(post_slot));
                    assert(post_state.cache.status_map
                        == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                    assert(post_state.cache.status_map[post_slot]
                        == pre_state.cache.status_map[post_slot]);
                    assert(cache_filled_addr(pre_state.cache, addr));
                    assert(filled_cache_status(pre_state.cache).contains_key(addr));
                    assert(filled_cache_status(pre_state.cache)[addr] == PageStatus::Clean);
                    assert(cache_filled_page(post_state.cache, addr)
                        == cache_filled_page(pre_state.cache, addr));
                    assert(unified_cache_shared_cache_disk_inv(pre));
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

pub proof fn cache_internal_preserves_outstanding_cache_entries(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
    ensures
        forall |addr: Address| {
            #[trigger] pre.program.state.outstanding_cache_reqs.values().contains(addr)
        } ==> {
            &&& pre.program.state.cache.lookup_map.contains_key(addr)
            &&& pre.program.state.cache.entries.contains_key(
                pre.program.state.cache.lookup_map[addr],
            )
            &&& post.program.state.cache.lookup_map.contains_key(addr)
            &&& post.program.state.cache.entries.contains_key(
                post.program.state.cache.lookup_map[addr],
            )
            &&& post.program.state.cache.lookup_map[addr]
                == pre.program.state.cache.lookup_map[addr]
            &&& post.program.state.cache.entries[
                post.program.state.cache.lookup_map[addr]
            ] == pre.program.state.cache.entries[
                pre.program.state.cache.lookup_map[addr]
            ]
            &&& post.program.state.cache.status_map[
                post.program.state.cache.lookup_map[addr]
            ] == pre.program.state.cache.status_map[
                pre.program.state.cache.lookup_map[addr]
            ]
        },
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let tracked_reqs = pre_state.outstanding_cache_reqs;
    let protected_addrs = tracked_reqs.values();

    Cache::State::inv_next(pre_state.cache, post_state.cache, Cache::Label::Internal{});
    assert(protected_addrs <= pre_state.cache.lookup_map.dom());
    assert forall |addr: Address| #[trigger] protected_addrs.contains(addr) implies {
        let slot = pre_state.cache.lookup_map[addr];
        match pre_state.cache.entries[slot] {
            Entry::Loading{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && pre_state.cache.status_map[slot] is Writeback,
            _ => false,
        }
    } by {
        let id = choose |id: ID| #![auto] tracked_reqs.contains_key(id) && tracked_reqs[id] == addr;
        assert(tracked_reqs.contains_key(id));
        assert(tracked_reqs[id] == addr);
        assert(unified_cache_cache_request_wf(pre));
    }
    cache_internal_preserves_protected_entries(
        pre_state.cache,
        post_state.cache,
        protected_addrs,
    );
}

pub proof fn cache_internal_preserves_cache_request_wf(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
    ensures
        unified_cache_cache_request_wf(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let tracked_reqs = pre_state.outstanding_cache_reqs;

    Cache::State::inv_next(pre_state.cache, post_state.cache, Cache::Label::Internal{});
    cache_internal_preserves_outstanding_cache_entries(pre, post);
    assert(post_state.outstanding_cache_reqs.is_injective());
    assert(!post_state.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
    assert forall |addr: Address| #[trigger] post_state.outstanding_cache_reqs.values().contains(addr)
        implies post_state.cache.lookup_map.dom().contains(addr) by {
        assert(tracked_reqs.values().contains(addr));
        assert(post_state.cache.lookup_map.contains_key(addr));
    }
    assert(post_state.outstanding_cache_reqs.values() <= post_state.cache.lookup_map.dom());
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.contains_key(id) implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let slot = post_state.cache.lookup_map[addr];
        match post_state.cache.entries[slot] {
            Entry::Loading{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && post_state.cache.status_map[slot] is Writeback,
            _ => false,
        }
    } by {
        assert(tracked_reqs.contains_key(id));
        let addr = tracked_reqs[id];
        assert(post_state.outstanding_cache_reqs[id] == addr);
        assert(tracked_reqs.values().contains(addr));
        let pre_slot = pre_state.cache.lookup_map[addr];
        let post_slot = post_state.cache.lookup_map[addr];
        assert(post_slot == pre_slot);
        assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[pre_slot]);
        assert(post_state.cache.status_map[post_slot] == pre_state.cache.status_map[pre_slot]);
    }
}

pub proof fn cache_internal_preserves_outstanding_cache_reqs_disk_backed(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        unified_cache_outstanding_cache_reqs_disk_backed_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
        post.disk.requests == pre.disk.requests,
        post.disk.responses == pre.disk.responses,
    ensures
        unified_cache_outstanding_cache_reqs_disk_backed_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    cache_internal_preserves_cache_request_wf(pre, post);
    cache_internal_preserves_outstanding_cache_entries(pre, post);

    assert(post_state.outstanding_cache_reqs.is_injective());
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        implies disk_has_pending_id(post.disk, id) by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(disk_has_pending_id(pre.disk, id));
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map.contains_key(addr)
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]] is Filled
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]]->data == req->data
            &&& post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == Status::Writeback{}
        }
    } by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        assert(post_state.outstanding_cache_reqs[id] == pre_state.outstanding_cache_reqs[id]);
        assert(post.disk.requests[id] == pre.disk.requests[id]);
        let addr = pre_state.outstanding_cache_reqs[id];
        let req = pre.disk.requests[id];
        assert(req.addr() == addr);
        if req is WriteReq {
            assert(pre_state.cache.lookup_map.contains_key(addr));
            let pre_slot = pre_state.cache.lookup_map[addr];
            assert(pre_state.cache.entries[pre_slot] is Filled);
            assert(pre_state.cache.entries[pre_slot]->data == req->data);
            assert(pre_state.cache.status_map[pre_slot] == Status::Writeback{});
            assert(pre_state.outstanding_cache_reqs.values().contains(addr));
            assert(post_state.cache.lookup_map[addr] == pre_slot);
            assert(post_state.cache.entries[post_state.cache.lookup_map[addr]]
                == pre_state.cache.entries[pre_slot]);
            assert(post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == pre_state.cache.status_map[pre_slot]);
        }
    }
}

pub proof fn cache_internal_preserves_shared_cache_disk_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_shared_cache_disk_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
        post.disk.content == pre.disk.content,
    ensures
        unified_cache_shared_cache_disk_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    Cache::State::inv_next(pre_state.cache, post_state.cache, Cache::Label::Internal{});

    assert forall |addr: Address| #[trigger] filled_cache_pages(post_state.cache).contains_key(addr)
        implies addr.wf() by {
        assert(cache_filled_addr(post_state.cache, addr));
        cache_internal_post_filled_addr_was_pre_filled(pre_state.cache, post_state.cache, addr);
        assert(cache_filled_addr(pre_state.cache, addr));
        assert(filled_cache_pages(pre_state.cache).contains_key(addr));
        assert(unified_cache_shared_cache_disk_inv(pre));
    }
    assert forall |addr: Address| #[trigger] post.disk.content.contains_key(addr)
        && addr != spec_superblock_addr()
        implies addr.wf() by {
        assert(pre.disk.content.contains_key(addr));
        assert(unified_cache_shared_cache_disk_inv(pre));
    }
    assert forall |addr: Address| {
        &&& #[trigger] filled_cache_status(post_state.cache).contains_key(addr)
        &&& filled_cache_status(post_state.cache)[addr] == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& post.disk.content.contains_key(addr)
    } implies post.disk.content[addr] == cache_filled_page(post_state.cache, addr) by {
        cache_internal_preserves_clean_filled_addr(pre_state.cache, post_state.cache, addr);
        assert(filled_cache_status(pre_state.cache).contains_key(addr));
        assert(filled_cache_status(pre_state.cache)[addr] == PageStatus::Clean);
        assert(unified_cache_shared_cache_disk_inv(pre));
        assert(pre.disk.content.contains_key(addr));
        assert(pre.disk.content[addr] == cache_filled_page(pre_state.cache, addr));
        assert(cache_filled_page(post_state.cache, addr) == cache_filled_page(pre_state.cache, addr));
    }
}

pub proof fn cache_internal_preserves_cache_disk_response_inv(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        inv(pre),
        post.disk.responses == pre.disk.responses,
        post.disk.content == pre.disk.content,
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
    ensures
        unified_cache_cache_disk_response_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let tracked_reqs = pre_state.outstanding_cache_reqs;

    cache_internal_preserves_outstanding_cache_entries(pre, post);

    assert forall |id: ID| {
        &&& #[trigger] post.disk.responses.contains_key(id)
        &&& post.program.state.outstanding_cache_reqs.contains_key(id)
    } implies {
        let addr = post.program.state.outstanding_cache_reqs[id];
        let resp = post.disk.responses[id];
        &&& resp is ReadResp ==> {
            &&& resp->data == post.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& cache_filled_addr(post.program.state.cache, addr)
            &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
        }
    } by {
        assert(pre.disk.responses.contains_key(id));
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(post_state.outstanding_cache_reqs[id] == pre_state.outstanding_cache_reqs[id]);
        let addr = pre_state.outstanding_cache_reqs[id];
        assert(post.disk.responses[id] == pre.disk.responses[id]);
        assert(post.disk.content == pre.disk.content);
        assert(unified_cache_cache_disk_response_inv(pre));
        if pre.disk.responses[id] is WriteResp {
            assert(tracked_reqs.values().contains(addr));
            let pre_slot = pre_state.cache.lookup_map[addr];
            let post_slot = post_state.cache.lookup_map[addr];
            assert(post_slot == pre_slot);
            assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[pre_slot]);
            assert(cache_filled_addr(pre_state.cache, addr));
            assert(cache_filled_addr(post_state.cache, addr));
            assert(cache_filled_page(post_state.cache, addr)
                == cache_filled_page(pre_state.cache, addr));
        }
    }
}

pub proof fn cache_io_begin_preserves_cache_request_wf(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs.union_prefer_right(
                Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr()),
            ),
        Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr()).is_injective(),
        !Map::new(
            |id| req_map.contains_key(id),
            |id| req_map[id].addr(),
        ).contains_value(spec_superblock_addr()),
    ensures
        unified_cache_cache_request_wf(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let updated = Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
    let new_outstanding = pre_state.outstanding_cache_reqs.union_prefer_right(updated);
    let lbl = Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()};
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step| Cache::State::next_by(pre_state.cache, post_state.cache, lbl, step);
    assert(updated.is_injective());
    assert(!updated.contains_value(spec_superblock_addr()));
    assert forall |addr: Address| #![auto] updated.values().contains(addr)
        implies !pre_state.outstanding_cache_reqs.values().contains(addr)
    by {
        let new_id = choose |id: ID| #![auto] updated.contains_key(id) && updated[id] == addr;
        let req = req_map[new_id];
        assert(req.addr() == addr);
        if pre_state.outstanding_cache_reqs.values().contains(addr) {
            let old_id = choose |id: ID| #![auto] pre_state.outstanding_cache_reqs.contains_key(id)
                && pre_state.outstanding_cache_reqs[id] == addr;
            let old_slot = pre_state.cache.lookup_map[addr];
            assert(match pre_state.cache.entries[old_slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && pre_state.cache.status_map[old_slot] is Writeback,
                _ => false,
            });
            match step {
                Cache::Step::load_initiate(new_slots_mapping) => {
                    assert(Cache::State::load_initiate(
                        pre_state.cache,
                        post_state.cache,
                        lbl,
                        new_slots_mapping,
                    ));
                    assert(req_map.values().contains(req));
                    assert(req is ReadReq);
                    assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                    assert(addr_maps_to_req(req_map.values(), req, addr));
                    assert(exists |r: DiskRequest| addr_maps_to_req(req_map.values(), r, addr));
                    assert(pre_state.cache.valid_new_slots_mapping(new_slots_mapping));
                    assert(new_slots_mapping.contains_value(addr));
                    assert(pre_state.cache.lookup_map.dom().contains(addr));
                    assert(new_slots_mapping.values().disjoint(pre_state.cache.lookup_map.dom()));
                    assert(false);
                },
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(pre_state.cache, post_state.cache, lbl));
                    assert(req_map.values().contains(req));
                    assert(req is WriteReq);
                    assert(pre_state.cache.valid_writeback_requests(req_map.values()));
                    assert(pre_state.cache.lookup_map.contains_key(addr));
                    let slot = pre_state.cache.lookup_map[addr];
                    assert(pre_state.cache.entries[slot]
                        == Entry::Filled{addr: addr, data: req->data});
                    assert(pre_state.cache.status_map[slot] is Dirty);
                    assert(slot == old_slot);
                    assert(false);
                },
                _ => {
                    assert(false);
                },
            }
        }
    }
    assert(new_outstanding.is_injective()) by {
        assert forall |id1: ID, id2: ID|
            id1 != id2
            && new_outstanding.contains_key(id1)
            && new_outstanding.contains_key(id2)
            implies #[trigger] new_outstanding[id1] != #[trigger] new_outstanding[id2]
        by {
            if updated.contains_key(id1) && updated.contains_key(id2) {
                assert(updated[id1] != updated[id2]);
                assert(new_outstanding[id1] == updated[id1]);
                assert(new_outstanding[id2] == updated[id2]);
            } else if !updated.contains_key(id1) && !updated.contains_key(id2) {
                assert(pre_state.outstanding_cache_reqs.contains_key(id1));
                assert(pre_state.outstanding_cache_reqs.contains_key(id2));
                assert(pre_state.outstanding_cache_reqs[id1]
                    != pre_state.outstanding_cache_reqs[id2]);
                assert(new_outstanding[id1] == pre_state.outstanding_cache_reqs[id1]);
                assert(new_outstanding[id2] == pre_state.outstanding_cache_reqs[id2]);
            } else if updated.contains_key(id1) {
                assert(pre_state.outstanding_cache_reqs.contains_key(id2));
                assert(updated.values().contains(updated[id1]));
                assert(!pre_state.outstanding_cache_reqs.values().contains(updated[id1]));
                assert(new_outstanding[id1] == updated[id1]);
                assert(new_outstanding[id2] == pre_state.outstanding_cache_reqs[id2]);
            } else {
                assert(updated.contains_key(id2));
                assert(pre_state.outstanding_cache_reqs.contains_key(id1));
                assert(updated.values().contains(updated[id2]));
                assert(!pre_state.outstanding_cache_reqs.values().contains(updated[id2]));
                assert(new_outstanding[id1] == pre_state.outstanding_cache_reqs[id1]);
                assert(new_outstanding[id2] == updated[id2]);
            }
        }
    }
    assert(!new_outstanding.contains_value(spec_superblock_addr())) by {
        if new_outstanding.contains_value(spec_superblock_addr()) {
            let id = choose |id: ID| #![auto] new_outstanding.contains_key(id)
                && new_outstanding[id] == spec_superblock_addr();
            if updated.contains_key(id) {
                assert(updated.contains_value(spec_superblock_addr()));
            } else {
                assert(pre_state.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
            }
            assert(false);
        }
    }
    assert forall |addr: Address| #![auto] new_outstanding.values().contains(addr)
        implies post_state.cache.lookup_map.dom().contains(addr)
    by {
        let id = choose |id: ID| #![auto] new_outstanding.contains_key(id) && new_outstanding[id] == addr;
        if updated.contains_key(id) {
            let req = req_map[id];
            assert(req.addr() == addr);
            match step {
                Cache::Step::load_initiate(new_slots_mapping) => {
                    assert(Cache::State::load_initiate(
                        pre_state.cache,
                        post_state.cache,
                        lbl,
                        new_slots_mapping,
                    ));
                    assert(req_map.values().contains(req));
                    assert(req is ReadReq);
                    assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                    assert(addr_maps_to_req(req_map.values(), req, addr));
                    assert(exists |r: DiskRequest| addr_maps_to_req(req_map.values(), r, addr));
                    assert(new_slots_mapping.contains_value(addr));
                    assert(post_state.cache.lookup_map.contains_key(addr));
                },
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(pre_state.cache, post_state.cache, lbl));
                    assert(req_map.values().contains(req));
                    assert(req is WriteReq);
                    assert(pre_state.cache.valid_writeback_requests(req_map.values()));
                    assert(pre_state.cache.lookup_map.contains_key(addr));
                    assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                },
                _ => {
                    assert(false);
                },
            }
        } else {
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
            assert(pre_state.cache.lookup_map.dom().contains(addr));
            match step {
                Cache::Step::load_initiate(new_slots_mapping) => {
                    assert(Cache::State::load_initiate(
                        pre_state.cache,
                        post_state.cache,
                        lbl,
                        new_slots_mapping,
                    ));
                    assert(post_state.cache.lookup_map.contains_key(addr));
                },
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(pre_state.cache, post_state.cache, lbl));
                    assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                },
                _ => {
                    assert(false);
                },
            }
        }
    }
    assert(new_outstanding.values() <= post_state.cache.lookup_map.dom());
    assert forall |id: ID| #[trigger] new_outstanding.contains_key(id) implies {
        let addr = new_outstanding[id];
        let slot = post_state.cache.lookup_map[addr];
        match post_state.cache.entries[slot] {
            Entry::Loading{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && post_state.cache.status_map[slot] is Writeback,
            _ => false,
        }
    } by {
        let addr = new_outstanding[id];
        if updated.contains_key(id) {
            let req = req_map[id];
            assert(req.addr() == addr);
            match step {
                Cache::Step::load_initiate(new_slots_mapping) => {
                    assert(Cache::State::load_initiate(
                        pre_state.cache,
                        post_state.cache,
                        lbl,
                        new_slots_mapping,
                    ));
                    assert(req_map.values().contains(req));
                    assert(req is ReadReq);
                    assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                    assert(addr_maps_to_req(req_map.values(), req, addr));
                    assert(exists |r: DiskRequest| addr_maps_to_req(req_map.values(), r, addr));
                    assert(new_slots_mapping.contains_value(addr));
                    Cache::State::invert_contains_pair(new_slots_mapping, addr);
                    let slot = new_slots_mapping.invert()[addr];
                    assert(new_slots_mapping.contains_pair(slot, addr));
                    assert(new_slots_mapping[slot] == addr);
                    assert(post_state.cache.lookup_map[addr] == slot);
                    let slot = post_state.cache.lookup_map[addr];
                    assert(post_state.cache.entries[slot] == Entry::Loading{addr});
                },
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(pre_state.cache, post_state.cache, lbl));
                    assert(req_map.values().contains(req));
                    assert(req is WriteReq);
                    assert(pre_state.cache.valid_writeback_requests(req_map.values()));
                    let slot = pre_state.cache.lookup_map[addr];
                    assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                    assert(post_state.cache.entries[slot] == pre_state.cache.entries[slot]);
                    assert(pre_state.cache.entries[slot]
                        == Entry::Filled{addr: addr, data: req->data});
                    let writeback_slots = Map::new(
                        |req: DiskRequest| req_map.values().contains(req),
                        |req: DiskRequest| pre_state.cache.lookup_map[req->to],
                    ).values();
                    let writeback_slot_map = Map::new(
                        |req: DiskRequest| req_map.values().contains(req),
                        |req: DiskRequest| pre_state.cache.lookup_map[req->to],
                    );
                    assert(writeback_slot_map.contains_key(req));
                    assert(writeback_slot_map[req] == slot);
                    assert(writeback_slots.contains(slot));
                    assert(post_state.cache.status_map[slot] is Writeback);
                },
                _ => {
                    assert(false);
                },
            }
        } else {
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
            assert(pre_state.outstanding_cache_reqs[id] == addr);
            match step {
                Cache::Step::load_initiate(new_slots_mapping) => {
                    assert(Cache::State::load_initiate(
                        pre_state.cache,
                        post_state.cache,
                        lbl,
                        new_slots_mapping,
                    ));
                    assert(!updated.values().contains(addr));
                    assert(!new_slots_mapping.contains_value(addr)) by {
                        if new_slots_mapping.contains_value(addr) {
                            assert(Cache::State::valid_load_requests(
                                req_map.values(),
                                new_slots_mapping,
                            ));
                            assert(exists |r: DiskRequest| addr_maps_to_req(
                                req_map.values(),
                                r,
                                addr,
                            ));
                            let r = choose |r: DiskRequest| addr_maps_to_req(
                                req_map.values(),
                                r,
                                addr,
                            );
                            let new_id = choose |id: ID| #![auto] req_map.contains_key(id)
                                && req_map[id] == r;
                            assert(updated.contains_key(new_id));
                            assert(updated[new_id] == addr);
                            assert(updated.values().contains(addr));
                            assert(false);
                        }
                    }
                    let pre_slot = pre_state.cache.lookup_map[addr];
                    let post_slot = post_state.cache.lookup_map[addr];
                    assert(pre_state.outstanding_cache_reqs.values().contains(addr));
                    assert(pre_state.cache.lookup_map.contains_key(addr));
                    pre_state.cache.build_lookup_map_ensures();
                    assert(post_slot == pre_slot);
                    assert(!new_slots_mapping.contains_key(pre_slot)) by {
                        if new_slots_mapping.contains_key(pre_slot) {
                            assert(pre_state.cache.valid_new_slots_mapping(new_slots_mapping));
                            assert(pre_state.cache.entries[pre_slot] is Empty);
                            assert(match pre_state.cache.entries[pre_slot] {
                                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                                Entry::Filled{addr: entry_addr, ..} =>
                                    entry_addr == addr
                                        && pre_state.cache.status_map[pre_slot] is Writeback,
                                _ => false,
                            });
                            assert(false);
                        }
                    }
                    let updated_entries = Map::new(
                        |slot: Slot| new_slots_mapping.contains_key(slot),
                        |slot: Slot| Entry::Loading{addr: new_slots_mapping[slot]},
                    );
                    assert(!updated_entries.contains_key(pre_slot));
                    assert(!updated_entries.contains_key(post_slot));
                    assert(pre_state.cache.entries.contains_key(pre_slot));
                    assert(pre_state.cache.entries.contains_key(post_slot));
                    assert(post_state.cache.entries
                        == pre_state.cache.entries.union_prefer_right(updated_entries));
                    assert(post_state.cache.entries[post_slot]
                        == pre_state.cache.entries.union_prefer_right(updated_entries)[post_slot]);
                    assert(pre_state.cache.entries.union_prefer_right(updated_entries)[post_slot]
                        == pre_state.cache.entries[post_slot]);
                    assert(pre_state.cache.entries[post_slot] == pre_state.cache.entries[pre_slot]);
                    assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[pre_slot]);
                    assert(post_state.cache.status_map[post_slot]
                        == pre_state.cache.status_map[pre_slot]);
                },
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(pre_state.cache, post_state.cache, lbl));
                    assert(!updated.values().contains(addr));
                    let pre_slot = pre_state.cache.lookup_map[addr];
                    let post_slot = post_state.cache.lookup_map[addr];
                    assert(pre_state.outstanding_cache_reqs.values().contains(addr));
                    assert(pre_state.cache.lookup_map.contains_key(addr));
                    pre_state.cache.build_lookup_map_ensures();
                    assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                    assert(post_slot == pre_slot);
                    assert(post_state.cache.entries[post_slot]
                        == pre_state.cache.entries[pre_slot]);
                    let writeback_slots = Map::new(
                        |req: DiskRequest| req_map.values().contains(req),
                        |req: DiskRequest| pre_state.cache.lookup_map[req->to],
                    ).values();
                    assert(!writeback_slots.contains(pre_slot)) by {
                        if writeback_slots.contains(pre_slot) {
                            let r = choose |r: DiskRequest| #![auto]
                                req_map.values().contains(r)
                                    && pre_state.cache.lookup_map[r->to] == pre_slot;
                            let new_id = choose |id: ID| #![auto] req_map.contains_key(id)
                                && req_map[id] == r;
                            assert(updated.contains_key(new_id));
                            assert(r.addr() == r->to);
                            assert(pre_state.cache.lookup_map[r->to]
                                == pre_state.cache.lookup_map[addr]);
                            assert(pre_state.cache.lookup_map.is_injective());
                            assert(r->to == addr);
                            assert(updated[new_id] == addr);
                            assert(updated.values().contains(addr));
                            assert(false);
                        }
                    }
                    let updated_status_map = Map::new(
                        |slot: Slot| writeback_slots.contains(slot),
                        |slot: Slot| Status::Writeback{},
                    );
                    assert(!updated_status_map.contains_key(pre_slot));
                    assert(!updated_status_map.contains_key(post_slot));
                    assert(pre_state.cache.status_map.contains_key(pre_slot));
                    assert(pre_state.cache.status_map.contains_key(post_slot));
                    assert(post_state.cache.status_map
                        == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                    assert(post_state.cache.status_map[post_slot]
                        == pre_state.cache.status_map.union_prefer_right(updated_status_map)[post_slot]);
                    assert(pre_state.cache.status_map.union_prefer_right(updated_status_map)[post_slot]
                        == pre_state.cache.status_map[post_slot]);
                    assert(pre_state.cache.status_map[post_slot]
                        == pre_state.cache.status_map[pre_slot]);
                    assert(post_state.cache.status_map[post_slot]
                        == pre_state.cache.status_map[pre_slot]);
                },
                _ => {
                    assert(false);
                },
            }
            let pre_slot = pre_state.cache.lookup_map[addr];
            let post_slot = post_state.cache.lookup_map[addr];
            assert(match pre_state.cache.entries[pre_slot] {
                Entry::Loading{addr: entry_addr} => entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr && pre_state.cache.status_map[pre_slot] is Writeback,
                _ => false,
            });
            assert(post_slot == pre_slot);
        }
    }
    assert(post_state.outstanding_cache_reqs == new_outstanding);
}

pub proof fn cache_io_end_preserves_cache_request_wf(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    resp_map: Map<ID, DiskResponse>,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        resp_map.dom() <= pre.program.state.outstanding_cache_reqs.dom(),
        cache_resps == Map::new(
            |addr| pre.program.state.outstanding_cache_reqs.restrict(
                resp_map.dom(),
            ).invert().contains_key(addr),
            |addr| resp_map[
                pre.program.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert()[addr]
            ],
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs.remove_keys(resp_map.dom()),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps},
        ),
    ensures
        unified_cache_cache_request_wf(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let new_outstanding = pre_state.outstanding_cache_reqs.remove_keys(resp_map.dom());
    let finished = pre_state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
    let lbl = Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps};
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step| Cache::State::next_by(pre_state.cache, post_state.cache, lbl, step);
    assert(new_outstanding.is_injective());
    assert(!new_outstanding.contains_value(spec_superblock_addr()));
    assert forall |id: ID| #[trigger] new_outstanding.contains_key(id) implies {
        let addr = new_outstanding[id];
        let slot = post_state.cache.lookup_map[addr];
        match post_state.cache.entries[slot] {
            Entry::Loading{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && post_state.cache.status_map[slot] is Writeback,
            _ => false,
        }
    } by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(!resp_map.dom().contains(id));
        let addr = new_outstanding[id];
        assert(pre_state.outstanding_cache_reqs[id] == addr);
        assert(pre_state.outstanding_cache_reqs.values().contains(addr));
        assert(pre_state.cache.lookup_map.contains_key(addr));
        assert(!cache_resps.contains_key(addr)) by {
            if cache_resps.contains_key(addr) {
                assert(finished.contains_key(addr));
                let finished_id = finished[addr];
                assert(pre_state.outstanding_cache_reqs.restrict(resp_map.dom()).contains_pair(
                    finished_id,
                    addr,
                ));
                assert(pre_state.outstanding_cache_reqs.contains_key(finished_id));
                assert(resp_map.dom().contains(finished_id));
                assert(pre_state.outstanding_cache_reqs[finished_id] == addr);
                assert(finished_id == id);
                assert(false);
            }
        };
        let pre_slot = pre_state.cache.lookup_map[addr];
        pre_state.cache.build_lookup_map_ensures();
        assert(pre_state.cache.entries.contains_key(pre_slot));
        assert(pre_state.cache.status_map.contains_key(pre_slot));
        match step {
            Cache::Step::load_complete() => {
                assert(Cache::State::load_complete(pre_state.cache, post_state.cache, lbl));
                assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                let post_slot = post_state.cache.lookup_map[addr];
                assert(post_slot == pre_slot);
                let slot_addr_map = pre_state.cache.lookup_map.restrict(cache_resps.dom()).invert();
                let updated_entries = Map::new(
                    |slot: Slot| slot_addr_map.contains_key(slot),
                    |slot: Slot| Entry::Filled{
                        addr: slot_addr_map[slot],
                        data: cache_resps[slot_addr_map[slot]]->data,
                    },
                );
                let updated_status_map = Map::new(
                    |slot: Slot| slot_addr_map.contains_key(slot),
                    |slot: Slot| Status::Clean,
                );
                assert(!slot_addr_map.contains_key(pre_slot)) by {
                    if slot_addr_map.contains_key(pre_slot) {
                        assert(pre_state.cache.lookup_map.restrict(
                            cache_resps.dom(),
                        ).contains_value(pre_slot));
                        let resp_addr = choose |a: Address| #![auto]
                            pre_state.cache.lookup_map.restrict(cache_resps.dom()).contains_key(a)
                                && pre_state.cache.lookup_map.restrict(cache_resps.dom())[a]
                                    == pre_slot;
                        assert(cache_resps.contains_key(resp_addr));
                        assert(pre_state.cache.lookup_map[resp_addr]
                            == pre_state.cache.lookup_map[addr]);
                        assert(pre_state.cache.lookup_map.is_injective());
                        assert(resp_addr == addr);
                        assert(false);
                    }
                }
                assert(!updated_entries.contains_key(pre_slot));
                assert(!updated_status_map.contains_key(pre_slot));
                assert(post_state.cache.entries
                    == pre_state.cache.entries.union_prefer_right(updated_entries));
                assert(post_state.cache.status_map
                    == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                assert(post_state.cache.entries[post_slot] == pre_state.cache.entries[pre_slot]);
                assert(post_state.cache.status_map[post_slot]
                    == pre_state.cache.status_map[pre_slot]);
            },
            Cache::Step::writeback_complete() => {
                assert(Cache::State::writeback_complete(pre_state.cache, post_state.cache, lbl));
                assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                assert(post_state.cache.entries == pre_state.cache.entries);
                let post_slot = post_state.cache.lookup_map[addr];
                assert(post_slot == pre_slot);
                let resps_slots = pre_state.cache.lookup_map.restrict(cache_resps.dom()).values();
                let updated_status_map = Map::new(
                    |slot: Slot| resps_slots.contains(slot),
                    |slot: Slot| Status::Clean,
                );
                assert(!resps_slots.contains(pre_slot)) by {
                    if resps_slots.contains(pre_slot) {
                        let resp_addr = choose |a: Address| #![auto]
                            pre_state.cache.lookup_map.restrict(cache_resps.dom()).contains_key(a)
                                && pre_state.cache.lookup_map.restrict(cache_resps.dom())[a]
                                    == pre_slot;
                        assert(cache_resps.contains_key(resp_addr));
                        assert(pre_state.cache.lookup_map[resp_addr]
                            == pre_state.cache.lookup_map[addr]);
                        assert(pre_state.cache.lookup_map.is_injective());
                        assert(resp_addr == addr);
                        assert(false);
                    }
                }
                assert(!updated_status_map.contains_key(pre_slot));
                assert(post_state.cache.status_map
                    == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                assert(post_state.cache.status_map[post_slot]
                    == pre_state.cache.status_map[pre_slot]);
            },
            _ => {
                assert(false);
            },
        }
        let post_slot = post_state.cache.lookup_map[addr];
        assert(match pre_state.cache.entries[pre_slot] {
            Entry::Loading{addr: entry_addr} => entry_addr == addr,
            Entry::Filled{addr: entry_addr, ..} =>
                entry_addr == addr && pre_state.cache.status_map[pre_slot] is Writeback,
            _ => false,
        });
        assert(post_slot == pre_slot);
    }
    assert forall |addr: Address| #![auto] new_outstanding.values().contains(addr)
        implies post_state.cache.lookup_map.dom().contains(addr)
    by {
        let id = choose |id: ID| #![auto] new_outstanding.contains_key(id) && new_outstanding[id] == addr;
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(pre_state.outstanding_cache_reqs[id] == addr);
        assert(pre_state.cache.lookup_map.contains_key(addr));
        match step {
            Cache::Step::load_complete() => {
                assert(Cache::State::load_complete(pre_state.cache, post_state.cache, lbl));
                assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
            },
            Cache::Step::writeback_complete() => {
                assert(Cache::State::writeback_complete(pre_state.cache, post_state.cache, lbl));
                assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
            },
            _ => {
                assert(false);
            },
        }
    }
    assert(new_outstanding.values() <= post_state.cache.lookup_map.dom());
    assert(post_state.outstanding_cache_reqs == new_outstanding);
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
        cache_resps.dom() <= Set::new(|addr: Address| addr.wf()),
        forall |addr: Address| #[trigger] cache_resps.contains_key(addr) ==> {
            &&& cache_resps[addr] is ReadResp ==> cache_resps[addr]->data
                == pre.disk.content[addr]
            &&& cache_resps[addr] is WriteResp ==> {
                &&& pre.disk.content.contains_key(addr)
                &&& cache_filled_addr(pre.program.state.cache, addr)
                &&& pre.disk.content[addr] == cache_filled_page(pre.program.state.cache, addr)
            }
        },
{
    let state = pre.program.state;
    let restricted = state.outstanding_cache_reqs.restrict(resp_map.dom());
    let finished = restricted.invert();

    assert forall |addr: Address| #[trigger] cache_resps.contains_key(addr) implies {
        &&& cache_resps[addr] is ReadResp ==> cache_resps[addr]->data
            == pre.disk.content[addr]
        &&& cache_resps[addr] is WriteResp ==> {
            &&& pre.disk.content.contains_key(addr)
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
        assert(addr.wf()) by {
            assert(unified_cache_cache_disk_response_inv(pre));
        }
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

pub proof fn outstanding_cache_reqs_disk_backed_unchanged(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        unified_cache_outstanding_cache_reqs_disk_backed_inv(pre),
        post.program.state.cache == pre.program.state.cache,
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
        post.disk.requests == pre.disk.requests,
        post.disk.responses == pre.disk.responses,
    ensures
        unified_cache_outstanding_cache_reqs_disk_backed_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    assert(post_state.outstanding_cache_reqs.is_injective());
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.dom().contains(id)
        implies (post.disk.requests.dom() + post.disk.responses.dom()).contains(id) by {
        assert(pre_state.outstanding_cache_reqs.dom().contains(id));
        assert((pre.disk.requests.dom() + pre.disk.responses.dom()).contains(id));
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map.contains_key(addr)
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]] is Filled
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]]->data == req->data
            &&& post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == Status::Writeback{}
        }
    } by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        assert(post_state.outstanding_cache_reqs[id]
            == pre_state.outstanding_cache_reqs[id]);
        assert(post.disk.requests[id] == pre.disk.requests[id]);
    }
}

pub proof fn outstanding_cache_reqs_disk_backed_request_added(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        unified_cache_outstanding_cache_reqs_disk_backed_inv(pre),
        post.program.state.cache == pre.program.state.cache,
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
        req_map.dom().disjoint(pre.program.state.outstanding_cache_reqs.dom()),
        post.disk.requests == pre.disk.requests.union_prefer_right(req_map),
        post.disk.responses == pre.disk.responses,
    ensures
        unified_cache_outstanding_cache_reqs_disk_backed_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    assert(post_state.outstanding_cache_reqs.is_injective());
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.dom().contains(id)
        implies (post.disk.requests.dom() + post.disk.responses.dom()).contains(id) by {
        assert(pre_state.outstanding_cache_reqs.dom().contains(id));
        assert((pre.disk.requests.dom() + pre.disk.responses.dom()).contains(id));
        if pre.disk.requests.contains_key(id) {
            assert(post.disk.requests.contains_key(id));
        } else {
            assert(pre.disk.responses.contains_key(id));
            assert(post.disk.responses.contains_key(id));
        }
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map.contains_key(addr)
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]] is Filled
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]]->data == req->data
            &&& post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == Status::Writeback{}
        }
    } by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(!req_map.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        assert(post.disk.requests[id] == pre.disk.requests[id]);
    }
}

pub proof fn cache_io_begin_preserves_outstanding_cache_reqs_disk_backed(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        unified_cache_outstanding_cache_reqs_disk_backed_inv(pre),
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs.union_prefer_right(
                Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr()),
            ),
        Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr()).is_injective(),
        !Map::new(
            |id| req_map.contains_key(id),
            |id| req_map[id].addr(),
        ).contains_value(spec_superblock_addr()),
        post.disk.requests == pre.disk.requests.union_prefer_right(req_map),
        post.disk.responses == pre.disk.responses,
        req_map.dom().disjoint(pre.disk.requests.dom()),
        req_map.dom().disjoint(pre.disk.responses.dom()),
    ensures
        unified_cache_outstanding_cache_reqs_disk_backed_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let updated = Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
    cache_io_begin_preserves_cache_request_wf(pre, post, req_map);
    assert(post_state.outstanding_cache_reqs.is_injective());

    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.dom().contains(id)
        implies (post.disk.requests.dom() + post.disk.responses.dom()).contains(id) by {
        if updated.contains_key(id) {
            assert(req_map.contains_key(id));
            assert(post.disk.requests.contains_key(id));
        } else {
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
            assert((pre.disk.requests.dom() + pre.disk.responses.dom()).contains(id));
            if pre.disk.requests.contains_key(id) {
                assert(post.disk.requests.contains_key(id));
            } else {
                assert(pre.disk.responses.contains_key(id));
                assert(post.disk.responses.contains_key(id));
            }
        }
    }
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        implies disk_has_pending_id(post.disk, id) by {
        assert((post.disk.requests.dom() + post.disk.responses.dom()).contains(id));
    }

    let cache_lbl = Cache::Label::DiskOps{
        requests: req_map.values(),
        responses: Map::<Address, DiskResponse>::empty(),
    };
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step| Cache::State::next_by(
        pre_state.cache,
        post_state.cache,
        cache_lbl,
        step,
    );
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map.contains_key(addr)
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]] is Filled
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]]->data == req->data
            &&& post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == Status::Writeback{}
        }
    } by {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        if updated.contains_key(id) {
            assert(req_map.contains_key(id));
            assert(post_state.outstanding_cache_reqs[id] == updated[id]);
            assert(post.disk.requests[id] == req_map[id]);
            assert(req.addr() == addr);
            if req is WriteReq {
                match cache_step {
                    Cache::Step::writeback_initiate() => {
                        assert(Cache::State::writeback_initiate(
                            pre_state.cache,
                            post_state.cache,
                            cache_lbl,
                        )) by {
                        }
                        assert(pre_state.cache.valid_writeback_requests(req_map.values()));
                        assert(req_map.values().contains(req));
                        assert(pre_state.cache.lookup_map.contains_key(addr));
                        let slot = pre_state.cache.lookup_map[addr];
                        assert(pre_state.cache.entries[slot]
                            == Entry::Filled{addr: addr, data: req->data});
                        assert(post_state.cache.lookup_map == pre_state.cache.lookup_map);
                        assert(post_state.cache.entries == pre_state.cache.entries);
                        let writeback_slots = Map::new(
                            |req: DiskRequest| req_map.values().contains(req),
                            |req: DiskRequest| pre_state.cache.lookup_map[req->to],
                        ).values();
                        let writeback_slot_map = Map::new(
                            |req: DiskRequest| req_map.values().contains(req),
                            |req: DiskRequest| pre_state.cache.lookup_map[req->to],
                        );
                        assert(writeback_slot_map.contains_key(req));
                        assert(writeback_slot_map[req] == slot);
                        assert(writeback_slots.contains(slot));
                        let updated_status_map = Map::new(
                            |slot: Slot| writeback_slots.contains(slot),
                            |slot: Slot| Status::Writeback{},
                        );
                        assert(updated_status_map.contains_key(slot));
                        assert(post_state.cache.status_map
                            == pre_state.cache.status_map.union_prefer_right(updated_status_map));
                        assert(post_state.cache.status_map[slot] == Status::Writeback{});
                    },
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(Cache::State::load_initiate(
                            pre_state.cache,
                            post_state.cache,
                            cache_lbl,
                            new_slots_mapping,
                        )) by {
                        }
                        assert(Cache::State::valid_load_requests(
                            req_map.values(),
                            new_slots_mapping,
                        ));
                        assert(req_map.values().contains(req));
                        assert(req is ReadReq);
                        assert(false);
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        } else {
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
            assert(pre_state.outstanding_cache_reqs[id] == addr);
            assert(!req_map.contains_key(id)) by {
                if req_map.contains_key(id) {
                    assert(disk_has_pending_id(pre.disk, id));
                    if pre.disk.requests.contains_key(id) {
                        assert(req_map.dom().disjoint(pre.disk.requests.dom()));
                    } else {
                        assert(pre.disk.responses.contains_key(id));
                        assert(req_map.dom().disjoint(pre.disk.responses.dom()));
                    }
                    assert(false);
                }
            }
            assert(pre.disk.requests.contains_key(id));
            assert(post.disk.requests[id] == pre.disk.requests[id]);
            assert(req == pre.disk.requests[id]);
            assert(req.addr() == addr);
            if req is WriteReq {
                assert(pre_state.cache.lookup_map.contains_key(addr));
                assert(pre_state.cache.entries[pre_state.cache.lookup_map[addr]] is Filled);
                assert(pre_state.cache.entries[pre_state.cache.lookup_map[addr]]->data
                    == req->data);
                assert(pre_state.cache.status_map[pre_state.cache.lookup_map[addr]]
                    == Status::Writeback{});
                pre_state.cache.build_lookup_map_ensures();
                assert(pre_state.cache.entries.contains_key(pre_state.cache.lookup_map[addr]));
                assert(cache_filled_addr(pre_state.cache, addr));
                cache_disk_ops_begin_preserves_filled_page(
                    pre_state.cache,
                    post_state.cache,
                    req_map.values(),
                    addr,
                );
                assert(post_state.cache.lookup_map.contains_key(addr));
                assert(post_state.cache.entries[post_state.cache.lookup_map[addr]] is Filled);
                assert(post_state.cache.entries[post_state.cache.lookup_map[addr]]->data
                    == req->data);
                assert(post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                    == Status::Writeback{}) by {
                    assert(post_state.outstanding_cache_reqs.contains_key(id));
                    assert(post_state.outstanding_cache_reqs[id] == addr);
                    assert(unified_cache_cache_request_wf(post));
                }
                assert(post_state.cache.entries[post_state.cache.lookup_map[addr]]->data
                    == req->data);
            }
        }
    }
}

pub proof fn cache_io_end_preserves_outstanding_cache_reqs_disk_backed(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    resp_map: Map<ID, DiskResponse>,
)
    requires
        unified_cache_outstanding_cache_reqs_disk_backed_inv(pre),
        pre.program.state.cache.inv(),
        unified_cache_cache_request_wf(pre),
        resp_map.dom() <= pre.program.state.outstanding_cache_reqs.dom(),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{
                requests: Set::empty(),
                responses: Map::new(
                    |addr| pre.program.state.outstanding_cache_reqs.restrict(
                        resp_map.dom(),
                    ).invert().contains_key(addr),
                    |addr| resp_map[
                        pre.program.state.outstanding_cache_reqs.restrict(
                            resp_map.dom(),
                        ).invert()[addr]
                    ],
                ),
            },
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs.remove_keys(resp_map.dom()),
        post.disk.requests == pre.disk.requests,
        post.disk.responses == pre.disk.responses.remove_keys(resp_map.dom()),
    ensures
        unified_cache_outstanding_cache_reqs_disk_backed_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let cache_resps = Map::new(
        |addr| pre_state.outstanding_cache_reqs.restrict(resp_map.dom()).invert().contains_key(addr),
        |addr| resp_map[pre_state.outstanding_cache_reqs.restrict(resp_map.dom()).invert()[addr]],
    );
    cache_io_end_preserves_cache_request_wf(pre, post, resp_map, cache_resps);
    assert(post_state.outstanding_cache_reqs.is_injective());
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.dom().contains(id)
        implies (post.disk.requests.dom() + post.disk.responses.dom()).contains(id) by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(!resp_map.contains_key(id));
        assert((pre.disk.requests.dom() + pre.disk.responses.dom()).contains(id));
        if pre.disk.requests.contains_key(id) {
            assert(post.disk.requests.contains_key(id));
        } else {
            assert(pre.disk.responses.contains_key(id));
            assert(post.disk.responses.contains_key(id));
        }
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map.contains_key(addr)
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]] is Filled
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]]->data == req->data
            &&& post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == Status::Writeback{}
        }
    } by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(!resp_map.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        assert(post.disk.requests[id] == pre.disk.requests[id]);
        assert(pre_state.outstanding_cache_reqs[id]
            == post_state.outstanding_cache_reqs[id]);
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        if req is WriteReq {
            pre_state.cache.build_lookup_map_ensures();
            assert(cache_filled_addr(pre_state.cache, addr));
            assert(cache_filled_page(pre_state.cache, addr) == req->data);
            cache_disk_ops_end_preserves_filled_page(
                pre_state.cache,
                post_state.cache,
                cache_resps,
                addr,
            );
            assert(cache_filled_addr(post_state.cache, addr));
            assert(cache_filled_page(post_state.cache, addr) == req->data);
            assert(unified_cache_cache_request_wf(post));
        }
    }
}

pub proof fn outstanding_cache_reqs_disk_backed_response_removed(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    removed_id: ID,
)
    requires
        unified_cache_outstanding_cache_reqs_disk_backed_inv(pre),
        !pre.program.state.outstanding_cache_reqs.contains_key(removed_id),
        post.program.state.cache == pre.program.state.cache,
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
        post.disk.requests == pre.disk.requests,
        post.disk.responses == pre.disk.responses.remove(removed_id),
    ensures
        unified_cache_outstanding_cache_reqs_disk_backed_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    assert(post_state.outstanding_cache_reqs.is_injective());
    assert forall |id: ID| #[trigger] post_state.outstanding_cache_reqs.dom().contains(id)
        implies (post.disk.requests.dom() + post.disk.responses.dom()).contains(id) by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(id != removed_id);
        assert((pre.disk.requests.dom() + pre.disk.responses.dom()).contains(id));
        if pre.disk.requests.contains_key(id) {
            assert(post.disk.requests.contains_key(id));
        } else {
            assert(pre.disk.responses.contains_key(id));
            assert(post.disk.responses.contains_key(id));
        }
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs.contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map.contains_key(addr)
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]] is Filled
            &&& post_state.cache.entries[post_state.cache.lookup_map[addr]]->data == req->data
            &&& post_state.cache.status_map[post_state.cache.lookup_map[addr]]
                == Status::Writeback{}
        }
    } by {
        assert(pre_state.outstanding_cache_reqs.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        assert(post.disk.requests[id] == pre.disk.requests[id]);
    }
}

pub proof fn init_refines(pre: SystemModel::State<UnifiedCacheProgramModel>)
    requires
        SystemModel::State::initialize(pre, pre.program, pre.disk),
    ensures
        CrashAwareCachingDiskSystem::State::init(unified_cache_system_i(pre)),
        inv(pre),
{
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
            }

            let journal_src = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
            let branch_src = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
            let dst = unified_cache_system_i(pre);
            let initial_superblock = pre.disk.content[spec_superblock_addr()];

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
                assert(pre.program.state.sync_phase is None);
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
            assert(unified_cache_recovery_superblock_io_inv(pre)) by {
                assert(pre.program.state.recovery_state is Begin);
                assert(pre.program.state.persistent_image is None);
                assert(pre.program.state.sync_phase is None);
                assert(pre.program.state.sync_req_map
                    == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty());
                assert(journal_src.journal_projection_aus() =~= Set::<AU>::empty()) by {
                    let image = journal_src.persistent_superblock_image_i();
                    let tj = UnifiedCacheJournalRefinement::UnifiedCacheJournalSource::journal_image_tj_i(
                        journal_src.disk.content,
                        image,
                    );
                    assert forall |au: AU| #[trigger] journal_src.journal_projection_aus().contains(au)
                        implies false by {
                        assert(journal_src.journal_image_projection_aus_i(image).contains(au));
                        assert(tj.disk_view.loose_build_lsn_au_index_au_walk(
                            tj.freshest_rec,
                            image.journal_snapshot.first(),
                        ).values().contains(au));
                        assert(false);
                    }
                }
                assert(pre.program.state.cache.lookup_map == Map::<Address, crate::implementation::Cache_v::Slot>::empty()) by {
                }
                assert(journal_src.journal_caching_disk_i().cache
                    == Map::<Address, RawPage>::empty()) by {
                    assert_maps_equal!(
                        journal_src.journal_caching_disk_i().cache,
                        Map::<Address, RawPage>::empty(),
                        addr => {
                            if journal_src.journal_caching_disk_i().cache.contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(false);
                            }
                        }
                    );
                }
                assert(journal_src.journal_caching_disk_i().status
                    == Map::<Address, PageStatus>::empty()) by {
                    assert_maps_equal!(
                        journal_src.journal_caching_disk_i().status,
                        Map::<Address, PageStatus>::empty(),
                        addr => {
                            if journal_src.journal_caching_disk_i().status.contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(false);
                            }
                        }
                    );
                }
                assert(branch_src.branch_caching_disk_i().cache
                    == Map::<Address, RawPage>::empty()) by {
                    assert_maps_equal!(
                        branch_src.branch_caching_disk_i().cache,
                        Map::<Address, RawPage>::empty(),
                        addr => {
                            if branch_src.branch_caching_disk_i().cache.contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(false);
                            }
                        }
                    );
                }
                assert(branch_src.branch_caching_disk_i().status
                    == Map::<Address, PageStatus>::empty()) by {
                    assert_maps_equal!(
                        branch_src.branch_caching_disk_i().status,
                        Map::<Address, PageStatus>::empty(),
                        addr => {
                            if branch_src.branch_caching_disk_i().status.contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(false);
                            }
                        }
                    );
                }
                assert(branch_src.persistent_branch_image_i()
                    == crate::implementation::CachingDiskBranch_v::empty_caching_disk_branch_image()) by {
                    assert(branch_src.persistent_branch_image_i().persistent
                        == Map::<Address, RawPage>::empty());
                    assert(branch_src.persistent_branch_image_i().sealed_roots
                        == Seq::<Address>::empty());
                    assert(branch_src.persistent_branch_image_i().seq_end == 0);
                }
                crate::implementation::CachingDiskBranch_v::empty_caching_disk_branch_image_wf();
                assert(branch_src.persistent_branch_image_i().loadable());
                assert(branch_src.persistent_branch_image_i().stack_wf());
                empty_caching_disk_branch_image_summary_aus_empty();
                assert(dst.branch_owned_aus() =~= Set::<AU>::empty());
                assert(dst.component_disjoint());
                assert(dst.allocation_wf());
                let branch_image_aus =
                    UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
                        pre.disk.content,
                        branch_src.persistent_superblock_image_i().branch_roots,
                    );
                assert(project_cache_pages(pre.program.state.cache, branch_image_aus)
                    == Map::<Address, RawPage>::empty()) by {
                    assert_maps_equal!(
                        project_cache_pages(pre.program.state.cache, branch_image_aus),
                        Map::<Address, RawPage>::empty(),
                        addr => {
                            if project_cache_pages(pre.program.state.cache, branch_image_aus).contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(false);
                            }
                        }
                    );
                }
                assert(project_cache_status(pre.program.state.cache, branch_image_aus)
                    == Map::<Address, PageStatus>::empty()) by {
                    assert_maps_equal!(
                        project_cache_status(pre.program.state.cache, branch_image_aus),
                        Map::<Address, PageStatus>::empty(),
                        addr => {
                            if project_cache_status(pre.program.state.cache, branch_image_aus).contains_key(addr) {
                                assert(cache_filled_addr(pre.program.state.cache, addr));
                                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                                assert(false);
                            }
                        }
                    );
                }
                assert(pre.disk.requests == Map::<ID, DiskRequest>::empty());
                assert(pre.disk.responses == Map::<ID, DiskResponse>::empty());
            }
            assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(pre)) by {
                assert(pre.program.state.outstanding_cache_reqs == Map::<ID, Address>::empty());
            }
            empty_caching_disk_branch_image_summary_aus_empty();
            assert(dst.branch_owned_aus() =~= Set::<AU>::empty());
            assert(dst.component_disjoint());
            assert(dst.allocation_wf());
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
    assert(post.disk == pre.disk);
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
    assert(post.disk == pre.disk);
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
    assert(post.disk == pre.disk);
    assert(post.program.state == pre.program.state);
    assert(unified_cache_cache_request_wf(post));
    assert(unified_cache_cache_disk_response_inv(post));
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
    let read_nodes = to_branch_nodes(reads);
    let write_nodes = to_branch_nodes(writes);

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
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.journal.in_flight == pre_state.journal.in_flight);
    assert(post_state.branch.in_flight == pre_state.branch.in_flight);
    assert(journal_post.in_flight_image == journal_pre.in_flight_image) by {
        if pre_state.sync_image() is Some {
            assert(post_state.atomic_inflight_superblock_i()
                == pre_state.atomic_inflight_superblock_i());
        }
    }
    assert(branch_post.in_flight_image == branch_pre.in_flight_image) by {
        if pre_state.sync_image() is Some {
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
    assert(post.disk == pre.disk);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    cache_access_preserves_cache_request_wf(pre, post, reads, writes);
    cache_access_preserves_cache_disk_response_inv(pre, post, reads, writes);
    assert(unified_cache_cache_request_wf(post));
    assert(unified_cache_cache_disk_response_inv(post));
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();
    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let atomic_branch_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre_state.branch, post_state.branch, branch_atomic_lbl, step);
    assert(writes.dom() <= Set::new(|addr: Address| addr.wf())) by {
        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
            implies Set::new(|addr: Address| addr.wf()).contains(addr) by {
            assert(writes.contains_key(addr));
            reveal(Cache::State::next);
            reveal(Cache::State::next_by);
            assert(Cache::State::next_by(pre_state.cache, post_state.cache, cache_lbl, Cache::Step::access()));
            assert(Cache::State::access(pre_state.cache, post_state.cache, cache_lbl)) by {
            }
            assert(pre_state.cache.valid_write(addr));
            let slot = pre_state.cache.lookup_map[addr];
            if pre_state.cache.entries[slot] is Filled {
                assert(cache_filled_addr(pre_state.cache, addr));
                assert(filled_cache_pages(pre_state.cache).contains_key(addr));
                assert(unified_cache_shared_cache_disk_inv(pre));
            } else {
                assert(pre_state.cache.entries[slot] is Reserved);
                match atomic_branch_step {
                    AtomicBranchState::Step::append_nonempty(new_active_branch) => {
                        assert(AtomicBranchState::State::append_nonempty(
                            pre_state.branch,
                            post_state.branch,
                            branch_atomic_lbl,
                            new_active_branch,
                        )) by {
                        }
                        let branch_lbl = CachedBranch::Label::Append{
                            mini_allocator: pre_state.branch.mini_allocator,
                            receipt,
                            keys,
                            msgs,
                            read_nodes,
                            write_nodes,
                        };
                        assert(CachedBranch::State::next(
                            pre_state.branch.active_branch,
                            post_state.branch.active_branch,
                            branch_lbl,
                        ));
                        reveal(CachedBranch::State::next);
                        reveal(CachedBranch::State::next_by);
                        assert(CachedBranch::State::next_by(
                            pre_state.branch.active_branch,
                            post_state.branch.active_branch,
                            branch_lbl,
                            CachedBranch::Step::append_step(),
                        ));
                        assert(CachedBranch::State::append_step(
                            pre_state.branch.active_branch,
                            post_state.branch.active_branch,
                            branch_lbl,
                        )) by {
                        }
                        assert(write_nodes.contains_key(addr));
                        assert(write_nodes == loaded_append_write_nodes(receipt, keys, msgs));
                        assert(addr == receipt.target().addr);
                        assert(reads.dom() == receipt.needed_addrs());
                        assert(receipt.needed_addrs().contains(addr)) by {
                            let i = receipt.lines.len() - 1;
                            assert(0 <= i < receipt.lines.len());
                            assert(receipt.lines[i].addr == addr);
                        }
                        assert(reads.contains_key(addr));
                        assert(Cache::State::access(pre_state.cache, post_state.cache, cache_lbl));
                        assert(cache_lbl->reads.contains_key(addr));
                        assert(pre_state.cache.valid_read(addr, reads[addr])) by {
                        }
                        assert(pre_state.cache.entries[slot] is Filled);
                        assert(false);
                    },
                    AtomicBranchState::Step::append_empty(new_active_branch) => {
                        assert(AtomicBranchState::State::append_empty(
                            pre_state.branch,
                            post_state.branch,
                            branch_atomic_lbl,
                            new_active_branch,
                        )) by {
                        }
                        assert(init_root is Some);
                        let init_addr = init_root.unwrap();
                        let branch_lbl = CachedBranch::Label::Initialize{
                            mini_allocator: pre_state.branch.mini_allocator,
                            init_root: init_addr,
                            keys,
                            msgs,
                            write_nodes,
                        };
                        assert(CachedBranch::State::next(
                            pre_state.branch.active_branch,
                            post_state.branch.active_branch,
                            branch_lbl,
                        ));
                        reveal(CachedBranch::State::next);
                        reveal(CachedBranch::State::next_by);
                        assert(CachedBranch::State::next_by(
                            pre_state.branch.active_branch,
                            post_state.branch.active_branch,
                            branch_lbl,
                            CachedBranch::Step::initialize_branch(),
                        ));
                        assert(CachedBranch::State::initialize_branch(
                            pre_state.branch.active_branch,
                            post_state.branch.active_branch,
                            branch_lbl,
                        )) by {
                        }
                        assert(write_nodes.contains_key(addr));
                        assert(write_nodes == loaded_initialize_write_nodes(init_addr, keys, msgs));
                        assert(addr == init_addr);
                        assert(pre_state.branch.mini_allocator.can_allocate(init_addr));
                        assert(init_addr.wf());
                    },
                    _ => {
                        assert(false);
                    },
                }
            }
        }
    }
    cache_access_preserves_shared_cache_disk_inv(pre, post, reads, writes);
    assert(unified_cache_shared_cache_disk_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(pre, post, reads, writes);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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

    assert(reads.dom() == crate::implementation::AtomicBranchState_v::query_receipts_read_addrs(
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
    assert(post.disk == pre.disk);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    cache_access_preserves_cache_request_wf(pre, post, reads, Map::empty());
    cache_access_preserves_cache_disk_response_inv(pre, post, reads, Map::empty());
    assert(unified_cache_cache_request_wf(post));
    assert(unified_cache_cache_disk_response_inv(post));
    cache_access_preserves_shared_cache_disk_inv(pre, post, reads, Map::empty());
    assert(unified_cache_shared_cache_disk_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(
        pre,
        post,
        reads,
        Map::empty(),
    );
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
    }
    assert(post.disk.responses == pre.disk.responses) by {
    }
    assert(post.disk.requests == pre.disk.requests.union_prefer_right(req_map)) by {
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
    assert(post_state.sync_phase == pre_state.sync_phase);
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
            assert(post_state.sync_phase == pre_state.sync_phase);
            assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
            if pre_state.sync_phase is SuperblockWriteIssued {
                let in_flight_req_id = pre_state.sync_phase->req_id;
                if pre.disk.requests.contains_key(in_flight_req_id) {
                    assert(!req_map.contains_key(in_flight_req_id)) by {
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
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(unified_cache_recovery_superblock_io_inv(pre));
        assert(pre_state.recovery_state is Begin);
        assert(post_state.recovery_state is AwaitingSuperblock);
        assert(post_state.persistent_image is None);
        assert(post_state.sync_phase is None);
        assert(post_state.sync_req_map
            == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty());
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk.responses == pre.disk.responses);
        assert(post.disk.content == pre.disk.content);
        assert(post_state.outstanding_cache_reqs.dom().disjoint(post.disk.responses.dom()));
        assert forall |id: ID| {
            &&& #[trigger] post.disk.requests.contains_key(id)
            &&& !post_state.outstanding_cache_reqs.contains_key(id)
        } implies {
            &&& post.disk.requests[id] is ReadReq
            &&& post.disk.requests[id]->from == spec_superblock_addr()
        } by {
            if req_map.contains_key(id) {
                assert(post.disk.requests[id] == req_map[id]);
                assert(req_map[id] == read_req);
            } else {
                assert(pre.disk.requests.contains_key(id));
                assert(!pre_state.outstanding_cache_reqs.contains_key(id));
                assert(pre.disk.requests[id] is ReadReq);
                assert(pre.disk.requests[id]->from == spec_superblock_addr());
                assert(post.disk.requests[id] == pre.disk.requests[id]);
            }
        }
        assert forall |id: ID| {
            &&& #[trigger] post.disk.responses.contains_key(id)
            &&& !post_state.outstanding_cache_reqs.contains_key(id)
        } implies {
            &&& post.disk.responses[id] is ReadResp
            &&& post.disk.content.contains_key(spec_superblock_addr())
            &&& post.disk.responses[id]->data == post.disk.content[spec_superblock_addr()]
        } by {
            assert(pre.disk.responses.contains_key(id));
            assert(!pre_state.outstanding_cache_reqs.contains_key(id));
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
    outstanding_cache_reqs_disk_backed_request_added(pre, post, req_map);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
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
        UnifiedCacheProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheSystem::Step::superblock_recovery(
                req_id,
                raw_page,
                image,
                new_journal,
                new_branch,
                reqs,
                resps,
            ),
            lbl->info,
        ),
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let read_resp = DiskResponse::ReadResp{data: raw_page};
    let resp_map = Map::empty().insert(req_id, read_resp);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };


    assert(lbl is ProgramDiskOp);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(resps == Multiset::empty().insert((req_id, read_resp)));
    assert(multiset_to_map(reqs) == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            multiset_to_map(reqs),
            Map::<ID, DiskRequest>::empty(),
            id => {
                if multiset_to_map(reqs).contains_key(id) {
                    let pr = choose |pr| #[trigger] reqs.contains(pr) && pr.0 == id;
                    assert(reqs.contains(pr));
                    assert(false);
                }
            }
        );
    }
    multiset_map_singleton_ensures(req_id, read_resp);
    assert(multiset_to_map(resps) == resp_map);
    assert(disk_lbl->requests == Map::<ID, DiskRequest>::empty());
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
    }
    assert(post.disk.requests == pre.disk.requests) by {
    }
    assert(post.disk.responses == pre.disk.responses.remove(req_id)) by {
        assert(resp_map.dom() == Set::<ID>::empty().insert(req_id));
    }
    assert(resp_map <= pre.disk.responses) by {
    }
    assert(resp_map.contains_key(req_id));
    assert(resp_map[req_id] == read_resp);
    assert(pre.disk.responses.contains_key(req_id)) by {
        assert(resp_map <= pre.disk.responses);
    }
    assert(pre.disk.responses[req_id] == read_resp) by {
        assert(resp_map <= pre.disk.responses);
    }
    crate::spec::AsyncDisk_t::inv_next(pre.disk, post.disk, disk_lbl);
    assert(post.disk.inv());

    assert(unified_cache_recovery_superblock_io_inv(pre));
    assert(pre_state.recovery_state is AwaitingSuperblock);
    assert(!pre_state.outstanding_cache_reqs.contains_key(req_id)) by {
        assert(pre_state.outstanding_cache_reqs.dom().disjoint(pre.disk.responses.dom()));
        assert(pre.disk.responses.dom().contains(req_id));
    }
    assert(pre.disk.responses[req_id] is ReadResp);
    assert(pre.disk.content.contains_key(spec_superblock_addr()));
    assert(pre.disk.responses[req_id]->data == pre.disk.content[spec_superblock_addr()]);
    assert(raw_page == pre.disk.content[spec_superblock_addr()]);
    assert(superblock_matches(raw_page, image));
    assert(parse_abstract_superblock(pre.disk.content[spec_superblock_addr()]) == image);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);
    let branch_image_aus =
        UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
            post.disk.content,
            image.branch_roots,
        );

    assert(UnifiedCacheJournalRefinement::async_disk_superblock_page_wf(pre.disk.content));
    assert(image.wf());
    assert(pre_state.persistent_image is None);
    assert(pre_state.sync_phase is None);

    assert(post_state == UnifiedCacheSystem::State{
        recovery_state: RecoveryState::SuperblockAvailable,
        journal: new_journal,
        branch: new_branch,
        persistent_image: Option::Some(image),
        sync_phase: AtomicSyncPhase::None,
        sync_req_map: Map::empty(),
        ..pre_state
    });
    assert(post_state.cache == pre_state.cache);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(!post_state.client_ready());

    assert(journal_pre.persistent_superblock_image_i() == image) by {
        assert(journal_pre.persistent_image is None);
        assert(UnifiedCacheJournalRefinement::async_disk_superblock_raw_i(pre.disk.content)
            == pre.disk.content[spec_superblock_addr()]);
    }
    assert(journal_post.persistent_image == Option::Some(image));
    assert(journal_post.cache == journal_pre.cache);
    assert(journal_post.disk.content == journal_pre.disk.content);
    assert(journal_post.in_flight is None);
    assert(journal_post.in_flight_image is None);
    assert(journal_post.journal_caching_disk_i().cache
        == journal_pre.journal_caching_disk_i().cache) by {
        assert(journal_post.journal_projection_aus() =~= journal_pre.journal_projection_aus()) by {
            assert(!journal_post.journal.ready());
            assert(!journal_pre.journal.ready());
            assert(journal_post.persistent_superblock_image_i() == image);
            assert(journal_pre.persistent_superblock_image_i() == image);
            assert(journal_post.disk.content == journal_pre.disk.content);
        }
        assert_maps_equal!(
            journal_post.journal_caching_disk_i().cache,
            journal_pre.journal_caching_disk_i().cache,
            addr => {}
        );
    }
    assert(journal_post.journal_caching_disk_i().status
        == journal_pre.journal_caching_disk_i().status) by {
        assert(journal_post.journal_projection_aus() =~= journal_pre.journal_projection_aus());
        assert_maps_equal!(
            journal_post.journal_caching_disk_i().status,
            journal_pre.journal_caching_disk_i().status,
            addr => {}
        );
    }
    assert(journal_pre.journal_caching_disk_i().cache == Map::<Address, RawPage>::empty());
    assert(journal_pre.journal_caching_disk_i().status == Map::<Address, PageStatus>::empty());
    assert(journal_post.journal_caching_disk_i().cache == Map::<Address, RawPage>::empty());
    assert(journal_post.journal_caching_disk_i().status == Map::<Address, PageStatus>::empty());

    assert(branch_pre.persistent_superblock_image_i() == image) by {
        assert(branch_pre.persistent_image is None);
        assert(UnifiedCacheBranchRefinement::async_disk_superblock_raw_i(pre.disk.content)
            == pre.disk.content[spec_superblock_addr()]);
    }
    assert(branch_post.persistent_image == Option::Some(image));
    assert(branch_post.cache == branch_pre.cache);
    assert(branch_post.disk.content == branch_pre.disk.content);
    assert(branch_post.in_flight is None);
    assert(branch_post.in_flight_image is None);
    assert(project_cache_pages(branch_post.cache, branch_image_aus)
        == Map::<Address, RawPage>::empty()) by {
        assert(branch_post.cache == branch_pre.cache);
        assert(post.disk.content == pre.disk.content);
        assert(branch_image_aus
            =~= UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
                pre.disk.content,
                branch_pre.persistent_superblock_image_i().branch_roots,
            ));
    }
    assert(project_cache_status(branch_post.cache, branch_image_aus)
        == Map::<Address, PageStatus>::empty()) by {
        assert(branch_post.cache == branch_pre.cache);
        assert(post.disk.content == pre.disk.content);
        assert(branch_image_aus
            =~= UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
                pre.disk.content,
                branch_pre.persistent_superblock_image_i().branch_roots,
            ));
    }
    assert(branch_pre.branch_caching_disk_i().cache == Map::<Address, RawPage>::empty());
    assert(branch_pre.branch_caching_disk_i().status == Map::<Address, PageStatus>::empty());
    assert(branch_pre.persistent_branch_image_i().loadable());
    assert(branch_pre.persistent_branch_image_i().stack_wf());

    UnifiedCacheJournalRefinement::load_ephemeral_refines(
        journal_pre,
        journal_post,
        image,
    );
    UnifiedCacheBranchRefinement::load_ephemeral_refines(
        branch_pre,
        branch_post,
        image,
    );

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::LoadEphemeral,
    ));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::LoadEphemeral,
    ));
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty());
    assert(src.sync_reqs == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty());
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase is None);
        assert(pre_state.sync_phase is None);
        assert(!unified_cache_superblock_write_pending(pre));
        assert(!unified_cache_superblock_write_pending(post));
        assert(!unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(!unified_cache_in_flight_superblock_landed(post_state, post.disk));
        assert(post.disk.content == pre.disk.content);
    }
    assert(CrashAwareCachingDiskSystem::State::load_ephemeral_from_persistent(
        src,
        dst,
        target_lbl,
        dst.journal,
        dst.branch,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::load_ephemeral_from_persistent(
            dst.journal,
            dst.branch,
        ),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post));
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert forall |id: ID| {
            &&& #[trigger] post.disk.responses.contains_key(id)
            &&& post_state.outstanding_cache_reqs.contains_key(id)
        } implies {
            let addr = post_state.outstanding_cache_reqs[id];
            let resp = post.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& resp->data == post.disk.content[addr]
            }
            &&& resp is WriteResp ==> {
                &&& post.disk.content.contains_key(addr)
                &&& cache_filled_addr(post_state.cache, addr)
                &&& post.disk.content[addr] == cache_filled_page(post_state.cache, addr)
            }
        } by {
            assert(pre.disk.responses.contains_key(id));
            assert(id != req_id);
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
        }
    }
    assert(unified_cache_recovery_superblock_io_inv(post));
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    outstanding_cache_reqs_disk_backed_response_removed(pre, post, req_id);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_recovery_branch_metadata_agrees(post)) by {
        let roots = post_state.branch.image.sealed_roots;
        let nodes = to_branch_nodes(post.disk.content);
        assert(post_state.branch.mini_allocator == MiniAllocator::empty());
        assert(post_state.branch.image == post_state.branch.persistent_image);
        assert(branch_summary_reads_valid(roots, nodes));
        assert(post_state.branch.branch_summary == Map::<AU, Summary>::empty());
        assert(post_state.branch.branch_summary.dom() == Set::<AU>::empty());
        assert(post_state.branch.branch_summary.dom()
            <= root_aus_up_to(roots, roots.len() as nat)) by {
            assert forall |au: AU| #[trigger] post_state.branch.branch_summary.dom().contains(au)
                implies root_aus_up_to(roots, roots.len() as nat).contains(au) by {
                assert(Set::<AU>::empty().contains(au));
                assert(false);
            }
        }
        assert forall |i: int| #![trigger roots[i]]
            0 <= i < roots.len() && post_state.branch.branch_summary.contains_key(roots[i].au)
            implies {
                &&& crate::implementation::CachedBranch_v::root_summary_read_valid(roots[i], nodes)
                &&& post_state.branch.branch_summary[roots[i].au]
                    == crate::implementation::CachedBranch_v::root_summary_from_read(roots[i], nodes)
            } by {
            if 0 <= i < roots.len() && post_state.branch.branch_summary.contains_key(roots[i].au) {
                assert(post_state.branch.branch_summary.dom().contains(roots[i].au));
                assert(Set::<AU>::empty().contains(roots[i].au));
                assert(false);
            }
        }
        loaded_branch_summary_agrees_from_forall(roots, nodes, post_state.branch.branch_summary);
    }
    assert(inv(post));
}

pub proof fn program_disk_execute_sync_begin_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
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
        UnifiedCacheProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheSystem::Step::execute_sync_begin(
                image,
                journal_reads,
                new_cache,
                new_journal,
                new_branch,
                reqs,
                resps,
            ),
            lbl->info,
        ),
        UnifiedCacheSystem::State::execute_sync_begin(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };
    let cache_lbl = Cache::Label::Access{reads: journal_reads, writes: Map::empty()};
    let journal_lbl = AtomicJournalState::Label::CommitStart{
        snapshot: image.journal_snapshot,
        seq_end: image.journal_seq_end,
        reads: crate::implementation::JournalTypes_v::to_journal_records(journal_reads),
    };
    let branch_image = AtomicBranchImage{
        sealed_roots: image.branch_roots,
        seq_end: image.branch_seq_end,
    };
    let branch_lbl = AtomicBranchState::Label::CommitStart{branch_image};


    assert(lbl is ProgramDiskOp);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(resps.is_empty());
    assert(multiset_to_map(reqs) == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            multiset_to_map(reqs),
            Map::<ID, DiskRequest>::empty(),
            id => {
                if multiset_to_map(reqs).contains_key(id) {
                    let pr = choose |pr| #[trigger] reqs.contains(pr) && pr.0 == id;
                    assert(reqs.contains(pr));
                    assert(false);
                }
            }
        );
    }
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
    assert(disk_lbl->requests == Map::<ID, DiskRequest>::empty());
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
    }
    assert(post.disk.requests == pre.disk.requests) by {
        assert_maps_equal!(
            pre.disk.requests.union_prefer_right(Map::<ID, DiskRequest>::empty()),
            pre.disk.requests,
            id => {}
        );
    }
    assert(post.disk.responses == pre.disk.responses) by {
        assert_maps_equal!(
            pre.disk.responses.remove_keys(Map::<ID, DiskResponse>::empty().dom()),
            pre.disk.responses,
            id => {}
        );
    }
    crate::spec::AsyncDisk_t::inv_next(pre.disk, post.disk, disk_lbl);
    assert(post.disk.inv());

    assert(pre_state.client_ready());
    assert(pre_state.sync_phase is None);
    assert(pre_state.sync_image_metadata_valid(image));
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicJournalState::State::next(pre_state.journal, post_state.journal, journal_lbl));
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, branch_lbl));
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        journal: new_journal,
        branch: new_branch,
        sync_phase: AtomicSyncPhase::Started{image},
        ..pre_state
    });
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.recovery_state == pre_state.recovery_state);

    AtomicJournalState::State::commit_start_effect(pre_state.journal, post_state.journal, journal_lbl);
    AtomicBranchState::State::commit_start_effect(pre_state.branch, post_state.branch, branch_lbl);
    assert(post_state.journal.prepared == false);
    assert(post_state.branch.prepared == false);
    assert(post_state.atomic_inflight_superblock_i() == image) by {
        assert(post_state.journal.in_flight.unwrap().snapshot == image.journal_snapshot);
        assert(post_state.journal.in_flight.unwrap().seq_end == image.journal_seq_end);
        assert(post_state.branch.in_flight.unwrap().sealed_roots == image.branch_roots);
        assert(post_state.branch.in_flight.unwrap().seq_end == image.branch_seq_end);
    }

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_post.in_flight_image == Option::Some(image));
    assert(branch_post.in_flight_image == Option::Some(image));
    journal_projection_aus_subset_system_journal_owned(pre);
    assert(journal_pre.journal_projection_aus() <= unified_cache_system_i(pre).journal_owned_aus());
    let journal_root_set = Set::new(|addr: Address| {
        image.journal_snapshot.freshest_rec() is Some
            && addr == image.journal_snapshot.freshest_rec().unwrap()
    });
    UnifiedCacheJournalRefinement::commit_start_refines(
        journal_pre,
        journal_post,
        image.journal_snapshot,
        image.journal_seq_end,
        journal_reads,
    );
    UnifiedCacheBranchRefinement::commit_start_refines(
        branch_pre,
        branch_post,
        branch_image,
        journal_reads,
    );

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::CommitStart{
            new_boundary_lsn: image.journal_snapshot.boundary_lsn,
            snapshot: image.journal_snapshot,
            seq_end: image.journal_seq_end,
        },
    ));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::CommitStart{
            new_boundary_lsn: image.branch_seq_end,
            sealed_roots: image.branch_roots,
        },
    ));
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post.disk.content == pre.disk.content);
        assert(!unified_cache_superblock_write_pending(pre)) by {
            assert(pre_state.sync_phase is None);
        }
        assert(!unified_cache_superblock_write_pending(post)) by {
            assert(post_state.sync_phase is Started);
        }
        assert(!unified_cache_in_flight_superblock_landed(pre_state, pre.disk)) by {
            assert(pre_state.sync_phase is None);
        }
        assert(!unified_cache_in_flight_superblock_landed(post_state, post.disk)) by {
            assert(post_state.sync_phase is Started);
        }
    }
    assert(CrashAwareCachingDiskSystem::State::commit_start(
        src,
        dst,
        target_lbl,
        dst.journal,
        dst.branch,
        image,
    )) by {
        assert(image.branch_seq_end == image.journal_snapshot.boundary_lsn);
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::commit_start(
            dst.journal,
            dst.branch,
            image,
        ),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal.journal == pre_state.journal.journal);
        assert(post_state.branch.seq_end == pre_state.branch.seq_end);
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal.persistent_seq_end == pre_state.journal.persistent_seq_end);
    }
    cache_access_preserves_cache_request_wf(pre, post, journal_reads, Map::empty());
    assert(unified_cache_cache_request_wf(post));
    cache_access_preserves_cache_disk_response_inv(pre, post, journal_reads, Map::empty());
    assert(unified_cache_cache_disk_response_inv(post));
    cache_access_preserves_shared_cache_disk_inv(pre, post, journal_reads, Map::empty());
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(pre_state.client_ready());
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(
        pre,
        post,
        journal_reads,
        Map::empty(),
    );
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(inv(post));
}

pub proof fn program_disk_execute_sync_prepared_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    req_id: ID,
    req: DiskRequest,
    new_journal: AtomicJournalState::State,
    new_branch: AtomicBranchState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(pre, post, lbl, new_program, new_disk),
        inv(pre),
        UnifiedCacheProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheSystem::Step::execute_sync_prepared(
                req_id,
                req,
                new_journal,
                new_branch,
                reqs,
                resps,
            ),
            lbl->info,
        ),
        UnifiedCacheSystem::State::execute_sync_prepared(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            req_id,
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };
    let req_map = Map::empty().insert(req_id, req);
    let image = pre_state.atomic_inflight_superblock_i();
    let raw_page = req->data;


    assert(lbl is ProgramDiskOp);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(pre_state.sync_phase is Started);
    assert(pre_state.client_ready());
    assert(req is WriteReq);
    assert(req->to == spec_superblock_addr());
    assert(superblock_matches(raw_page, image));
    assert(reqs == Multiset::singleton((req_id, req)));
    assert(reqs == multiset_map_singleton(req_id, req));
    assert(resps.is_empty());
    multiset_map_singleton_ensures(req_id, req);
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
    }
    assert(post.disk.requests == pre.disk.requests.union_prefer_right(req_map)) by {
    }
    assert(post.disk.responses == pre.disk.responses) by {
        assert_maps_equal!(
            pre.disk.responses.remove_keys(Map::<ID, DiskResponse>::empty().dom()),
            pre.disk.responses,
            id => {}
        );
    }
    assert(!pre.disk.requests.contains_key(req_id)) by {
        assert(req_map.dom().contains(req_id));
        assert(disk_lbl->requests.dom().disjoint(pre.disk.requests.dom()));
    }
    assert(!pre.disk.responses.contains_key(req_id)) by {
        assert(req_map.dom().contains(req_id));
        assert(disk_lbl->requests.dom().disjoint(pre.disk.responses.dom()));
    }
    assert(post.disk.requests.contains_key(req_id));
    assert(post.disk.requests[req_id] == req);
    assert(!post.disk.responses.contains_key(req_id));
    crate::spec::AsyncDisk_t::inv_next(pre.disk, post.disk, disk_lbl);
    assert(post.disk.inv());

    assert(post_state == UnifiedCacheSystem::State{
        journal: new_journal,
        branch: new_branch,
        sync_phase: AtomicSyncPhase::SuperblockWriteIssued{req_id, image},
        ..pre_state
    });
    assert(post_state.cache == pre_state.cache);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.recovery_state == pre_state.recovery_state);
    assert(AtomicJournalState::State::next(
        pre_state.journal,
        post_state.journal,
        AtomicJournalState::Label::CommitPrepared,
    ));
    assert(AtomicBranchState::State::next(
        pre_state.branch,
        post_state.branch,
        AtomicBranchState::Label::CommitPrepared,
    ));
    assert(post_state.journal == AtomicJournalState::State{
        prepared: true,
        ..pre_state.journal
    }) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre_state.journal,
            post_state.journal,
            AtomicJournalState::Label::CommitPrepared,
            AtomicJournalState::Step::commit_prepared(),
        ));
    }
    assert(post_state.branch == AtomicBranchState::State{
        prepared: true,
        ..pre_state.branch
    }) by {
        reveal(AtomicBranchState::State::next);
        reveal(AtomicBranchState::State::next_by);
        assert(AtomicBranchState::State::next_by(
            pre_state.branch,
            post_state.branch,
            AtomicBranchState::Label::CommitPrepared,
            AtomicBranchState::Step::commit_prepared(),
        ));
    }
    assert(post_state.journal.journal == pre_state.journal.journal);
    assert(post_state.branch.seq_end == pre_state.branch.seq_end);
    assert(!pre_state.journal.prepared) by {
        assert(unified_cache_sync_phase_inv(pre));
    }
    assert(!pre_state.branch.prepared) by {
        assert(unified_cache_sync_phase_inv(pre));
    }

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_post.cache == journal_pre.cache);
    assert(journal_post.disk.content == journal_pre.disk.content);
    assert(journal_post.persistent_image == journal_pre.persistent_image);
    assert(journal_post.in_flight == journal_pre.in_flight);
    assert(journal_post.in_flight_image == journal_pre.in_flight_image);
    assert(branch_post.cache == branch_pre.cache);
    assert(branch_post.disk.content == branch_pre.disk.content);
    assert(branch_post.persistent_image == branch_pre.persistent_image);
    assert(branch_post.in_flight == branch_pre.in_flight);
    assert(branch_post.in_flight_image == branch_pre.in_flight_image);
    UnifiedCacheJournalRefinement::commit_prepared_refines(journal_pre, journal_post);
    UnifiedCacheBranchRefinement::commit_prepared_refines(branch_pre, branch_post);

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::CommitPrepared,
    ));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::FreezePrepared,
    ));
    assert(src.commit_started());
    assert(src.frozen_superblock_image() == image) by {
        assert(src.journal.frozen.unwrap().snapshot == image.journal_snapshot);
        assert(src.journal.frozen.unwrap().seq_end == image.journal_seq_end);
        assert(src.branch.frozen.unwrap().sealed_roots == image.branch_roots);
        assert(src.branch.frozen.unwrap().seq_end == image.branch_seq_end);
    }
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);

    assert(!unified_cache_superblock_write_pending(pre)) by {
        assert(pre_state.sync_phase is Started);
    }
    assert(unified_cache_superblock_write_pending(post)) by {
        assert(post_state.sync_phase is SuperblockWriteIssued);
        assert(post.disk.requests.contains_key(req_id));
        assert(post.disk.requests[req_id] is WriteReq);
        assert(post.disk.requests[req_id]->to == spec_superblock_addr());
    }
    assert(!unified_cache_in_flight_superblock_landed(pre_state, pre.disk)) by {
        assert(pre_state.sync_phase is Started);
    }
    assert(!unified_cache_in_flight_superblock_landed(post_state, post.disk)) by {
        assert(post_state.sync_phase is SuperblockWriteIssued);
        assert(!post.disk.responses.contains_key(req_id));
    }
    assert(src.superblockstore.in_flight is None);
    assert(!src.superblockstore.landed);
    assert(dst.superblockstore.persistent == src.superblockstore.persistent) by {
        assert(post.disk.content == pre.disk.content);
    }
    assert(dst.superblockstore.in_flight == Option::Some(raw_page));
    assert(!dst.superblockstore.landed);
    assert(SuperblockStore::State::write(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Write{raw: raw_page},
    )) by {
    }
    assert(SuperblockStore::State::next_by(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Write{raw: raw_page},
        SuperblockStore::Step::write(),
    )) by {
        reveal(SuperblockStore::State::next_by);
    }
    reveal(SuperblockStore::State::next);

    assert(CrashAwareCachingDiskSystem::State::commit_prepared(
        src,
        dst,
        target_lbl,
        dst.journal,
        dst.branch,
        dst.superblockstore,
        raw_page,
    )) by {
        assert(superblock_matches(raw_page, src.frozen_superblock_image()));
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::commit_prepared(
            dst.journal,
            dst.branch,
            dst.superblockstore,
            raw_page,
        ),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal.journal == pre_state.journal.journal);
        assert(post_state.branch.seq_end == pre_state.branch.seq_end);
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal.persistent_seq_end == pre_state.journal.persistent_seq_end);
    }
    assert(!post_state.outstanding_cache_reqs.contains_key(req_id)) by {
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        if pre_state.outstanding_cache_reqs.contains_key(req_id) {
            assert(pre_state.outstanding_cache_reqs.dom().contains(req_id));
            assert((pre.disk.requests.dom() + pre.disk.responses.dom()).contains(req_id));
            if pre.disk.requests.contains_key(req_id) {
                assert(false);
            } else {
                assert(pre.disk.responses.contains_key(req_id));
                assert(false);
            }
        }
    }
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase is SuperblockWriteIssued);
    }
    assert(unified_cache_cache_request_wf(post)) by {
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert forall |id: ID| {
            &&& #[trigger] post.disk.responses.contains_key(id)
            &&& post_state.outstanding_cache_reqs.contains_key(id)
        } implies {
            let addr = post_state.outstanding_cache_reqs[id];
            let resp = post.disk.responses[id];
            &&& resp is ReadResp ==> {
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
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(pre_state.client_ready());
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    outstanding_cache_reqs_disk_backed_request_added(pre, post, req_map);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(inv(post));
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
        UnifiedCacheProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheSystem::Step::execute_sync_end(
                journal_discarded_aus,
                new_journal,
                new_branch,
                reqs,
                resps,
            ),
            lbl->info,
        ),
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };
    let phase = pre_state.sync_phase;
    let req_id = phase->req_id;
    let image = phase.image().unwrap();
    let write_resp = DiskResponse::WriteResp{};
    let resp_map = Map::empty().insert(req_id, write_resp);
    let journal_lbl = AtomicJournalState::Label::CommitComplete{
        require_end: pre_state.journal.journal.seq_end(),
        discarded_aus: journal_discarded_aus,
    };
    let branch_lbl = AtomicBranchState::Label::CommitComplete;


    assert(lbl is ProgramDiskOp);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(pre_state.sync_phase is SuperblockWriteIssued);
    assert(pre_state.client_ready());
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(resps == Multiset::singleton((req_id, write_resp)));
    assert(resps == multiset_map_singleton(req_id, write_resp));
    assert(multiset_to_map(reqs) == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            multiset_to_map(reqs),
            Map::<ID, DiskRequest>::empty(),
            id => {
                if multiset_to_map(reqs).contains_key(id) {
                    let pr = choose |pr| #[trigger] reqs.contains(pr) && pr.0 == id;
                    assert(reqs.contains(pr));
                    assert(false);
                }
            }
        );
    }
    multiset_map_singleton_ensures(req_id, write_resp);
    assert(multiset_to_map(resps) == resp_map);
    assert(disk_lbl->requests == Map::<ID, DiskRequest>::empty());
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
    }
    assert(post.disk.requests == pre.disk.requests) by {
    }
    assert(post.disk.responses == pre.disk.responses.remove(req_id)) by {
        assert(resp_map.dom() == Set::<ID>::empty().insert(req_id));
    }
    assert(resp_map <= pre.disk.responses) by {
    }
    assert(resp_map.contains_key(req_id));
    assert(resp_map.dom().contains(req_id));
    assert(resp_map.dom() <= pre.disk.responses.dom()) by {
        assert(resp_map <= pre.disk.responses);
    }
    assert(pre.disk.responses.dom().contains(req_id));
    assert(pre.disk.responses.contains_key(req_id));
    assert(pre.disk.responses[req_id] == write_resp);
    crate::spec::AsyncDisk_t::inv_next(pre.disk, post.disk, disk_lbl);
    assert(post.disk.inv());

    assert(post_state == UnifiedCacheSystem::State{
        free_aus: pre_state.free_aus + journal_discarded_aus,
        journal: new_journal,
        branch: new_branch,
        persistent_image: Option::Some(image),
        sync_phase: AtomicSyncPhase::None,
        ..pre_state
    });
    assert(post_state.cache == pre_state.cache);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    assert(post_state.recovery_state == pre_state.recovery_state);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(AtomicJournalState::State::next(pre_state.journal, post_state.journal, journal_lbl));
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, branch_lbl));

    AtomicJournalState::State::wf_next(pre_state.journal, post_state.journal, journal_lbl);
    AtomicJournalState::State::commit_complete_effect(
        pre_state.journal,
        post_state.journal,
        journal_lbl,
    );
    AtomicBranchState::State::wf_next(pre_state.branch, post_state.branch, branch_lbl);
    AtomicBranchState::State::commit_complete_effect(
        pre_state.branch,
        post_state.branch,
        branch_lbl,
    );

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_post.cache == journal_pre.cache);
    assert(journal_post.disk.content == journal_pre.disk.content);
    assert(journal_pre.in_flight == Option::Some(image));
    assert(journal_pre.in_flight_image == Option::Some(image));
    assert(journal_post.persistent_image == journal_pre.in_flight_image);
    assert(journal_post.in_flight is None);
    assert(journal_post.in_flight_image is None);
    assert(branch_post.cache == branch_pre.cache);
    assert(branch_post.disk.content == branch_pre.disk.content);
    assert(branch_pre.in_flight == Option::Some(image));
    assert(branch_pre.in_flight_image == Option::Some(image));
    assert(branch_post.persistent_image == branch_pre.in_flight_image);
    assert(branch_post.in_flight is None);
    assert(branch_post.in_flight_image is None);

    let require_end = pre_state.journal.journal.seq_end();
    UnifiedCacheJournalRefinement::commit_complete_refines(
        journal_pre,
        journal_post,
        require_end,
        journal_discarded_aus,
    );
    UnifiedCacheBranchRefinement::commit_complete_refines(branch_pre, branch_post);

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::CommitComplete{
            require_end,
            discarded: journal_discarded_aus,
        },
    ));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::CommitComplete,
    ));
    assert(src.branch.ephemeral is Known);
    assert(src.branch.ephemeral->v == branch_pre.branch_caching_disk_state_i());
    assert(src.branch_lsn() == pre_state.branch.seq_end);
    assert(unified_cache_ready_inv(pre));
    assert(pre_state.journal.journal.seq_end() == pre_state.branch.seq_end());
    assert(src.branch_lsn() == require_end);

    assert(unified_cache_sync_phase_inv(pre));
    assert(!pre_state.outstanding_cache_reqs.contains_key(req_id));
    assert(unified_cache_in_flight_superblock_landed(pre_state, pre.disk)) by {
        assert(pre.disk.responses.contains_key(req_id));
        assert(pre.disk.responses[req_id] is WriteResp);
    }
    assert(!unified_cache_superblock_write_pending(pre)) by {
        if pre.disk.requests.contains_key(req_id) {
            assert(pre.disk.inv());
            assert(pre.disk.requests.dom().disjoint(pre.disk.responses.dom()));
            assert(pre.disk.requests.dom().contains(req_id));
            assert(pre.disk.responses.dom().contains(req_id));
            assert(false);
        }
    }
    assert(!unified_cache_in_flight_superblock_landed(post_state, post.disk)) by {
        assert(post_state.sync_phase is None);
    }
    assert(!unified_cache_superblock_write_pending(post)) by {
        assert(post_state.sync_phase is None);
    }
    assert(src.superblockstore.landed);
    assert(src.superblockstore.in_flight is None);
    assert(!dst.superblockstore.landed);
    assert(dst.superblockstore.in_flight is None);
    assert(dst.superblockstore.persistent == src.superblockstore.persistent) by {
        assert(post.disk.content == pre.disk.content);
    }
    assert(SuperblockStore::State::complete(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Complete,
    )) by {
    }
    assert(SuperblockStore::State::next_by(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Complete,
        SuperblockStore::Step::complete(),
    )) by {
        reveal(SuperblockStore::State::next_by);
    }
    reveal(SuperblockStore::State::next);

    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus + journal_discarded_aus);
    assert(CrashAwareCachingDiskSystem::State::commit_complete(
        src,
        dst,
        target_lbl,
        dst.journal,
        dst.branch,
        dst.superblockstore,
        journal_discarded_aus,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::commit_complete(
            dst.journal,
            dst.branch,
            dst.superblockstore,
            journal_discarded_aus,
        ),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_ready_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image is Some);
        assert(post_state.journal.ready());
        assert(post_state.branch.metadata_loaded());
        assert(post_state.journal.journal.seq_end() == pre_state.journal.journal.seq_end());
        assert(post_state.branch.seq_end == pre_state.branch.seq_end);
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post_state.client_ready());
        assert(post_state.persistent_image == Option::Some(image));
        assert(post_state.journal.persistent_seq_end == pre_state.journal.in_flight.unwrap().seq_end);
        assert(journal_pre.in_flight_image is Some);
        assert(journal_pre.in_flight_image.unwrap().journal_seq_end
            == pre_state.journal.in_flight.unwrap().seq_end);
    }
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase is None);
    }
    assert(unified_cache_cache_request_wf(post)) by {
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert forall |id: ID| {
            &&& #[trigger] post.disk.responses.contains_key(id)
            &&& post_state.outstanding_cache_reqs.contains_key(id)
        } implies {
            let addr = post_state.outstanding_cache_reqs[id];
            let resp = post.disk.responses[id];
            &&& resp is ReadResp ==> {
                &&& resp->data == post.disk.content[addr]
            }
            &&& resp is WriteResp ==> {
                &&& post.disk.content.contains_key(addr)
                &&& cache_filled_addr(post_state.cache, addr)
                &&& post.disk.content[addr] == cache_filled_page(post_state.cache, addr)
            }
        } by {
            assert(pre.disk.responses.contains_key(id));
            assert(id != req_id);
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
            assert(unified_cache_cache_disk_response_inv(pre));
        }
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(pre_state.client_ready());
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    outstanding_cache_reqs_disk_backed_response_removed(pre, post, req_id);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(inv(post));
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
        UnifiedCacheSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            UnifiedCacheSystem::Step::cache_io_begin(req_map, new_cache, reqs, resps),
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

    reveal(UnifiedCacheSystem::State::next_by);

    assert(lbl is ProgramDiskOp);
    assert(!(pre_state.recovery_state is Begin));
    assert(!(pre_state.recovery_state is AwaitingSuperblock));
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
    }

    assert(post.disk.content == pre.disk.content) by {
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
    assert(post_state.sync_phase == pre_state.sync_phase);
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
            assert(post_state.sync_phase == pre_state.sync_phase);
            assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
            if pre_state.sync_phase is SuperblockWriteIssued {
                let req_id = pre_state.sync_phase->req_id;
                if pre.disk.requests.contains_key(req_id) {
                    assert(!req_map.contains_key(req_id)) by {
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
                assert(post_state.sync_phase == pre_state.sync_phase);
                assert(pre_state.sync_phase is None);
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
    }
    assert(req_map.dom().disjoint(pre.disk.requests.dom())) by {
    }
    assert(req_map.dom().disjoint(pre.disk.responses.dom())) by {
    }
    cache_io_begin_preserves_cache_request_wf(pre, post, req_map);
    assert(unified_cache_cache_request_wf(post));
    cache_io_begin_preserves_cache_disk_response_inv(pre, post, req_map);
    assert(unified_cache_cache_disk_response_inv(post));
    cache_io_begin_preserves_shared_cache_disk_inv(pre, post, req_map);
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
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
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_io_begin_preserves_outstanding_cache_reqs_disk_backed(pre, post, req_map);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(post_state.journal == pre_state.journal);
            assert(post_state.branch == pre_state.branch);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            let phase = post_state.sync_phase;
            let sync_req_id = phase->req_id;
            assert(pre_state.sync_phase is SuperblockWriteIssued);
            assert(unified_cache_sync_phase_inv(pre));
            assert(!pre_state.outstanding_cache_reqs.contains_key(sync_req_id));
            assert(!post_state.outstanding_cache_reqs.contains_key(sync_req_id)) by {
                if post_state.outstanding_cache_reqs.contains_key(sync_req_id) {
                    if updated.contains_key(sync_req_id) {
                        assert(req_map.contains_key(sync_req_id));
                        if unified_cache_superblock_write_pending(pre) {
                            assert(pre.disk.requests.contains_key(sync_req_id));
                            assert(req_map.dom().disjoint(pre.disk.requests.dom()));
                        } else {
                            assert(pre.disk.responses.contains_key(sync_req_id));
                            assert(req_map.dom().disjoint(pre.disk.responses.dom()));
                        }
                    } else {
                        assert(pre_state.outstanding_cache_reqs.contains_key(sync_req_id));
                    }
                    assert(false);
                }
            }
            if unified_cache_superblock_write_pending(pre) {
                assert(post.disk.requests.contains_key(sync_req_id));
                assert(post.disk.requests[sync_req_id] == pre.disk.requests[sync_req_id]);
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(sync_req_id));
                assert(post.disk.responses.contains_key(sync_req_id));
                assert(post.disk.responses[sync_req_id] == pre.disk.responses[sync_req_id]);
            }
        }
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        if unified_cache_before_metadata_load_complete(post_state) {
            assert(post_state.recovery_state == pre_state.recovery_state);
            assert(unified_cache_before_metadata_load_complete(pre_state));
            assert(unified_cache_recovery_cache_quiescent_inv(pre));
            cache_disk_ops_begin_preserves_all_filled_clean_and_read_requests(
                pre_state.cache,
                post_state.cache,
                req_map,
            );
            assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
                implies post.disk.requests[id] is ReadReq by {
                if req_map.contains_key(id) {
                    assert(post.disk.requests[id] == req_map[id]);
                } else {
                    assert(pre.disk.requests.contains_key(id));
                    assert(post.disk.requests[id] == pre.disk.requests[id]);
                }
            }
        }
    }
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
        UnifiedCacheSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Disk,
            UnifiedCacheSystem::Step::cache_io_end(resp_map, new_cache, reqs, resps),
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

    reveal(UnifiedCacheSystem::State::next_by);

    assert(lbl is ProgramDiskOp);
    assert(!(pre_state.recovery_state is Begin));
    assert(!(pre_state.recovery_state is AwaitingSuperblock));
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
    }
    assert(post.disk.requests == pre.disk.requests) by {
    }
    assert(post.disk.responses == pre.disk.responses.remove_keys(resp_map.dom())) by {
    }
    assert(resp_map <= pre.disk.responses) by {
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
    assert(UnifiedCacheSystem::State::cache_io_end(
        pre_state,
        post_state,
        UnifiedCacheSystem::Label::Disk,
        resp_map,
        new_cache,
        reqs,
        resps,
    )) by {
    }
    assert(post_state.recovery_state == pre_state.recovery_state);
    assert(post_state.journal == pre_state.journal);
    assert(post_state.branch == pre_state.branch);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
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
            assert(post_state.sync_phase == pre_state.sync_phase);
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
                assert(post_state.sync_phase == pre_state.sync_phase);
                assert(pre_state.sync_phase is None);
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
    cache_io_end_preserves_cache_request_wf(pre, post, resp_map, cache_resps);
    assert(unified_cache_cache_request_wf(post));
    cache_io_end_preserves_cache_disk_response_inv(pre, post, resp_map, cache_resps);
    assert(unified_cache_cache_disk_response_inv(post));
    assert(!cache_resps.contains_key(spec_superblock_addr())) by {
        if cache_resps.contains_key(spec_superblock_addr()) {
            assert(finished.contains_key(spec_superblock_addr()));
            Cache::State::invert_contains_pair(
                pre_state.outstanding_cache_reqs.restrict(resp_map.dom()),
                spec_superblock_addr(),
            );
            let id = finished[spec_superblock_addr()];
            assert(pre_state.outstanding_cache_reqs.restrict(resp_map.dom()).contains_pair(
                id,
                spec_superblock_addr(),
            ));
            assert(pre_state.outstanding_cache_reqs.contains_key(id));
            assert(pre_state.outstanding_cache_reqs[id] == spec_superblock_addr());
            assert(pre_state.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
            assert(unified_cache_cache_request_wf(pre));
            assert(false);
        }
    }
    assert(cache_resps.dom() <= Set::new(|addr: Address| addr.wf()));
    cache_io_end_preserves_shared_cache_disk_inv(pre, post, cache_resps);
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
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
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_io_end_preserves_outstanding_cache_reqs_disk_backed(pre, post, resp_map);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(post_state.journal == pre_state.journal);
            assert(post_state.branch == pre_state.branch);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            let phase = post_state.sync_phase;
            let sync_req_id = phase->req_id;
            assert(pre_state.sync_phase is SuperblockWriteIssued);
            assert(unified_cache_sync_phase_inv(pre));
            assert(!pre_state.outstanding_cache_reqs.contains_key(sync_req_id));
            assert(!resp_map.contains_key(sync_req_id)) by {
                if resp_map.contains_key(sync_req_id) {
                    assert(resp_map.dom() <= pre_state.outstanding_cache_reqs.dom());
                    assert(pre_state.outstanding_cache_reqs.contains_key(sync_req_id));
                    assert(false);
                }
            }
            assert(!post_state.outstanding_cache_reqs.contains_key(sync_req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(post.disk.requests.contains_key(sync_req_id));
                assert(post.disk.requests[sync_req_id] == pre.disk.requests[sync_req_id]);
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(sync_req_id));
                assert(post.disk.responses.contains_key(sync_req_id));
                assert(post.disk.responses[sync_req_id] == pre.disk.responses[sync_req_id]);
            }
        }
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        if unified_cache_before_metadata_load_complete(post_state) {
            assert(post_state.recovery_state == pre_state.recovery_state);
            assert(unified_cache_before_metadata_load_complete(pre_state));
            assert(unified_cache_recovery_cache_quiescent_inv(pre));
            assert(post.disk.requests == pre.disk.requests);
            cache_disk_ops_end_preserves_all_filled_clean(
                pre_state.cache,
                post_state.cache,
                cache_resps,
            );
        }
    }
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
    let unified_step = choose |step: UnifiedCacheSystem::Step| #![auto] {
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
            req_id,
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
                req_id,
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
                req_id,
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

pub proof fn program_internal_cache_internal_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_cache: Cache::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            UnifiedCacheSystem::Step::cache_internal(new_cache),
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

    reveal(UnifiedCacheSystem::State::next_by);

    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{ cache: new_cache, ..pre_state });
    assert(Cache::State::next(pre_state.cache, post_state.cache, Cache::Label::Internal{}));
    Cache::State::inv_next(pre_state.cache, post_state.cache, Cache::Label::Internal{});
    assert(post_state.recovery_state == pre_state.recovery_state);
    assert(post_state.journal == pre_state.journal);
    assert(post_state.branch == pre_state.branch);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(journal_pre.same_except_cache_and_disk(journal_post));
    assert(branch_pre.same_except_cache_and_disk(branch_post));
    assert(journal_post.disk.content == journal_pre.disk.content);
    assert(branch_post.disk.content == branch_pre.disk.content);
    assert(journal_post.disk.inv());
    assert(branch_post.disk.inv());

    if journal_pre.superblock_loaded() {
        assert(branch_pre.superblock_loaded());
        journal_pre.loaded_cache_internal_refines_journal_internal(journal_post);
        branch_pre.loaded_cache_internal_refines_branch_internal(branch_post);

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
            assert(post_state.sync_phase == pre_state.sync_phase);
            assert(post.disk == pre.disk);
            assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
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
            assert(journal_post.cache.inv());
            assert(journal_post.disk.inv());
            let aus = journal_pre.journal_projection_aus();
            cache_internal_refines_caching_disk_internal(
                pre_state.cache,
                post_state.cache,
                pre.disk,
                aus,
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
            assert(branch_post.cache.inv());
            assert(branch_post.disk.inv());
            let aus = branch_pre.branch_projection_aus();
            cache_internal_refines_caching_disk_internal(
                pre_state.cache,
                post_state.cache,
                pre.disk,
                aus,
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
        assert(unified_cache_component_refinement_inv(post));

        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        assert(dst == src) by {
            assert(dst.journal == src.journal);
            assert(dst.branch == src.branch);
            assert(dst.progress == src.progress);
            assert(dst.sync_reqs == src.sync_reqs);
            assert(dst.free_aus == src.free_aus);
            assert(dst.superblockstore == src.superblockstore) by {
                assert(post_state.sync_phase == pre_state.sync_phase);
                assert(post.disk == pre.disk);
                assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                    == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
                assert(unified_cache_superblock_write_pending(post)
                    == unified_cache_superblock_write_pending(pre));
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
    cache_internal_preserves_cache_request_wf(pre, post);
    assert(unified_cache_cache_request_wf(post));
    cache_internal_preserves_cache_disk_response_inv(pre, post);
    assert(unified_cache_cache_disk_response_inv(post));
    cache_internal_preserves_shared_cache_disk_inv(pre, post);
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post_state.sync_req_map == pre_state.sync_req_map);
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk == pre.disk);
        if post_state.recovery_state is Begin || post_state.recovery_state is AwaitingSuperblock {
            assert(unified_cache_recovery_superblock_io_inv(pre));
            let journal_aus = journal_pre.journal_projection_aus();
            assert(journal_post.journal_projection_aus() =~= journal_aus);
            cache_internal_preserves_empty_projection(
                pre_state.cache,
                post_state.cache,
                journal_aus,
            );
            assert(journal_post.journal_caching_disk_i().cache
                == Map::<Address, RawPage>::empty()) by {
                assert(project_cache_pages(post_state.cache, journal_aus)
                    == Map::<Address, RawPage>::empty());
                assert_maps_equal!(
                    journal_post.journal_caching_disk_i().cache,
                    Map::<Address, RawPage>::empty(),
                    addr => {
                        if journal_post.journal_caching_disk_i().cache.contains_key(addr) {
                            assert(addresses_in_aus(journal_post.journal_projection_aus()).contains(addr));
                            assert(addresses_in_aus(journal_aus).contains(addr));
                            assert(project_cache_pages(post_state.cache, journal_aus).contains_key(addr));
                            assert(false);
                        }
                    }
                );
            }
            assert(journal_post.journal_caching_disk_i().status
                == Map::<Address, PageStatus>::empty()) by {
                assert(project_cache_status(post_state.cache, journal_aus)
                    == Map::<Address, PageStatus>::empty());
                assert_maps_equal!(
                    journal_post.journal_caching_disk_i().status,
                    Map::<Address, PageStatus>::empty(),
                    addr => {
                        if journal_post.journal_caching_disk_i().status.contains_key(addr) {
                            assert(addresses_in_aus(journal_post.journal_projection_aus()).contains(addr));
                            assert(addresses_in_aus(journal_aus).contains(addr));
                            assert(project_cache_status(post_state.cache, journal_aus).contains_key(addr));
                            assert(false);
                        }
                    }
                );
            }

            let branch_aus = branch_pre.branch_projection_aus();
            assert(branch_post.branch_projection_aus() =~= branch_aus);
            cache_internal_preserves_empty_projection(
                pre_state.cache,
                post_state.cache,
                branch_aus,
            );
            assert(branch_post.branch_caching_disk_i().cache
                == Map::<Address, RawPage>::empty()) by {
                assert(project_cache_pages(post_state.cache, branch_aus)
                    == Map::<Address, RawPage>::empty());
                assert_maps_equal!(
                    branch_post.branch_caching_disk_i().cache,
                    Map::<Address, RawPage>::empty(),
                    addr => {
                        if branch_post.branch_caching_disk_i().cache.contains_key(addr) {
                            assert(addresses_in_aus(branch_post.branch_projection_aus()).contains(addr));
                            assert(addresses_in_aus(branch_aus).contains(addr));
                            assert(project_cache_pages(post_state.cache, branch_aus).contains_key(addr));
                            assert(false);
                        }
                    }
                );
            }
            assert(branch_post.branch_caching_disk_i().status
                == Map::<Address, PageStatus>::empty()) by {
                assert(project_cache_status(post_state.cache, branch_aus)
                    == Map::<Address, PageStatus>::empty());
                assert_maps_equal!(
                    branch_post.branch_caching_disk_i().status,
                    Map::<Address, PageStatus>::empty(),
                    addr => {
                        if branch_post.branch_caching_disk_i().status.contains_key(addr) {
                            assert(addresses_in_aus(branch_post.branch_projection_aus()).contains(addr));
                            assert(addresses_in_aus(branch_aus).contains(addr));
                            assert(project_cache_status(post_state.cache, branch_aus).contains_key(addr));
                            assert(false);
                        }
                    }
                );
            }

            let summary_aus = UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
                pre.disk.content,
                branch_pre.persistent_superblock_image_i().branch_roots,
            );
            assert(summary_aus =~=
                UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
                    post.disk.content,
                    branch_post.persistent_superblock_image_i().branch_roots,
                )
            );
            cache_internal_preserves_empty_projection(
                pre_state.cache,
                post_state.cache,
                summary_aus,
            );
            assert(project_cache_pages(post_state.cache, summary_aus)
                == Map::<Address, RawPage>::empty());
            assert(project_cache_status(post_state.cache, summary_aus)
                == Map::<Address, PageStatus>::empty());
        }
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
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_internal_preserves_outstanding_cache_reqs_disk_backed(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(post_state.journal == pre_state.journal);
            assert(post_state.branch == pre_state.branch);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            let phase = post_state.sync_phase;
            let sync_req_id = phase->req_id;
            assert(pre_state.sync_phase is SuperblockWriteIssued);
            assert(unified_cache_sync_phase_inv(pre));
            assert(!pre_state.outstanding_cache_reqs.contains_key(sync_req_id));
            assert(!post_state.outstanding_cache_reqs.contains_key(sync_req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(post.disk.requests.contains_key(sync_req_id));
                assert(post.disk.requests[sync_req_id] == pre.disk.requests[sync_req_id]);
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(sync_req_id));
                assert(post.disk.responses.contains_key(sync_req_id));
                assert(post.disk.responses[sync_req_id] == pre.disk.responses[sync_req_id]);
            }
        }
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        if unified_cache_before_metadata_load_complete(post_state) {
            assert(post_state.recovery_state == pre_state.recovery_state);
            assert(unified_cache_before_metadata_load_complete(pre_state));
            assert(unified_cache_recovery_cache_quiescent_inv(pre));
            assert(post.disk.requests == pre.disk.requests);
            cache_internal_preserves_all_filled_clean(pre_state.cache, post_state.cache);
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_journal_load_index_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    cache_reads: Map<Address, RawPage>,
    journal_reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::journal_load_index(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            cache_reads,
            journal_reads,
            discovered_aus,
            new_cache,
            new_journal,
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
    let cache_lbl = Cache::Label::Access{reads: cache_reads, writes: Map::empty()};
    let journal_lbl = AtomicJournalState::Label::LoadIndex{
        reads: crate::implementation::JournalTypes_v::to_journal_records(journal_reads),
        discovered_aus,
    };


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        free_aus: pre_state.free_aus - discovered_aus,
        journal: new_journal,
        ..pre_state
    });
    assert(post_state.recovery_state is SuperblockAvailable);
    assert(unified_cache_recovery_metadata_inv(pre));
    assert(pre_state.persistent_image is Some);
    assert(post_state.persistent_image is Some);
    assert(post_state.sync_phase is None);
    assert(journal_reads <= cache_reads);
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicJournalState::State::next(pre_state.journal, post_state.journal, journal_lbl));
    Cache::State::access_read_only_is_noop(pre_state.cache, post_state.cache, cache_reads);
    assert(post_state.cache == pre_state.cache);
    assert(post_state.branch == pre_state.branch);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(journal_pre.superblock_loaded());
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    UnifiedCacheJournalRefinement::load_index_refines(
        journal_pre,
        journal_post,
        cache_reads,
        journal_reads,
        discovered_aus,
    );
    branch_pre.unchanged_by_same_cache_and_disk_content(branch_post);
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::LoadIndex{discovered_aus},
    ));
    assert(dst.branch == src.branch);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus - discovered_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::journal_load_index(
        src,
        dst,
        target_lbl,
        dst.journal,
        discovered_aus,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::journal_load_index(dst.journal, discovered_aus),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(post_state.recovery_state is SuperblockAvailable);
        assert(post_state.persistent_image is Some);
        assert(post_state.sync_phase is None);
        assert(post_state.sync_req_map == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(!(post_state.recovery_state is RecoveryComplete));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(!(post_state.recovery_state is RecoveryComplete));
    }
    cache_access_preserves_cache_request_wf(pre, post, cache_reads, Map::empty());
    assert(unified_cache_cache_request_wf(post));
    cache_access_preserves_cache_disk_response_inv(pre, post, cache_reads, Map::empty());
    assert(unified_cache_cache_disk_response_inv(post));
    cache_access_preserves_shared_cache_disk_inv(pre, post, cache_reads, Map::empty());
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(
        pre,
        post,
        cache_reads,
        Map::empty(),
    );
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase is None);
    }
    assert(inv(post));
}

pub proof fn program_internal_read_for_recovery_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    addr: Address,
    keys: Seq<Key>,
    msgs: Seq<Message>,
    receipt: LoadedPathReceipt,
    init_root: Option<Address>,
    journal_reads: Map<Address, RawPage>,
    branch_reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
    new_branch: AtomicBranchState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::read_for_recovery(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            addr,
            keys,
            msgs,
            receipt,
            init_root,
            journal_reads,
            branch_reads,
            writes,
            new_cache,
            new_journal,
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let reads = journal_reads.union_prefer_right(branch_reads);
    let cache_lbl = Cache::Label::Access{reads, writes};
    let full_msgs = crate::implementation::JournalTypes_v::to_journal_records(
        journal_reads,
    )[addr].message_seq;
    let journal_records = full_msgs.maybe_discard_old(
        pre_state.journal.journal.snapshot.boundary_lsn,
    );
    let branch_records = full_msgs.maybe_discard_old(pre_state.branch.seq_end());
    let journal_lbl = AtomicJournalState::Label::ReadForRecovery{
        messages: journal_records,
        reads: crate::implementation::JournalTypes_v::to_journal_records(journal_reads),
    };
    let branch_lbl = AtomicBranchState::Label::Append{
        keys,
        msgs,
        receipt,
        init_root,
        read_nodes: to_branch_nodes(branch_reads),
        write_nodes: to_branch_nodes(writes),
    };
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post.requests == pre.requests);
    assert(post.replies == pre.replies);
    assert(post.sync_requests == pre.sync_requests);
    assert(post.sync_replies == pre.sync_replies);
    assert(post.id_history == pre.id_history);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        journal: new_journal,
        branch: new_branch,
        ..pre_state
    });
    assert(pre_state.recovery_state is MetadataLoadComplete);
    assert(post_state.recovery_state == pre_state.recovery_state);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicJournalState::State::next(pre_state.journal, post_state.journal, journal_lbl));
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, branch_lbl));
    assert(branch_records == crate::implementation::AllocationBranchStackRefinement_v::append_puts(
        pre_state.branch.seq_end(),
        keys,
        msgs,
    ));

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    assert(journal_pre.superblock_loaded());
    assert(journal_pre.journal.ready());
    assert(branch_pre.superblock_loaded());
    assert(branch_pre.branch.metadata_loaded());

    UnifiedCacheBranchRefinement::cache_access_restrict_reads_same_post(
        pre_state.cache,
        post_state.cache,
        reads,
        branch_reads,
        writes,
    );
    assert(Cache::State::next(
        branch_pre.cache,
        branch_post.cache,
        Cache::Label::Access{reads: branch_reads, writes},
    ));
    UnifiedCacheBranchRefinement::append_refines_with_extra_reads(
        branch_pre,
        branch_post,
        keys,
        msgs,
        receipt,
        init_root,
        branch_reads,
        writes,
    );
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(writes.dom() <= addresses_in_aus(branch_pre.branch_projection_aus()));
    assert(post_state.branch.seq_end() == pre_state.branch.seq_end() + keys.len());

    assert(writes.dom().disjoint(addresses_in_aus(journal_pre.journal_projection_aus()))) by {
        let system = unified_cache_system_i(pre);
        let journal_cj = journal_pre.journal_caching_disk_state_i();
        let branch_cb = branch_pre.branch_caching_disk_state_i();
        assert(system.allocation_wf());
        assert(system.component_disjoint());
        assert(system.journal_owned_aus().disjoint(system.branch_owned_aus()));
        assert(system.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
        assert(system.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
        assert(system.journal.ephemeral is Known);
        assert(system.branch.ephemeral is Known);
        assert(system.journal.ephemeral->v == journal_cj);
        assert(system.branch.ephemeral->v == branch_cb);
        journal_cj.loaded_index_values_accessible();
        branch_cb.metadata_loaded_full_accessible_eq();
        assert(journal_pre.journal_projection_aus() <= system.journal_owned_aus()) by {
            assert forall |au: AU| #[trigger] journal_pre.journal_projection_aus().contains(au)
                implies system.journal_owned_aus().contains(au) by {
                assert(journal_pre.journal_projection_aus() == journal_pre.journal.owned_aus());
                if journal_pre.journal.loaded_index_aus().contains(au) {
                    assert(journal_cj.accessible_aus().contains(au));
                } else {
                    assert(journal_pre.journal.mini_allocator.all_aus().contains(au));
                    assert(journal_cj.accessible_aus().contains(au));
                }
            }
        }
        assert(branch_pre.branch_projection_aus() <= system.branch_owned_aus()) by {
            assert forall |au: AU| #[trigger] branch_pre.branch_projection_aus().contains(au)
                implies system.branch_owned_aus().contains(au) by {
                assert(branch_pre.branch_projection_aus() == branch_pre.branch.owned_aus());
                assert(branch_cb.accessible_aus().contains(au));
                assert(branch_cb.full_accessible_aus().contains(au));
            }
        }
        assert forall |a: Address| #[trigger] writes.dom().contains(a)
            implies !addresses_in_aus(journal_pre.journal_projection_aus()).contains(a) by {
            assert(addresses_in_aus(branch_pre.branch_projection_aus()).contains(a));
            if addresses_in_aus(journal_pre.journal_projection_aus()).contains(a) {
                assert(branch_pre.branch_projection_aus().contains(a.au));
                assert(journal_pre.journal_projection_aus().contains(a.au));
                assert(system.branch_owned_aus().contains(a.au));
                assert(system.journal_owned_aus().contains(a.au));
                assert(false);
            }
        }
    }
    assert(journal_pre.journal_projection_aus() <= unified_cache_system_i(pre).journal_owned_aus()) by {
        let system = unified_cache_system_i(pre);
        let journal_cj = journal_pre.journal_caching_disk_state_i();
        assert(system.allocation_wf());
        assert(system.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
        assert(system.journal.ephemeral is Known);
        assert(system.journal.ephemeral->v == journal_cj);
        journal_cj.loaded_index_values_accessible();
        assert forall |au: AU| #[trigger] journal_pre.journal_projection_aus().contains(au)
            implies system.journal_owned_aus().contains(au) by {
            assert(journal_pre.journal_projection_aus() == journal_pre.journal.owned_aus());
            if journal_pre.journal.loaded_index_aus().contains(au) {
                assert(journal_cj.accessible_aus().contains(au));
            } else {
                assert(journal_pre.journal.mini_allocator.all_aus().contains(au));
                assert(journal_cj.accessible_aus().contains(au));
            }
        }
    }
    let recovery_journal_reads = journal_reads.restrict(
        addresses_in_aus(journal_pre.journal_projection_aus()),
    );
    UnifiedCacheJournalRefinement::read_for_recovery_refines(
        journal_pre,
        journal_post,
        addr,
        journal_reads,
        reads,
        writes,
    );
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(post_state.journal == pre_state.journal);
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(src.branch_lsn() == pre_state.branch.seq_end()) by {
        assert(src.branch.ephemeral is Known);
        assert(src.branch.ephemeral->v == branch_pre.branch_caching_disk_state_i());
    }
    assert(journal_records.maybe_discard_old(src.branch_lsn()) == branch_records) by {
        assert(src.branch_lsn() == pre_state.branch.seq_end());
        assert(pre_state.journal.journal.seq_start()
            == pre_state.journal.journal.snapshot.boundary_lsn);
        assert(pre_state.journal.journal.snapshot.boundary_lsn
            == pre_state.journal.journal.seq_start());
    }
    assert(journal_records.maybe_discard_old(src.branch_lsn())
        == crate::implementation::AllocationBranchStackRefinement_v::append_puts(
            src.branch_lsn(),
            keys,
            msgs,
        )) by {
        assert(src.branch_lsn() == pre_state.branch.seq_end());
        assert(branch_records == crate::implementation::AllocationBranchStackRefinement_v::append_puts(
            pre_state.branch.seq_end(),
            keys,
            msgs,
        ));
    }
    assert(CrashAwareCachingDiskSystem::State::recover(
        src,
        dst,
        target_lbl,
        dst.journal,
        dst.branch,
        journal_records,
        branch_records,
        keys,
        msgs,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::recover(
            dst.journal,
            dst.branch,
            journal_records,
            branch_records,
            keys,
            msgs,
        ),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(post_state.recovery_state is MetadataLoadComplete);
        assert(post_state.persistent_image is Some);
        assert(post_state.journal.ready());
        assert(post_state.branch.metadata_loaded());
        assert(post_state.sync_phase is None);
        assert(post_state.sync_req_map == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(!(post_state.recovery_state is RecoveryComplete));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(!(post_state.recovery_state is RecoveryComplete));
    }
    cache_access_preserves_cache_request_wf(pre, post, reads, writes);
    assert(unified_cache_cache_request_wf(post));
    cache_access_preserves_cache_disk_response_inv(pre, post, reads, writes);
    assert(unified_cache_cache_disk_response_inv(post));
    cache_access_preserves_shared_cache_disk_inv(pre, post, reads, writes);
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        assert(!unified_cache_before_metadata_load_complete(post_state));
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(pre, post, reads, writes);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(unified_cache_sync_phase_inv(pre));
        assert(post_state.sync_phase is None);
    }
    assert(inv(post));
}

pub proof fn program_internal_journal_marshall_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    addr: Address,
    raw_page: RawPage,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::journal_marshall(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            addr,
            raw_page,
            new_cache,
            new_journal,
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
    let writes = Map::<Address, RawPage>::empty().insert(addr, raw_page);
    let cache_lbl = Cache::Label::Access{reads: Map::empty(), writes};
    let journal_lbl = AtomicJournalState::Label::JournalMarshal{
        addr,
        writes: crate::implementation::JournalTypes_v::to_journal_records(writes),
    };
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        journal: new_journal,
        ..pre_state
    });
    assert(pre_state.client_ready());
    assert(post_state.client_ready());
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicJournalState::State::next(pre_state.journal, post_state.journal, journal_lbl));
    assert(post_state.branch == pre_state.branch);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(journal_pre.superblock_loaded());
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));

    UnifiedCacheJournalRefinement::journal_marshal_refines(
        journal_pre,
        journal_post,
        addr,
        raw_page,
    );
    assert(post_state.journal.persistent_seq_end == pre_state.journal.persistent_seq_end);
    assert(post_state.journal.in_flight == pre_state.journal.in_flight);
    assert(post_state.journal.prepared == pre_state.journal.prepared);
    assert(post_state.journal.journal.seq_end() == pre_state.journal.journal.seq_end());

    assert(writes.dom().disjoint(addresses_in_aus(branch_pre.branch_projection_aus()))) by {
        journal_projection_aus_subset_system_journal_owned(pre);
        branch_projection_aus_subset_system_branch_owned(pre);
        let system = unified_cache_system_i(pre);
        assert(system.allocation_wf());
        assert(system.component_disjoint());
        assert(system.journal_owned_aus().disjoint(system.branch_owned_aus()));
        assert(journal_pre.journal_projection_aus().contains(addr.au));
        assert forall |a: Address| #[trigger] writes.contains_key(a)
            implies !addresses_in_aus(branch_pre.branch_projection_aus()).contains(a) by {
            assert(a == addr);
            if addresses_in_aus(branch_pre.branch_projection_aus()).contains(a) {
                assert(branch_pre.branch_projection_aus().contains(addr.au));
                assert(journal_pre.journal_projection_aus().contains(addr.au));
                assert(system.branch_owned_aus().contains(addr.au));
                assert(system.journal_owned_aus().contains(addr.au));
                assert(false);
            }
        }
    }
    branch_pre.unchanged_by_cache_access_outside_branch_projection(
        branch_post,
        Map::empty(),
        writes,
    );
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::Internal,
    ));
    assert(dst.branch == src.branch);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::journal_internal(
        src,
        dst,
        target_lbl,
        dst.journal,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::journal_internal(dst.journal),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(unified_cache_recovery_metadata_inv(pre));
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(unified_cache_ready_inv(pre));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(unified_cache_durable_image_inv(pre));
    }
    cache_access_preserves_cache_request_wf(pre, post, Map::empty(), writes);
    assert(unified_cache_cache_request_wf(post));
    cache_access_preserves_cache_disk_response_inv(pre, post, Map::empty(), writes);
    assert(unified_cache_cache_disk_response_inv(post));
    assert(writes.dom() <= Set::new(|addr: Address| addr.wf())) by {
        assert(addr.wf());
        assert forall |a: Address| #[trigger] writes.dom().contains(a)
            implies Set::new(|addr: Address| addr.wf()).contains(a) by {
            assert(a == addr);
        }
    }
    cache_access_preserves_shared_cache_disk_inv(pre, post, Map::empty(), writes);
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(pre_state.client_ready());
        assert(post_state.client_ready());
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(
        pre,
        post,
        Map::empty(),
        writes,
    );
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(!post_state.journal.prepared);
            assert(!post_state.branch.prepared);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            assert(unified_cache_sync_phase_inv(pre));
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] == pre.disk.responses[phase->req_id]);
            }
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_observe_clean_journal_aus_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    aus: Set<AU>,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::observe_clean_journal_aus(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            aus,
            new_cache,
            new_journal,
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
    let cache_lbl = Cache::Label::EvictableCheck{aus};
    let journal_lbl = AtomicJournalState::Label::ObserveCleanAUs{aus};
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        journal: new_journal,
        ..pre_state
    });
    assert(pre_state.client_ready());
    assert(post_state.client_ready());
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicJournalState::State::next(pre_state.journal, post_state.journal, journal_lbl));

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(pre_state.cache, post_state.cache, cache_lbl, step);
    match cache_step {
        Cache::Step::evictable() => {
            assert(post_state.cache == pre_state.cache);
        },
        _ => {
            assert(false);
        },
    }

    assert(post_state.branch == pre_state.branch);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(journal_pre.superblock_loaded());
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));

    UnifiedCacheJournalRefinement::observe_clean_aus_refines(
        journal_pre,
        journal_post,
        aus,
    );
    assert(journal_post.cache == journal_pre.cache);
    assert(post_state.journal.persistent_seq_end == pre_state.journal.persistent_seq_end);
    assert(post_state.journal.in_flight == pre_state.journal.in_flight);
    assert(post_state.journal.prepared == pre_state.journal.prepared);
    assert(post_state.journal.journal.seq_end() == pre_state.journal.journal.seq_end());

    assert(branch_post == branch_pre);
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::ObserveCleanAUs{aus},
    ));
    assert(dst.branch == src.branch);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::journal_observe_clean_aus(
        src,
        dst,
        target_lbl,
        dst.journal,
        aus,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::journal_observe_clean_aus(dst.journal, aus),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(unified_cache_recovery_metadata_inv(pre));
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(unified_cache_ready_inv(pre));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(unified_cache_durable_image_inv(pre));
    }
    assert(unified_cache_cache_request_wf(post)) by {
        assert(unified_cache_cache_request_wf(pre));
        assert(post_state.cache == pre_state.cache);
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert(unified_cache_cache_disk_response_inv(pre));
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(unified_cache_recovery_superblock_io_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post_state.sync_req_map == pre_state.sync_req_map);
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk == pre.disk);
        assert(post_state.cache == pre_state.cache);
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(!post_state.journal.prepared);
            assert(!post_state.branch.prepared);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            assert(unified_cache_sync_phase_inv(pre));
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] == pre.disk.responses[phase->req_id]);
            }
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_journal_fill_aus_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    aus: Set<AU>,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::journal_fill_aus(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            aus,
            new_journal,
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
    let atomic_lbl = AtomicJournalState::Label::FillAUs{aus};
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        free_aus: pre_state.free_aus - aus,
        journal: new_journal,
        ..pre_state
    });
    assert(pre_state.allocation_metadata_loaded());
    assert(post_state.allocation_metadata_loaded()) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.branch == pre_state.branch);
        assert(AtomicJournalState::State::next(pre_state.journal, post_state.journal, atomic_lbl));
        reveal(AtomicJournalState::State::next);
        let step = choose |step| AtomicJournalState::State::next_by(
            pre_state.journal,
            post_state.journal,
            atomic_lbl,
            step,
        );
        match step {
            AtomicJournalState::Step::fill_aus() => {
                reveal(AtomicJournalState::State::next_by);
                assert(post_state.journal.journal == pre_state.journal.journal);
            },
            _ => {
                reveal(AtomicJournalState::State::next_by);
                assert(false);
            },
        }
    }
    assert(AtomicJournalState::State::next(pre_state.journal, post_state.journal, atomic_lbl));

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    allocation_metadata_loaded_facts(pre);
    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(journal_pre.superblock_loaded());
    assert(journal_pre.journal.ready());
    assert(journal_post.cache == journal_pre.cache);
    assert(journal_post.disk == journal_pre.disk);
    assert(journal_post.persistent_image == journal_pre.persistent_image);
    assert(journal_post.in_flight == journal_pre.in_flight);
    assert(journal_post.in_flight_image == journal_pre.in_flight_image);
    assert(aus.disjoint(journal_pre.journal_projection_aus())) by {
        let system = unified_cache_system_i(pre);
        journal_projection_aus_subset_system_journal_owned(pre);
        assert(system.allocation_wf());
        assert(aus <= pre_state.free_aus);
        assert(pre_state.free_aus.disjoint(system.journal_owned_aus()));
        assert(journal_pre.journal_projection_aus() <= system.journal_owned_aus());
    }
    journal_fill_aus_shared_projection_inv_from_system_inv(pre, aus);
    assert(journal_pre.journal_fill_aus_shared_projection_inv(aus));
    UnifiedCacheJournalRefinement::fill_aus_refines(journal_pre, journal_post, aus);

    assert(branch_post == branch_pre);
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::InternalAlloc{
            allocs: aus,
            deallocs: Set::empty(),
            prune_aus: Set::empty(),
        },
    ));
    assert(dst.branch == src.branch);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus - aus);
    assert(dst.free_aus == (src.free_aus - aus) + Set::<AU>::empty());
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::journal_internal_alloc(
        src,
        dst,
        target_lbl,
        dst.journal,
        aus,
        Set::empty(),
        Set::empty(),
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::journal_internal_alloc(
            dst.journal,
            aus,
            Set::empty(),
            Set::empty(),
        ),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(post_state.journal.journal == pre_state.journal.journal);
        assert(post_state.branch == pre_state.branch);
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(unified_cache_ready_inv(pre));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(unified_cache_durable_image_inv(pre));
    }
    assert(unified_cache_cache_request_wf(post)) by {
        assert(unified_cache_cache_request_wf(pre));
        assert(post_state.cache == pre_state.cache);
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert(unified_cache_cache_disk_response_inv(pre));
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_shared_cache_disk_inv(post)) by {
        assert(unified_cache_shared_cache_disk_inv(pre));
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(unified_cache_recovery_superblock_io_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post_state.sync_req_map == pre_state.sync_req_map);
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk == pre.disk);
        assert(post_state.cache == pre_state.cache);
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(!post_state.journal.prepared);
            assert(!post_state.branch.prepared);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            assert(unified_cache_sync_phase_inv(pre));
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] == pre.disk.responses[phase->req_id]);
            }
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_branch_load_metadata_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    root: Address,
    reads: Map<Address, RawPage>,
    discovered_aus: Set<AU>,
    new_cache: Cache::State,
    new_branch: AtomicBranchState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::branch_load_metadata(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            root,
            reads,
            discovered_aus,
            new_cache,
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let cache_lbl = Cache::Label::Access{reads, writes: Map::empty()};
    let branch_lbl = AtomicBranchState::Label::LoadMetadata{
        root,
        discovered_aus,
        read_nodes: to_branch_nodes(reads),
    };


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        free_aus: pre_state.free_aus - discovered_aus,
        branch: new_branch,
        ..pre_state
    });
    assert(pre_state.recovery_state is SuperblockAvailable);
    assert(post_state.recovery_state is SuperblockAvailable);
    assert(unified_cache_recovery_metadata_inv(pre));
    assert(pre_state.persistent_image is Some);
    assert(post_state.persistent_image is Some);
    assert(pre_state.sync_phase is None);
    assert(post_state.sync_phase is None);
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, branch_lbl));
    Cache::State::access_read_only_is_noop(pre_state.cache, post_state.cache, reads);
    assert(post_state.cache == pre_state.cache);
    assert(post_state.journal == pre_state.journal);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    assert(branch_pre.superblock_loaded());
    assert(branch_pre.branch.mini_allocator == MiniAllocator::empty());
    assert(branch_post.superblock_loaded());
    assert(branch_post.persistent_image == branch_pre.persistent_image);
    assert(branch_post.disk == branch_pre.disk);
    assert(branch_post.cache == branch_pre.cache);
    assert(branch_post.in_flight == branch_pre.in_flight);
    assert(branch_post.in_flight_image == branch_pre.in_flight_image);

    reveal(AtomicBranchState::State::next);
    reveal(AtomicBranchState::State::next_by);
    let branch_step = choose |step: AtomicBranchState::Step|
        AtomicBranchState::State::next_by(pre_state.branch, post_state.branch, branch_lbl, step);
    match branch_step {
        AtomicBranchState::Step::load_metadata() => {
            assert(AtomicBranchState::State::load_metadata(
                pre_state.branch,
                post_state.branch,
                branch_lbl,
            )) by {
            }
        },
        _ => {
            assert(false);
        },
    }
    AtomicBranchState::State::wf_next(pre_state.branch, post_state.branch, branch_lbl);
    assert(post_state.branch.wf());
    assert(post_state.branch.image == pre_state.branch.image);
    assert(post_state.branch.persistent_image == pre_state.branch.persistent_image);
    assert(post_state.branch.in_flight == pre_state.branch.in_flight);
    assert(post_state.branch.prepared == pre_state.branch.prepared);
    assert(post_state.branch.persisted_root_count == pre_state.branch.persisted_root_count);
    assert(post_state.branch.active_branch == pre_state.branch.active_branch);
    assert(post_state.branch.mini_allocator == pre_state.branch.mini_allocator);
    assert(post_state.branch.seq_end == pre_state.branch.seq_end);
    assert(pre_state.branch.image.sealed_roots.contains(root));
    assert(crate::implementation::CachedBranch_v::root_summary_read_valid(
        root,
        to_branch_nodes(reads),
    ));
    assert(discovered_aus == crate::implementation::CachedBranch_v::root_summary_from_read(
        root,
        to_branch_nodes(reads),
    ));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    let roots = pre_state.branch.image.sealed_roots;
    let read_nodes = to_branch_nodes(reads);
    let disk_nodes = to_branch_nodes(pre.disk.content);
    let branch_cdb_pre = branch_pre.branch_caching_disk_state_i();
    assert(branch_cdb_pre.inv());
    assert(branch_cdb_pre.sealed_roots == roots);
    assert(set_addrs_disjoint_aus(roots.to_set())) by {
        assert(branch_cdb_pre.sealed_stack_i().wf(branch_cdb_pre.interpreted_branch_summary()));
    }
    assert(branch_pre.branch.image.sealed_roots == branch_pre.persistent_superblock_image_i().branch_roots) by {
        assert(branch_pre.superblock_loaded());
        assert(branch_pre.inv());
        assert(branch_pre.branch.persistent_image.sealed_roots
            == branch_pre.persistent_superblock_image_i().branch_roots);
        assert(pre_state.branch.image == pre_state.branch.persistent_image);
    }
    UnifiedCacheBranchRefinement::recovery_branch_projection_aus_matches_image_summary(
        branch_pre,
    );

    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(src.branch.ephemeral is Known);
    assert(src.branch.ephemeral->v == branch_cdb_pre);
    assert(src.inv());
    assert(src.allocation_wf());
    assert(src.component_disjoint());
    assert(branch_cdb_pre.visible_branch_nodes().contains_key(root)) by {
        assert(branch_summary_reads_valid(branch_cdb_pre.sealed_roots, branch_cdb_pre.visible_branch_nodes()));
        let root_idx = choose |i: int| 0 <= i < roots.len() && roots[i] == root;
        assert(branch_cdb_pre.sealed_roots[root_idx] == root);
    }
    assert(branch_cdb_pre.disk.visible().contains_key(root));
    to_aus_domain(branch_cdb_pre.disk.visible().dom());
    assert(to_aus(branch_cdb_pre.disk.visible().dom()).contains(root.au));
    assert(branch_cdb_pre.full_accessible_aus().contains(root.au));
    let interpreted_branch_summary = branch_cdb_pre.interpreted_branch_summary();
    branch_cdb_pre.sealed_stack_i().root_au_in_summary(interpreted_branch_summary, root);
    assert(src.branch_owned_aus().contains(root.au)) by {
        assert(src.branch_owned_aus() == src.branch.ephemeral->v.semantic_owned_aus());
        assert(branch_cdb_pre.semantic_owned_aus().contains(root.au));
    }
    assert(!CrashAwareCachingDiskSystem::State::reserved_aus().contains(root.au)) by {
        if CrashAwareCachingDiskSystem::State::reserved_aus().contains(root.au) {
            assert(src.component_owned_aus().contains(root.au));
            assert(false);
        }
    }
    assert(root != spec_superblock_addr()) by {
        if root == spec_superblock_addr() {
            assert(CrashAwareCachingDiskSystem::State::reserved_aus().contains(root.au));
            assert(false);
        }
    }
    assert(reads.contains_key(root));
    Cache::State::access_read_valid(pre_state.cache, post_state.cache, reads, Map::empty(), root);
    assert(pre.disk.content.contains_key(root)) by {
        assert(branch_cdb_pre.disk.visible().contains_key(root));
        assert(branch_cdb_pre.disk == branch_pre.branch_caching_disk_i());
        if branch_cdb_pre.disk.visible_cache().contains_key(root) {
            assert(branch_cdb_pre.disk.status.contains_key(root));
            assert(branch_cdb_pre.disk.status[root] != PageStatus::Clean);
            assert(project_cache_status(
                pre_state.cache,
                branch_pre.branch_projection_aus(),
            ).contains_key(root));
            assert(filled_cache_status(pre_state.cache).contains_key(root));
            assert(filled_cache_status(pre_state.cache)[root] == branch_cdb_pre.disk.status[root]);
            assert(unified_cache_recovery_cache_quiescent_inv(pre));
            assert(cache_all_filled_clean(pre_state.cache));
            assert(false);
        } else {
            assert(branch_cdb_pre.disk.persistent.contains_key(root));
            assert(project_persistent(
                pre.disk,
                branch_pre.branch_projection_aus(),
            ).contains_key(root));
        }
    }
    recovery_valid_read_matches_disk(pre, root, reads[root]);
    assert(read_nodes[root] == disk_nodes[root]) by {
        assert(reads[root] == pre.disk.content[root]);
    }

    if read_nodes[root] is Index {
        let aux = read_nodes[root]->aux_ptr.unwrap();
        assert(reads.contains_key(aux));
        assert(read_nodes.contains_key(aux));
        assert(read_nodes[aux] is Auxiliary);
        assert(disk_nodes[root] is Index);
        assert(disk_nodes[root]->aux_ptr == Some(aux));
        assert(branch_cdb_pre.visible_branch_nodes()[root] == read_nodes[root]) by {
            if branch_cdb_pre.disk.cache.contains_key(root) {
                assert(branch_cdb_pre.disk.cache[root] == cache_filled_page(pre_state.cache, root));
                assert(cache_filled_page(pre_state.cache, root) == reads[root]);
            } else {
                assert(branch_cdb_pre.disk.persistent.contains_key(root));
                assert(branch_cdb_pre.disk.persistent[root] == pre.disk.content[root]);
                assert(pre.disk.content[root] == reads[root]);
            }
        }
        assert(branch_cdb_pre.visible_branch_nodes()[root] is Index);
        assert(branch_cdb_pre.visible_branch_nodes()[root]->aux_ptr == Some(aux));
        assert(branch_cdb_pre.visible_branch_nodes().contains_key(aux)) by {
            assert(crate::implementation::CachedBranch_v::root_summary_read_valid(
                root,
                branch_cdb_pre.visible_branch_nodes(),
            ));
        }
        assert(branch_cdb_pre.disk.visible().contains_key(aux));
        to_aus_domain(branch_cdb_pre.disk.visible().dom());
        assert(to_aus(branch_cdb_pre.disk.visible().dom()).contains(aux.au));
        assert(branch_cdb_pre.full_accessible_aus().contains(aux.au));
        branch_cdb_pre.interpreted_index_root_aux_in_summary(root, aux);
        assert(src.branch_owned_aus().contains(aux.au)) by {
            assert(src.branch_owned_aus() == src.branch.ephemeral->v.semantic_owned_aus());
            assert(branch_cdb_pre.semantic_owned_aus().contains(aux.au));
        }
        assert(!CrashAwareCachingDiskSystem::State::reserved_aus().contains(aux.au)) by {
            if CrashAwareCachingDiskSystem::State::reserved_aus().contains(aux.au) {
                assert(src.component_owned_aus().contains(aux.au));
                assert(false);
            }
        }
        assert(aux != spec_superblock_addr()) by {
            if aux == spec_superblock_addr() {
                assert(CrashAwareCachingDiskSystem::State::reserved_aus().contains(aux.au));
                assert(false);
            }
        }
        Cache::State::access_read_valid(pre_state.cache, post_state.cache, reads, Map::empty(), aux);
        assert(pre.disk.content.contains_key(aux)) by {
            assert(branch_cdb_pre.disk.visible().contains_key(aux));
            assert(branch_cdb_pre.disk == branch_pre.branch_caching_disk_i());
            if branch_cdb_pre.disk.visible_cache().contains_key(aux) {
                assert(branch_cdb_pre.disk.status.contains_key(aux));
                assert(branch_cdb_pre.disk.status[aux] != PageStatus::Clean);
                assert(project_cache_status(
                    pre_state.cache,
                    branch_pre.branch_projection_aus(),
                ).contains_key(aux));
                assert(filled_cache_status(pre_state.cache).contains_key(aux));
                assert(filled_cache_status(pre_state.cache)[aux] == branch_cdb_pre.disk.status[aux]);
                assert(unified_cache_recovery_cache_quiescent_inv(pre));
                assert(cache_all_filled_clean(pre_state.cache));
                assert(false);
            } else {
                assert(branch_cdb_pre.disk.persistent.contains_key(aux));
                assert(project_persistent(
                    pre.disk,
                    branch_pre.branch_projection_aus(),
                ).contains_key(aux));
            }
        }
        recovery_valid_read_matches_disk(pre, aux, reads[aux]);
        assert(read_nodes[aux] == disk_nodes[aux]) by {
            assert(reads[aux] == pre.disk.content[aux]);
        }
    }
    assert(crate::implementation::CachedBranch_v::root_summary_from_read(root, read_nodes)
        == crate::implementation::CachedBranch_v::root_summary_from_read(root, disk_nodes)) by {
        if read_nodes[root] is Index {
            let aux = read_nodes[root]->aux_ptr.unwrap();
            assert(read_nodes[aux] == disk_nodes[aux]);
        }
    }
    assert(loaded_branch_summary_agrees(
        roots,
        disk_nodes,
        post_state.branch.branch_summary,
    )) by {
        loaded_branch_summary_agrees_insert_root(
            roots,
            disk_nodes,
            read_nodes,
            pre_state.branch.branch_summary,
            root,
        );
        assert(post_state.branch.branch_summary
            == pre_state.branch.branch_summary.insert(root.au, discovered_aus));
        assert(discovered_aus
            == crate::implementation::CachedBranch_v::root_summary_from_read(root, read_nodes));
    }
    assert(branch_post.branch.image.sealed_roots
        == branch_post.persistent_superblock_image_i().branch_roots) by {
        assert(branch_post.persistent_superblock_image_i()
            == branch_pre.persistent_superblock_image_i());
        assert(post_state.branch.image == post_state.branch.persistent_image);
        assert(post_state.branch.persistent_image.sealed_roots
            == branch_post.persistent_superblock_image_i().branch_roots);
    }
    assert(branch_post.branch.mini_allocator == MiniAllocator::empty());
    assert(branch_summary_reads_valid(
        branch_post.branch.image.sealed_roots,
        to_branch_nodes(branch_post.disk.content),
    ));
    assert(loaded_branch_summary_agrees(
        branch_post.branch.image.sealed_roots,
        to_branch_nodes(branch_post.disk.content),
        branch_post.branch.branch_summary,
    ));
    UnifiedCacheBranchRefinement::recovery_branch_projection_aus_matches_image_summary(
        branch_post,
    );
    assert(branch_post.branch_projection_aus() =~= branch_pre.branch_projection_aus());
    UnifiedCacheBranchRefinement::load_metadata_refines(
        branch_pre,
        branch_post,
        root,
        reads,
        discovered_aus,
    );
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(journal_post == journal_pre);
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(unified_cache_component_refinement_inv(post));

    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(dst.journal == src.journal);
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::LoadMetadata{root, discovered_aus},
    ));
    CrashAwareCachingDiskBranch::State::load_metadata_discovered_aus_subset_full_accessible(
        src.branch,
        dst.branch,
        root,
        discovered_aus,
    );
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus - discovered_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(discovered_aus <= src.branch_owned_aus()) by {
        assert(src.branch.ephemeral is Known);
        assert(discovered_aus <= src.branch.ephemeral->v.semantic_owned_aus());
        assert(src.branch_owned_aus() == src.branch.ephemeral->v.semantic_owned_aus());
    }
    assert(CrashAwareCachingDiskSystem::State::map_load_metadata(
        src,
        dst,
        target_lbl,
        dst.branch,
        root,
        discovered_aus,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::map_load_metadata(dst.branch, root, discovered_aus),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post));
    assert(unified_cache_ready_inv(post)) by {
        assert(!(post_state.recovery_state is RecoveryComplete));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(!(post_state.recovery_state is RecoveryComplete));
    }
    cache_access_preserves_cache_request_wf(pre, post, reads, Map::empty());
    assert(unified_cache_cache_request_wf(post));
    cache_access_preserves_cache_disk_response_inv(pre, post, reads, Map::empty());
    assert(unified_cache_cache_disk_response_inv(post));
    cache_access_preserves_shared_cache_disk_inv(pre, post, reads, Map::empty());
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(unified_cache_recovery_cache_quiescent_inv(pre));
        assert(post.disk.requests == pre.disk.requests);
        assert(post_state.cache == pre_state.cache);
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(
        pre,
        post,
        reads,
        Map::empty(),
    );
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase is None);
    }
    assert(inv(post));
}

pub proof fn program_internal_metadata_load_complete_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::metadata_load_complete(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
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


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post.requests == pre.requests);
    assert(post.replies == pre.replies);
    assert(post.sync_requests == pre.sync_requests);
    assert(post.sync_replies == pre.sync_replies);
    assert(post.id_history == pre.id_history);
    assert(post_state == UnifiedCacheSystem::State{
        recovery_state: RecoveryState::MetadataLoadComplete,
        ..pre_state
    });
    assert(pre_state.recovery_state is SuperblockAvailable);
    assert(pre_state.journal_metadata_loaded());
    assert(pre_state.branch_metadata_loaded());
    assert(pre_state.branch.mini_allocator
        == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.journal == pre_state.journal);
    assert(post_state.branch == pre_state.branch);
    assert(post_state.cache == pre_state.cache);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    assert(unified_cache_system_i(post) == unified_cache_system_i(pre)) by {
        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        assert(dst.journal == src.journal);
        assert(dst.branch == src.branch);
        assert(dst.progress == src.progress);
        assert(dst.sync_reqs == src.sync_reqs);
        assert(dst.free_aus == src.free_aus);
        assert(dst.superblockstore == src.superblockstore) by {
            assert(post_state.sync_phase == pre_state.sync_phase);
            assert(post.disk == pre.disk);
            assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
            assert(unified_cache_superblock_write_pending(post)
                == unified_cache_superblock_write_pending(pre));
        }
    }
    system_i_noop_next(pre, post, lbl);

    assert(unified_cache_component_refinement_inv(post)) by {
        assert(UnifiedCacheJournalRefinement::unified_cache_journal_source(post)
            == UnifiedCacheJournalRefinement::unified_cache_journal_source(pre));
        assert(UnifiedCacheBranchRefinement::unified_cache_branch_source(post)
            == UnifiedCacheBranchRefinement::unified_cache_branch_source(pre));
        assert(unified_cache_component_refinement_inv(pre));
    }
    assert(unified_cache_superblockstore_refinement_inv(post)) by {
        assert(unified_cache_superblockstore_i(post) == unified_cache_superblockstore_i(pre));
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert(unified_cache_cache_disk_response_inv(pre));
    }
    assert(unified_cache_shared_cache_disk_inv(post)) by {
        assert(unified_cache_shared_cache_disk_inv(pre));
    }
    assert(unified_cache_cache_request_wf(post)) by {
        assert(unified_cache_cache_request_wf(pre));
    }
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post)) by {
        assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(pre));
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(pre_state.persistent_image is Some);
        assert(post_state.persistent_image is Some);
        assert(post_state.journal.ready());
        assert(post_state.branch.metadata_loaded());
        assert(post_state.sync_phase is None);
        assert(post_state.sync_req_map == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::empty());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(!(post_state.recovery_state is RecoveryComplete));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(!(post_state.recovery_state is RecoveryComplete));
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(system_model_progress_history_inv(pre));
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(unified_cache_sync_phase_inv(pre));
    }
    assert(inv(post));
}

pub proof fn program_internal_branch_fill_aus_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    aus: Set<AU>,
    new_branch: AtomicBranchState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::branch_fill_aus(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            aus,
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let atomic_lbl = AtomicBranchState::Label::FillAUs{aus};
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        free_aus: pre_state.free_aus - aus,
        branch: new_branch,
        ..pre_state
    });
    assert(pre_state.allocation_metadata_loaded());
    assert(post_state.allocation_metadata_loaded()) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.journal == pre_state.journal);
        assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, atomic_lbl));
        reveal(AtomicBranchState::State::next);
        let step = choose |step| AtomicBranchState::State::next_by(
            pre_state.branch,
            post_state.branch,
            atomic_lbl,
            step,
        );
        match step {
            AtomicBranchState::Step::fill_aus() => {
                reveal(AtomicBranchState::State::next_by);
                assert(post_state.branch.image == pre_state.branch.image);
                assert(post_state.branch.branch_summary == pre_state.branch.branch_summary);
                assert(post_state.branch.active_branch == pre_state.branch.active_branch);
                assert(post_state.branch.seq_end == pre_state.branch.seq_end);
            },
            _ => {
                reveal(AtomicBranchState::State::next_by);
                assert(false);
            },
        }
    }
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, atomic_lbl));

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    allocation_metadata_loaded_facts(pre);
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    assert(branch_pre.superblock_loaded());
    assert(branch_pre.branch.metadata_loaded());
    assert(branch_post.cache == branch_pre.cache);
    assert(branch_post.disk == branch_pre.disk);
    assert(branch_post.persistent_image == branch_pre.persistent_image);
    assert(branch_post.in_flight == branch_pre.in_flight);
    assert(branch_post.in_flight_image == branch_pre.in_flight_image);
    assert(aus.disjoint(branch_pre.branch_projection_aus())) by {
        let system = unified_cache_system_i(pre);
        branch_projection_aus_subset_system_branch_owned(pre);
        assert(system.allocation_wf());
        assert(aus <= pre_state.free_aus);
        assert(pre_state.free_aus.disjoint(system.branch_owned_aus()));
        assert(branch_pre.branch_projection_aus() <= system.branch_owned_aus());
    }
    branch_fill_aus_shared_projection_inv_from_system_inv(pre, aus);
    assert(branch_pre.branch_fill_aus_shared_projection_inv(aus));
    UnifiedCacheBranchRefinement::fill_aus_refines(branch_pre, branch_post, aus);

    assert(journal_post == journal_pre);
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::InternalAlloc{
            allocs: aus,
            deallocs: Set::empty(),
        },
    ));
    assert(dst.journal == src.journal);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus - aus);
    assert(dst.free_aus == (src.free_aus - aus) + Set::<AU>::empty());
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::map_internal_alloc(
        src,
        dst,
        target_lbl,
        dst.branch,
        aus,
        Set::empty(),
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::map_internal_alloc(
            dst.branch,
            aus,
            Set::empty(),
        ),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(post_state.journal == pre_state.journal);
        assert(post_state.branch.seq_end() == pre_state.branch.seq_end());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(unified_cache_ready_inv(pre));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(unified_cache_durable_image_inv(pre));
    }
    assert(unified_cache_cache_request_wf(post)) by {
        assert(unified_cache_cache_request_wf(pre));
        assert(post_state.cache == pre_state.cache);
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert(unified_cache_cache_disk_response_inv(pre));
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_shared_cache_disk_inv(post)) by {
        assert(unified_cache_shared_cache_disk_inv(pre));
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(unified_cache_recovery_superblock_io_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post_state.sync_req_map == pre_state.sync_req_map);
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk == pre.disk);
        assert(post_state.cache == pre_state.cache);
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(!post_state.journal.prepared);
            assert(!post_state.branch.prepared);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            assert(unified_cache_sync_phase_inv(pre));
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] == pre.disk.responses[phase->req_id]);
            }
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_branch_grow_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_root_addr: Address,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    new_branch: AtomicBranchState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::branch_grow(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            new_root_addr,
            reads,
            writes,
            new_cache,
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let cache_lbl = Cache::Label::Access{reads, writes};
    let branch_lbl = AtomicBranchState::Label::Grow{
        new_root_addr,
        read_nodes: to_branch_nodes(reads),
        write_nodes: to_branch_nodes(writes),
    };
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        branch: new_branch,
        ..pre_state
    });
    assert(pre_state.client_ready());
    assert(post_state.client_ready());
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, branch_lbl));
    assert(post_state.journal == pre_state.journal);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    assert(branch_pre.superblock_loaded());
    assert(branch_pre.branch.metadata_loaded());
    UnifiedCacheBranchRefinement::grow_refines(
        branch_pre,
        branch_post,
        new_root_addr,
        reads,
        writes,
    );
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(writes.dom() <= addresses_in_aus(branch_pre.branch_projection_aus()));

    assert(journal_pre.same_except_cache_and_disk(journal_post));
    assert(journal_post.disk == journal_pre.disk);
    assert(journal_post.journal_projection_aus() =~= journal_pre.journal_projection_aus()) by {
        assert(journal_post.journal == journal_pre.journal);
    }
    branch_writes_disjoint_from_journal_projection(pre, writes.dom());
    journal_pre.inv_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        reads,
        writes,
    );
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(journal_post.persistent_journal_i() == journal_pre.persistent_journal_i()) by {
        assert(journal_post.disk.content == journal_pre.disk.content);
    }
    journal_pre.journal_interpretation_unchanged_by_same_projection(journal_post);
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::Internal,
    ));
    assert(dst.journal == src.journal);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::map_internal(
        src,
        dst,
        target_lbl,
        dst.branch,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::map_internal(dst.branch),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.journal == pre_state.journal);
        assert(post_state.branch.seq_end() == pre_state.branch.seq_end());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(unified_cache_ready_inv(pre));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(unified_cache_durable_image_inv(pre));
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
    }
    cache_access_preserves_cache_request_wf(pre, post, reads, writes);
    assert(unified_cache_cache_request_wf(post));
    cache_access_preserves_cache_disk_response_inv(pre, post, reads, writes);
    assert(unified_cache_cache_disk_response_inv(post));
    cache_access_preserves_shared_cache_disk_inv(pre, post, reads, writes);
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(unified_cache_recovery_superblock_io_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post_state.sync_req_map == pre_state.sync_req_map);
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        assert(post_state.client_ready());
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(pre, post, reads, writes);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(!post_state.journal.prepared);
            assert(!post_state.branch.prepared);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            assert(unified_cache_sync_phase_inv(pre));
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] == pre.disk.responses[phase->req_id]);
            }
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_branch_split_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    new_child_addr: Address,
    receipt: LoadedPathReceipt,
    split_arg: SplitArg,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    new_branch: AtomicBranchState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::branch_split(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            new_child_addr,
            receipt,
            split_arg,
            reads,
            writes,
            new_cache,
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let cache_lbl = Cache::Label::Access{reads, writes};
    let branch_lbl = AtomicBranchState::Label::Split{
        new_child_addr,
        receipt,
        split_arg,
        read_nodes: to_branch_nodes(reads),
        write_nodes: to_branch_nodes(writes),
    };
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        branch: new_branch,
        ..pre_state
    });
    assert(pre_state.client_ready());
    assert(post_state.client_ready());
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, branch_lbl));
    assert(post_state.journal == pre_state.journal);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    assert(branch_pre.superblock_loaded());
    assert(branch_pre.branch.metadata_loaded());
    UnifiedCacheBranchRefinement::split_refines(
        branch_pre,
        branch_post,
        new_child_addr,
        receipt,
        split_arg,
        reads,
        writes,
    );
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(writes.dom() <= addresses_in_aus(branch_pre.branch_projection_aus()));

    assert(journal_pre.same_except_cache_and_disk(journal_post));
    assert(journal_post.disk == journal_pre.disk);
    assert(journal_post.journal_projection_aus() =~= journal_pre.journal_projection_aus()) by {
        assert(journal_post.journal == journal_pre.journal);
    }
    branch_writes_disjoint_from_journal_projection(pre, writes.dom());
    journal_pre.inv_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        reads,
        writes,
    );
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(journal_post.persistent_journal_i() == journal_pre.persistent_journal_i()) by {
        assert(journal_post.disk.content == journal_pre.disk.content);
    }
    journal_pre.journal_interpretation_unchanged_by_same_projection(journal_post);
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::Internal,
    ));
    assert(dst.journal == src.journal);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::map_internal(
        src,
        dst,
        target_lbl,
        dst.branch,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::map_internal(dst.branch),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.journal == pre_state.journal);
        assert(post_state.branch.seq_end() == pre_state.branch.seq_end());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(unified_cache_ready_inv(pre));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(unified_cache_durable_image_inv(pre));
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
    }
    cache_access_preserves_cache_request_wf(pre, post, reads, writes);
    assert(unified_cache_cache_request_wf(post));
    cache_access_preserves_cache_disk_response_inv(pre, post, reads, writes);
    assert(unified_cache_cache_disk_response_inv(post));
    cache_access_preserves_shared_cache_disk_inv(pre, post, reads, writes);
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(unified_cache_recovery_superblock_io_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post_state.sync_req_map == pre_state.sync_req_map);
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        assert(post_state.client_ready());
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(pre, post, reads, writes);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(!post_state.journal.prepared);
            assert(!post_state.branch.prepared);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            assert(unified_cache_sync_phase_inv(pre));
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] == pre.disk.responses[phase->req_id]);
            }
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_branch_seal_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    aux_ptr: Pointer,
    summary: Summary,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    new_cache: Cache::State,
    new_branch: AtomicBranchState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            UnifiedCacheSystem::Step::branch_seal(
                aux_ptr,
                summary,
                reads,
                writes,
                new_cache,
                new_branch,
            ),
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
    let cache_lbl = Cache::Label::Access{reads, writes};
    let branch_lbl = AtomicBranchState::Label::Seal{
        aux_ptr,
        summary,
        read_nodes: to_branch_nodes(reads),
        write_nodes: to_branch_nodes(writes),
    };
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);

    reveal(UnifiedCacheSystem::State::next_by);

    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        branch: new_branch,
        ..pre_state
    });
    assert(pre_state.client_ready());
    assert(post_state.client_ready());
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, branch_lbl));
    assert(UnifiedCacheSystem::State::branch_seal(
        pre_state,
        post_state,
        UnifiedCacheSystem::Label::Internal,
        aux_ptr,
        summary,
        reads,
        writes,
        new_cache,
        new_branch,
    )) by {
    }
    assert(post_state.journal == pre_state.journal);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    assert(branch_pre.superblock_loaded());
    assert(branch_pre.branch.metadata_loaded());
    UnifiedCacheBranchRefinement::seal_refines(
        branch_pre,
        branch_post,
        aux_ptr,
        summary,
        reads,
        writes,
    );
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(writes.dom() <= addresses_in_aus(branch_pre.branch_projection_aus()));

    assert(journal_pre.same_except_cache_and_disk(journal_post));
    assert(journal_post.disk == journal_pre.disk);
    assert(journal_post.journal_projection_aus() =~= journal_pre.journal_projection_aus()) by {
        assert(journal_post.journal == journal_pre.journal);
    }
    branch_writes_disjoint_from_journal_projection(pre, writes.dom());
    journal_pre.inv_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        reads,
        writes,
    );
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(journal_post.persistent_journal_i() == journal_pre.persistent_journal_i()) by {
        assert(journal_post.disk.content == journal_pre.disk.content);
    }
    journal_pre.journal_interpretation_unchanged_by_same_projection(journal_post);
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::Internal,
    ));
    assert(dst.journal == src.journal);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::map_internal(
        src,
        dst,
        target_lbl,
        dst.branch,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::map_internal(dst.branch),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.journal == pre_state.journal);
        assert(post_state.branch.seq_end() == pre_state.branch.seq_end());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(unified_cache_ready_inv(pre));
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(unified_cache_durable_image_inv(pre));
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
    }
    cache_access_preserves_cache_request_wf(pre, post, reads, writes);
    assert(unified_cache_cache_request_wf(post));
    cache_access_preserves_cache_disk_response_inv(pre, post, reads, writes);
    assert(unified_cache_cache_disk_response_inv(post));
    cache_access_preserves_shared_cache_disk_inv(pre, post, reads, writes);
    assert(unified_cache_shared_cache_disk_inv(post));
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(unified_cache_recovery_superblock_io_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post_state.sync_req_map == pre_state.sync_req_map);
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        assert(post_state.client_ready());
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    cache_access_preserves_outstanding_cache_reqs_disk_backed(pre, post, reads, writes);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(!post_state.journal.prepared);
            assert(!post_state.branch.prepared);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            assert(unified_cache_sync_phase_inv(pre));
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] == pre.disk.responses[phase->req_id]);
            }
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_observe_persisted_branch_roots_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
    target_count: nat,
    aus: Set<AU>,
    new_cache: Cache::State,
    new_branch: AtomicBranchState::State,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::observe_persisted_branch_roots(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            target_count,
            aus,
            new_cache,
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
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let cache_lbl = Cache::Label::EvictableCheck{aus};
    let branch_lbl = AtomicBranchState::Label::ObservePersistedRoots{target_count};
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post_state == UnifiedCacheSystem::State{
        cache: new_cache,
        branch: new_branch,
        ..pre_state
    });
    assert(pre_state.client_ready());
    assert(post_state.client_ready());
    assert(aus == sealed_summary_aus_between(
        pre_state.branch.image.sealed_roots,
        pre_state.branch.branch_summary,
        pre_state.branch.persisted_root_count,
        target_count,
    ));
    assert(Cache::State::next(pre_state.cache, post_state.cache, cache_lbl));
    assert(AtomicBranchState::State::next(pre_state.branch, post_state.branch, branch_lbl));
    assert(post_state.journal == pre_state.journal);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    assert(UnifiedCacheJournalRefinement::inv(journal_pre));
    assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    assert(branch_pre.superblock_loaded());
    assert(branch_pre.branch.metadata_loaded());
    UnifiedCacheBranchRefinement::observe_persisted_roots_refines(
        branch_pre,
        branch_post,
        target_count,
        aus,
    );
    assert(UnifiedCacheBranchRefinement::inv(branch_post));
    assert(post_state.cache == pre_state.cache);
    assert(journal_post == journal_pre) by {
        assert(post_state.journal == pre_state.journal);
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
    }
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(unified_cache_component_refinement_inv(post));

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    assert(src.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_pre));
    assert(dst.journal == UnifiedCacheJournalRefinement::unified_cache_journal_i(journal_post));
    assert(src.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_pre));
    assert(dst.branch == UnifiedCacheBranchRefinement::unified_cache_branch_i(branch_post));
    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::Internal,
    ));
    assert(dst.journal == src.journal);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post.disk == pre.disk);
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
            == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
        assert(unified_cache_superblock_write_pending(post)
            == unified_cache_superblock_write_pending(pre));
    }
    assert(CrashAwareCachingDiskSystem::State::map_internal(
        src,
        dst,
        target_lbl,
        dst.branch,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::map_internal(dst.branch),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    system_i_inv_next(pre, post, target_lbl);

    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.journal == pre_state.journal);
        assert(post_state.branch.seq_end() == pre_state.branch.seq_end());
        assert(post_state.branch.metadata_loaded());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(unified_cache_ready_inv(pre));
        assert(post_state.branch.metadata_loaded());
        assert(post_state.branch.seq_end() == pre_state.branch.seq_end());
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(unified_cache_durable_image_inv(pre));
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.journal == pre_state.journal);
    }
    assert(unified_cache_cache_request_wf(post)) by {
        assert(unified_cache_cache_request_wf(pre));
        assert(post_state.cache == pre_state.cache);
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert(unified_cache_cache_disk_response_inv(pre));
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_shared_cache_disk_inv(post)) by {
        assert(unified_cache_shared_cache_disk_inv(pre));
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(unified_cache_recovery_superblock_io_inv(pre));
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(post_state.sync_req_map == pre_state.sync_req_map);
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post.disk == pre.disk);
        assert(post_state.cache == pre_state.cache);
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        assert(unified_cache_recovery_cache_quiescent_inv(pre));
        assert(post_state.cache == pre_state.cache);
        assert(post_state.recovery_state == pre_state.recovery_state);
        assert(post.disk == pre.disk);
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.id_history == pre.id_history);
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    outstanding_cache_reqs_disk_backed_unchanged(pre, post);
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is Started {
            assert(unified_cache_sync_phase_inv(pre));
            assert(!post_state.journal.prepared);
            assert(!post_state.branch.prepared);
        }
        if post_state.sync_phase is SuperblockWriteIssued {
            assert(unified_cache_sync_phase_inv(pre));
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if unified_cache_superblock_write_pending(pre) {
                assert(unified_cache_superblock_write_pending(post));
            } else {
                assert(pre.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] == pre.disk.responses[phase->req_id]);
            }
        }
    }
    assert(inv(post));
}

pub proof fn program_internal_recovery_complete_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheProgramModel,
)
    requires
        SystemModel::State::program_internal(pre, post, lbl, new_program),
        inv(pre),
        UnifiedCacheSystem::State::recovery_complete(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
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
    let journal_lbl = AtomicJournalState::Label::QueryEndLsn{
        end_lsn: pre_state.branch.seq_end(),
    };


    assert(lbl is ProgramInternal);
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop);
    assert(post.program == new_program);
    assert(post.disk == pre.disk);
    assert(post.requests == pre.requests);
    assert(post.replies == pre.replies);
    assert(post.sync_requests == pre.sync_requests);
    assert(post.sync_replies == pre.sync_replies);
    assert(post.id_history == pre.id_history);
    assert(pre_state.recovery_state is MetadataLoadComplete);
    assert(post_state == UnifiedCacheSystem::State{
        recovery_state: RecoveryState::RecoveryComplete,
        ..pre_state
    });
    assert(post_state.persistent_image == pre_state.persistent_image);
    assert(post_state.journal == pre_state.journal);
    assert(post_state.branch == pre_state.branch);
    assert(post_state.cache == pre_state.cache);
    assert(post_state.free_aus == pre_state.free_aus);
    assert(post_state.sync_phase == pre_state.sync_phase);
    assert(post_state.sync_req_map == pre_state.sync_req_map);
    assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
    assert(AtomicJournalState::State::next(pre_state.journal, pre_state.journal, journal_lbl));

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    UnifiedCacheJournalRefinement::recovery_complete_refines_query_end_lsn(pre, post);
    assert(UnifiedCacheJournalRefinement::inv(journal_post));
    assert(journal_pre == journal_post) by {
        assert(post_state.journal == pre_state.journal);
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
    }
    assert(branch_pre == branch_post) by {
        assert(post_state.branch == pre_state.branch);
        assert(post_state.cache == pre_state.cache);
        assert(post.disk == pre.disk);
        assert(post_state.persistent_image == pre_state.persistent_image);
        assert(post_state.sync_phase == pre_state.sync_phase);
    }
    assert(UnifiedCacheBranchRefinement::inv(branch_post)) by {
        assert(UnifiedCacheBranchRefinement::inv(branch_pre));
    }
    assert(unified_cache_component_refinement_inv(post));

    assert(pre_state.journal.journal.seq_end() == pre_state.branch.seq_end());
    assert(post_state.journal.journal.seq_end() == post_state.branch.seq_end());

    assert(unified_cache_system_i(post) == unified_cache_system_i(pre)) by {
        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        assert(dst.journal == src.journal);
        assert(dst.branch == src.branch);
        assert(dst.progress == src.progress);
        assert(dst.sync_reqs == src.sync_reqs);
        assert(dst.free_aus == src.free_aus);
        assert(dst.superblockstore == src.superblockstore) by {
            assert(post_state.sync_phase == pre_state.sync_phase);
            assert(post.disk == pre.disk);
            assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                == unified_cache_in_flight_superblock_landed(pre_state, pre.disk));
            assert(unified_cache_superblock_write_pending(post)
                == unified_cache_superblock_write_pending(pre));
        }
    }
    system_i_noop_next(pre, post, lbl);

    assert(unified_cache_superblockstore_refinement_inv(post)) by {
        assert(unified_cache_superblockstore_i(post) == unified_cache_superblockstore_i(pre));
    }
    assert(unified_cache_recovery_metadata_inv(post)) by {
        assert(unified_cache_recovery_metadata_inv(pre));
        assert(pre_state.persistent_image is Some);
        assert(post_state.persistent_image is Some);
        assert(post_state.journal.ready());
        assert(post_state.branch.metadata_loaded());
    }
    assert(unified_cache_ready_inv(post)) by {
        assert(post_state.client_ready());
        assert(post_state.persistent_image is Some);
        assert(post_state.journal.ready());
        assert(post_state.branch.metadata_loaded());
    }
    assert(unified_cache_durable_image_inv(post)) by {
        assert(post_state.client_ready());
        assert(post_state.persistent_image is Some);
        assert(UnifiedCacheJournalRefinement::inv(journal_post));
        assert(journal_post.superblock_loaded());
        assert(journal_post.journal.persistent_seq_end
            == journal_post.persistent_superblock_image_i().journal_seq_end);
        assert(journal_post.persistent_superblock_image_i()
            == post_state.persistent_image.unwrap());
    }
    assert(unified_cache_cache_request_wf(post)) by {
        assert(unified_cache_cache_request_wf(pre));
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert(unified_cache_cache_disk_response_inv(pre));
    }
    assert(unified_cache_shared_cache_disk_inv(post)) by {
        assert(unified_cache_shared_cache_disk_inv(pre));
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(!(post_state.recovery_state is Begin));
        assert(!(post_state.recovery_state is AwaitingSuperblock));
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post)) by {
        assert(!unified_cache_before_metadata_load_complete(post_state));
    }
    assert(system_model_progress_history_inv(post)) by {
        assert(system_model_progress_history_inv(pre));
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post)) by {
        assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(pre));
    }
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        assert(unified_cache_sync_phase_inv(pre));
    }
    assert(inv(post));
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
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::program_internal(pre, post, lbl, new_program));

    assert(lbl is ProgramInternal);
    assert(post.program == new_program);
    assert(UnifiedCacheProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::Internal{},
    ));
    assert(UnifiedCacheSystem::State::next(
        pre.program.state,
        post.program.state,
        UnifiedCacheSystem::Label::Internal,
    ));
    reveal(UnifiedCacheSystem::State::next);
    reveal(UnifiedCacheSystem::State::next_by);
    let unified_step = choose |step: UnifiedCacheSystem::Step|
        UnifiedCacheSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheSystem::Label::Internal,
            step,
        );
    match unified_step {
        UnifiedCacheSystem::Step::cache_internal(new_cache) => {
            program_internal_cache_internal_refines(pre, post, lbl, new_program, new_cache);
        },
        UnifiedCacheSystem::Step::journal_load_index(
            cache_reads,
            journal_reads,
            discovered_aus,
            new_cache,
            new_journal,
        ) => {
            assert(UnifiedCacheSystem::State::journal_load_index(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                cache_reads,
                journal_reads,
                discovered_aus,
                new_cache,
                new_journal,
            ));
            program_internal_journal_load_index_refines(
                pre,
                post,
                lbl,
                new_program,
                cache_reads,
                journal_reads,
                discovered_aus,
                new_cache,
                new_journal,
            );
        },
        UnifiedCacheSystem::Step::read_for_recovery(
            addr,
            keys,
            msgs,
            receipt,
            init_root,
            journal_reads,
            branch_reads,
            writes,
            new_cache,
            new_journal,
            new_branch,
        ) => {
            assert(UnifiedCacheSystem::State::read_for_recovery(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                addr,
                keys,
                msgs,
                receipt,
                init_root,
                journal_reads,
                branch_reads,
                writes,
                new_cache,
                new_journal,
                new_branch,
            ));
            program_internal_read_for_recovery_refines(
                pre,
                post,
                lbl,
                new_program,
                addr,
                keys,
                msgs,
                receipt,
                init_root,
                journal_reads,
                branch_reads,
                writes,
                new_cache,
                new_journal,
                new_branch,
            );
        },
        UnifiedCacheSystem::Step::journal_marshall(
            addr,
            raw_page,
            new_cache,
            new_journal,
        ) => {
            assert(UnifiedCacheSystem::State::journal_marshall(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                addr,
                raw_page,
                new_cache,
                new_journal,
            ));
            program_internal_journal_marshall_refines(
                pre,
                post,
                lbl,
                new_program,
                addr,
                raw_page,
                new_cache,
                new_journal,
            );
        },
        UnifiedCacheSystem::Step::observe_clean_journal_aus(aus, new_cache, new_journal) => {
            assert(UnifiedCacheSystem::State::observe_clean_journal_aus(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                aus,
                new_cache,
                new_journal,
            ));
            program_internal_observe_clean_journal_aus_refines(
                pre,
                post,
                lbl,
                new_program,
                aus,
                new_cache,
                new_journal,
            );
        },
        UnifiedCacheSystem::Step::journal_fill_aus(aus, new_journal) => {
            assert(UnifiedCacheSystem::State::journal_fill_aus(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                aus,
                new_journal,
            ));
            program_internal_journal_fill_aus_refines(
                pre,
                post,
                lbl,
                new_program,
                aus,
                new_journal,
            );
        },
        UnifiedCacheSystem::Step::branch_load_metadata(
            root,
            reads,
            discovered_aus,
            new_cache,
            new_branch,
        ) => {
            assert(UnifiedCacheSystem::State::branch_load_metadata(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                root,
                reads,
                discovered_aus,
                new_cache,
                new_branch,
            ));
            program_internal_branch_load_metadata_refines(
                pre,
                post,
                lbl,
                new_program,
                root,
                reads,
                discovered_aus,
                new_cache,
                new_branch,
            );
        },
        UnifiedCacheSystem::Step::metadata_load_complete() => {
            assert(UnifiedCacheSystem::State::metadata_load_complete(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
            ));
            program_internal_metadata_load_complete_refines(pre, post, lbl, new_program);
        },
        UnifiedCacheSystem::Step::branch_fill_aus(aus, new_branch) => {
            assert(UnifiedCacheSystem::State::branch_fill_aus(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                aus,
                new_branch,
            ));
            program_internal_branch_fill_aus_refines(
                pre,
                post,
                lbl,
                new_program,
                aus,
                new_branch,
            );
        },
        UnifiedCacheSystem::Step::branch_grow(
            new_root_addr,
            reads,
            writes,
            new_cache,
            new_branch,
        ) => {
            assert(UnifiedCacheSystem::State::branch_grow(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                new_root_addr,
                reads,
                writes,
                new_cache,
                new_branch,
            ));
            program_internal_branch_grow_refines(
                pre,
                post,
                lbl,
                new_program,
                new_root_addr,
                reads,
                writes,
                new_cache,
                new_branch,
            );
        },
        UnifiedCacheSystem::Step::branch_split(
            new_child_addr,
            receipt,
            split_arg,
            reads,
            writes,
            new_cache,
            new_branch,
        ) => {
            assert(UnifiedCacheSystem::State::branch_split(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                new_child_addr,
                receipt,
                split_arg,
                reads,
                writes,
                new_cache,
                new_branch,
            ));
            program_internal_branch_split_refines(
                pre,
                post,
                lbl,
                new_program,
                new_child_addr,
                receipt,
                split_arg,
                reads,
                writes,
                new_cache,
                new_branch,
            );
        },
        UnifiedCacheSystem::Step::branch_seal(
            aux_ptr,
            summary,
            reads,
            writes,
            new_cache,
            new_branch,
        ) => {
            program_internal_branch_seal_refines(
                pre,
                post,
                lbl,
                new_program,
                aux_ptr,
                summary,
                reads,
                writes,
                new_cache,
                new_branch,
            );
        },
        UnifiedCacheSystem::Step::observe_persisted_branch_roots(
            target_count,
            aus,
            new_cache,
            new_branch,
        ) => {
            assert(UnifiedCacheSystem::State::observe_persisted_branch_roots(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
                target_count,
                aus,
                new_cache,
                new_branch,
            ));
            program_internal_observe_persisted_branch_roots_refines(
                pre,
                post,
                lbl,
                new_program,
                target_count,
                aus,
                new_cache,
                new_branch,
            );
        },
        UnifiedCacheSystem::Step::recovery_complete() => {
            assert(UnifiedCacheSystem::State::recovery_complete(
                pre.program.state,
                post.program.state,
                UnifiedCacheSystem::Label::Internal,
            ));
            program_internal_recovery_complete_refines(pre, post, lbl, new_program);
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn disk_internal_process_read_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    id: ID,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::disk_internal(new_disk),
        ),
        inv(pre),
        AsyncDisk::State::next_by(
            pre.disk,
            new_disk,
            DiskLabel::Internal{},
            AsyncDisk::Step::process_read(id),
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    reveal(SystemModel::State::next_by);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);

    assert(lbl is DiskInternal);
    assert(post.program == pre.program);
    assert(post.disk == new_disk);
    assert(DiskModel::next(pre.disk, new_disk, DiskLabel::Internal{}));
    assert(pre.disk.requests.contains_key(id));
    assert(pre.disk.requests[id] is ReadReq);
    assert(new_disk.requests == pre.disk.requests.remove(id));
    assert(new_disk.responses == pre.disk.responses.insert(
        id,
        DiskResponse::ReadResp{data: pre.disk.content[pre.disk.requests[id]->from]},
    ));
    assert(new_disk.content == pre.disk.content);
    crate::spec::AsyncDisk_t::inv_next(pre.disk, new_disk, DiskLabel::Internal{});
    assert(post.disk.inv());

    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

    journal_pre.unchanged_by_same_cache_and_disk_content(journal_post);
    branch_pre.unchanged_by_same_cache_and_disk_content(branch_post);

    assert(unified_cache_system_i(post) == unified_cache_system_i(pre)) by {
        assert(journal_post.i() == journal_pre.i());
        assert(branch_post.i() == branch_pre.i());
        assert(post.program.state == pre.program.state);
        assert(post.requests == pre.requests);
        assert(post.replies == pre.replies);
        assert(post.disk.content == pre.disk.content);
        assert(unified_cache_superblockstore_i(post) == unified_cache_superblockstore_i(pre)) by {
            assert(unified_cache_superblock_write_pending(post)
                == unified_cache_superblock_write_pending(pre)) by {
                if pre.program.state.sync_phase is SuperblockWriteIssued {
                    let phase = pre.program.state.sync_phase;
                    if phase->req_id == id {
                        assert(unified_cache_sync_phase_inv(pre));
                        assert(unified_cache_superblock_write_pending(pre));
                        assert(pre.disk.requests[id] is WriteReq);
                        assert(pre.disk.requests[id] is ReadReq);
                        assert(false);
                    }
                }
            }
            assert(unified_cache_in_flight_superblock_landed(
                post.program.state,
                post.disk,
            ) == unified_cache_in_flight_superblock_landed(
                pre.program.state,
                pre.disk,
            )) by {
                if pre.program.state.sync_phase is SuperblockWriteIssued {
                    let phase = pre.program.state.sync_phase;
                    if phase->req_id == id {
                        assert(unified_cache_sync_phase_inv(pre));
                        if unified_cache_superblock_write_pending(pre) {
                            assert(pre.disk.requests[id] is WriteReq);
                            assert(pre.disk.requests[id] is ReadReq);
                            assert(false);
                        } else {
                            assert(pre.disk.responses.contains_key(id));
                            assert(pre.disk.requests.dom().disjoint(pre.disk.responses.dom()));
                            assert(false);
                        }
                    } else {
                        if pre.disk.responses.contains_key(phase->req_id) {
                            assert(post.disk.responses.contains_key(phase->req_id));
                            assert(post.disk.responses[phase->req_id]
                                == pre.disk.responses[phase->req_id]);
                        }
                    }
                }
            }
        }
    }
    assert(unified_cache_system_i_lbl(pre, post, lbl) == CrashAwareCachingDiskSystem::Label::Noop);
    system_i_noop_next(pre, post, lbl);

    assert(unified_cache_component_refinement_inv(post));
    assert(unified_cache_superblockstore_refinement_inv(post));
    assert(unified_cache_cache_request_wf(post));
    assert(unified_cache_shared_cache_disk_inv(post)) by {
        assert(post.program.state == pre.program.state);
        assert(post.disk.content == pre.disk.content);
    }
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post)) by {
        assert(post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs);
        assert(post.program.state.cache == pre.program.state.cache);
        assert(post.disk.requests == pre.disk.requests.remove(id));
        assert(post.disk.responses == pre.disk.responses.insert(
            id,
            DiskResponse::ReadResp{data: pre.disk.content[pre.disk.requests[id]->from]},
        ));
        assert(post.disk.content == pre.disk.content);
        assert(post.program.state.outstanding_cache_reqs.is_injective());
        assert forall |pending_id: ID|
            #[trigger] post.program.state.outstanding_cache_reqs.contains_key(pending_id)
            implies disk_has_pending_id(post.disk, pending_id)
        by {
            assert(pre.program.state.outstanding_cache_reqs.contains_key(pending_id));
            assert(disk_has_pending_id(pre.disk, pending_id));
            if pending_id == id {
                assert(post.disk.responses.contains_key(id));
            } else if pre.disk.requests.contains_key(pending_id) {
                assert(post.disk.requests.contains_key(pending_id));
            } else {
                assert(pre.disk.responses.contains_key(pending_id));
                assert(post.disk.responses.contains_key(pending_id));
            }
        }
        assert forall |pending_id: ID| {
            &&& #[trigger] post.program.state.outstanding_cache_reqs.contains_key(pending_id)
            &&& post.disk.requests.contains_key(pending_id)
        } implies {
            let addr = post.program.state.outstanding_cache_reqs[pending_id];
            let req = post.disk.requests[pending_id];
            &&& req.addr() == addr
            &&& req is WriteReq ==> {
                &&& post.program.state.cache.lookup_map.contains_key(addr)
                &&& post.program.state.cache.entries[
                    post.program.state.cache.lookup_map[addr]
                ] is Filled
                &&& post.program.state.cache.entries[
                    post.program.state.cache.lookup_map[addr]
                ]->data == req->data
                &&& post.program.state.cache.status_map[
                    post.program.state.cache.lookup_map[addr]
                ] == Status::Writeback{}
            }
        } by {
            assert(pending_id != id);
            assert(pre.program.state.outstanding_cache_reqs.contains_key(pending_id));
            assert(pre.disk.requests.contains_key(pending_id));
            assert(post.disk.requests[pending_id] == pre.disk.requests[pending_id]);
        }
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert forall |resp_id: ID| {
            &&& #[trigger] post.disk.responses.contains_key(resp_id)
            &&& post.program.state.outstanding_cache_reqs.contains_key(resp_id)
        } implies {
            let addr = post.program.state.outstanding_cache_reqs[resp_id];
            let resp = post.disk.responses[resp_id];
            &&& resp is ReadResp ==> {
                &&& resp->data == post.disk.content[addr]
            }
            &&& resp is WriteResp ==> {
                &&& post.disk.content.contains_key(addr)
                &&& cache_filled_addr(post.program.state.cache, addr)
                &&& post.disk.content[addr] == cache_filled_page(post.program.state.cache, addr)
            }
        } by {
            let addr = post.program.state.outstanding_cache_reqs[resp_id];
            if resp_id == id {
                assert(pre.program.state.outstanding_cache_reqs.contains_key(resp_id));
                assert(pre.disk.requests.contains_key(resp_id));
                assert(pre.disk.requests[resp_id].addr() == addr);
                assert(pre.disk.requests[resp_id] is ReadReq);
                assert(pre.disk.requests[resp_id]->from == addr);
                assert(post.disk.responses[resp_id] == DiskResponse::ReadResp{
                    data: pre.disk.content[addr],
                });
            } else {
                assert(pre.disk.responses.contains_key(resp_id));
                assert(pre.program.state.outstanding_cache_reqs.contains_key(resp_id));
                assert(post.disk.responses[resp_id] == pre.disk.responses[resp_id]);
                assert(post.disk.content == pre.disk.content);
                if pre.disk.responses[resp_id] is WriteResp {
                    assert(cache_filled_addr(pre.program.state.cache, addr));
                    assert(cache_filled_page(post.program.state.cache, addr)
                        == cache_filled_page(pre.program.state.cache, addr));
                }
            }
        }
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        if post.program.state.recovery_state is Begin
            || post.program.state.recovery_state is AwaitingSuperblock {
            assert(pre.program.state.recovery_state == post.program.state.recovery_state);
            assert(unified_cache_recovery_superblock_io_inv(pre));
            assert(post.program.state.outstanding_cache_reqs
                == Map::<ID, Address>::empty());
        }
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post));
    assert(unified_cache_recovery_metadata_inv(post));
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post));
    assert(unified_cache_sync_phase_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(inv(post));
}

pub proof fn disk_internal_process_write_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    new_disk: crate::trusted::ProgramModelTrait_t::DiskModel,
    id: ID,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::disk_internal(new_disk),
        ),
        inv(pre),
        AsyncDisk::State::next_by(
            pre.disk,
            new_disk,
            DiskLabel::Internal{},
            AsyncDisk::Step::process_write(id),
        ),
    ensures
        CrashAwareCachingDiskSystem::State::next(
            unified_cache_system_i(pre),
            unified_cache_system_i(post),
            unified_cache_system_i_lbl(pre, post, lbl),
        ),
        inv(post),
{
    reveal(SystemModel::State::next_by);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);

    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let req = pre.disk.requests[id];
    let addr = req->to;
    let write_resp = DiskResponse::WriteResp{};

    assert(lbl is DiskInternal);
    assert(post.program == pre.program);
    assert(post.disk == new_disk);
    assert(DiskModel::next(pre.disk, new_disk, DiskLabel::Internal{}));
    assert(pre.disk.requests.contains_key(id));
    assert(req is WriteReq);
    assert(addr.wf());
    assert(new_disk.requests == pre.disk.requests.remove(id));
    assert(new_disk.responses == pre.disk.responses.insert(id, write_resp));
    assert(new_disk.content == pre.disk.content.insert(addr, req->data));
    crate::spec::AsyncDisk_t::inv_next(pre.disk, new_disk, DiskLabel::Internal{});
    assert(post.disk.inv());
    assert(post_state == pre_state);

    if pre_state.outstanding_cache_reqs.contains_key(id) {
        assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(pre));
        assert(unified_cache_cache_request_wf(pre));
        let cache_addr = pre_state.outstanding_cache_reqs[id];
        assert(req.addr() == cache_addr);
        assert(cache_addr == addr);
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(pre_state.outstanding_cache_reqs.contains_value(spec_superblock_addr()));
                assert(false);
            }
        }
        let slot = pre_state.cache.lookup_map[addr];
        assert(pre_state.cache.lookup_map.contains_key(addr));
        assert(pre_state.cache.entries[slot] is Filled);
        assert(pre_state.cache.entries[slot]->data == req->data);
        assert(pre_state.cache.status_map[slot] == Status::Writeback{});
        pre_state.cache.build_lookup_map_ensures();
        assert(cache_filled_addr(pre_state.cache, addr));
        assert(cache_filled_page(pre_state.cache, addr) == req->data);
        assert(filled_cache_status(pre_state.cache).contains_key(addr));
        assert(cache_status_i(pre_state.cache, addr) == PageStatus::Writeback);
        assert(filled_cache_status(pre_state.cache)[addr] == PageStatus::Writeback);

        let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
        let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
        let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
        let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);

        assert(journal_pre.same_except_cache_and_disk(journal_post));
        assert(branch_pre.same_except_cache_and_disk(branch_post));
        assert(journal_post.cache == journal_pre.cache);
        assert(branch_post.cache == branch_pre.cache);

        assert(UnifiedCacheJournalRefinement::async_disk_superblock_page_wf(
            post.disk.content,
        )) by {
            assert(UnifiedCacheJournalRefinement::async_disk_superblock_page_wf(
                pre.disk.content,
            ));
            assert(post.disk.content.contains_key(spec_superblock_addr()));
            assert(post.disk.content[spec_superblock_addr()]
                == pre.disk.content[spec_superblock_addr()]);
        }
        assert(UnifiedCacheBranchRefinement::async_disk_superblock_page_wf(
            post.disk.content,
        )) by {
            assert(UnifiedCacheBranchRefinement::async_disk_superblock_page_wf(
                pre.disk.content,
            ));
            assert(post.disk.content.contains_key(spec_superblock_addr()));
            assert(post.disk.content[spec_superblock_addr()]
                == pre.disk.content[spec_superblock_addr()]);
        }
        assert(journal_post.persistent_superblock_image_i()
            == journal_pre.persistent_superblock_image_i()) by {
            if journal_pre.persistent_image is Some {
                assert(journal_post.persistent_image == journal_pre.persistent_image);
            } else {
                assert(journal_post.persistent_image is None);
                assert(post.disk.content[spec_superblock_addr()]
                    == pre.disk.content[spec_superblock_addr()]);
            }
        }
        assert(branch_post.persistent_superblock_image_i()
            == branch_pre.persistent_superblock_image_i()) by {
            if branch_pre.persistent_image is Some {
                assert(branch_post.persistent_image == branch_pre.persistent_image);
            } else {
                assert(branch_post.persistent_image is None);
                assert(post.disk.content[spec_superblock_addr()]
                    == pre.disk.content[spec_superblock_addr()]);
            }
        }

        async_disk_process_write_refines_projected_internal(
            pre_state.cache,
            pre.disk,
            post.disk,
            journal_pre.journal_projection_aus(),
            id,
        );
        async_disk_process_write_refines_projected_internal(
            pre_state.cache,
            pre.disk,
            post.disk,
            branch_pre.branch_projection_aus(),
            id,
        );
        async_disk_process_write_preserves_readable(
            pre_state.cache,
            pre.disk,
            post.disk,
            branch_pre.branch_projection_aus(),
            id,
        );
        assert(CachingDisk::State::next(
            journal_pre.journal_caching_disk_i(),
            journal_post.journal_caching_disk_i(),
            CachingDisk::Label::Internal{},
        )) by {
            assert(journal_post.journal_projection_aus() =~=
                journal_pre.journal_projection_aus());
        }
        assert(CachingDisk::State::next(
            branch_pre.branch_caching_disk_i(),
            branch_post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        )) by {
            assert(branch_post.branch_projection_aus() =~=
                branch_pre.branch_projection_aus());
        }
        assert(branch_post.branch_caching_disk_i().readable()
            == branch_pre.branch_caching_disk_i().readable()) by {
            assert(branch_pre.cache == pre_state.cache);
            assert(branch_post.cache == pre_state.cache);
            assert(branch_post.branch_projection_aus() =~=
                branch_pre.branch_projection_aus());
        }

        if journal_pre.superblock_loaded() {
            assert(branch_pre.superblock_loaded());
            journal_pre.loaded_caching_disk_internal_refines_journal_internal_preserves_inv(
                journal_post,
            );
            assert forall |addr: Address| {
                #[trigger] mini_allocator_allocated_addrs(
                    branch_pre.branch_caching_disk_state_i().mini_allocator,
                ).contains(addr)
            } implies {
                &&& branch_post.branch_caching_disk_i().readable().contains_key(addr)
                    == branch_pre.branch_caching_disk_state_i().disk.readable().contains_key(addr)
                &&& branch_post.branch_caching_disk_i().readable().contains_key(addr) ==>
                    branch_post.branch_caching_disk_i().readable()[addr]
                        == branch_pre.branch_caching_disk_state_i().disk.readable()[addr]
            } by {
                assert(branch_pre.branch_caching_disk_state_i().disk
                    == branch_pre.branch_caching_disk_i());
            }
            branch_pre.loaded_caching_disk_internal_refines_branch_internal_preserves_inv(
                branch_post,
            );

            let src = unified_cache_system_i(pre);
            let dst = unified_cache_system_i(post);
            let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
            assert(target_lbl == CrashAwareCachingDiskSystem::Label::Noop) by {
                assert(!unified_cache_in_flight_superblock_landed(pre_state, pre.disk)
                    || !unified_cache_in_flight_superblock_landed(post_state, post.disk)
                    || unified_cache_in_flight_superblock_landed(pre_state, pre.disk)
                        == unified_cache_in_flight_superblock_landed(post_state, post.disk));
                if pre_state.sync_phase is SuperblockWriteIssued {
                    let phase = pre_state.sync_phase;
                    assert(phase->req_id != id) by {
                        if phase->req_id == id {
                            assert(unified_cache_sync_phase_inv(pre));
                            assert(!pre_state.outstanding_cache_reqs.contains_key(phase->req_id));
                            assert(false);
                        }
                    }
                    if unified_cache_in_flight_superblock_landed(pre_state, pre.disk) {
                        assert(pre.disk.responses.contains_key(phase->req_id));
                        assert(post.disk.responses.contains_key(phase->req_id));
                    }
                    if unified_cache_in_flight_superblock_landed(post_state, post.disk) {
                        assert(post.disk.responses.contains_key(phase->req_id));
                        assert(phase->req_id != id);
                        assert(pre.disk.responses.contains_key(phase->req_id));
                    }
                }
            }
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
                assert(post_state.sync_phase == pre_state.sync_phase);
                assert(unified_cache_superblock_write_pending(post)
                    == unified_cache_superblock_write_pending(pre)) by {
                    if pre_state.sync_phase is SuperblockWriteIssued {
                        let phase = pre_state.sync_phase;
                        assert(phase->req_id != id) by {
                            if phase->req_id == id {
                                assert(unified_cache_sync_phase_inv(pre));
                                assert(!pre_state.outstanding_cache_reqs.contains_key(id));
                                assert(false);
                            }
                        }
                        if pre.disk.requests.contains_key(phase->req_id) {
                            assert(post.disk.requests.contains_key(phase->req_id));
                            assert(post.disk.requests[phase->req_id]
                                == pre.disk.requests[phase->req_id]);
                        }
                    }
                }
                assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)
                    == unified_cache_in_flight_superblock_landed(pre_state, pre.disk)) by {
                    if pre_state.sync_phase is SuperblockWriteIssued {
                        let phase = pre_state.sync_phase;
                        assert(phase->req_id != id) by {
                            if phase->req_id == id {
                                assert(unified_cache_sync_phase_inv(pre));
                                assert(!pre_state.outstanding_cache_reqs.contains_key(id));
                                assert(false);
                            }
                        }
                        if pre.disk.responses.contains_key(phase->req_id) {
                            assert(post.disk.responses.contains_key(phase->req_id));
                        }
                        if post.disk.responses.contains_key(phase->req_id) {
                            assert(pre.disk.responses.contains_key(phase->req_id));
                        }
                    }
                }
                assert(post.disk.content[spec_superblock_addr()]
                    == pre.disk.content[spec_superblock_addr()]);
            }
            assert(CrashAwareCachingDiskSystem::State::component_internals(
                src,
                dst,
                target_lbl,
                dst.journal,
                dst.branch,
            )) by {
            }
            assert(CrashAwareCachingDiskSystem::State::next_by(
                src,
                dst,
                target_lbl,
                CrashAwareCachingDiskSystem::Step::component_internals(
                    dst.journal,
                    dst.branch,
                ),
            )) by {
                reveal(CrashAwareCachingDiskSystem::State::next_by);
            }
            reveal(CrashAwareCachingDiskSystem::State::next);
            system_i_inv_next(pre, post, target_lbl);
        } else {
            assert(!branch_pre.superblock_loaded());
            assert(pre_state.persistent_image is None);
            assert(unified_cache_before_metadata_load_complete(pre_state)) by {
                assert(unified_cache_recovery_metadata_inv(pre));
                match pre_state.recovery_state {
                    RecoveryState::Begin => {},
                    RecoveryState::AwaitingSuperblock => {},
                    RecoveryState::SuperblockAvailable => {
                        assert(pre_state.persistent_image is Some);
                        assert(false);
                    },
                    RecoveryState::MetadataLoadComplete => {
                        assert(pre_state.persistent_image is Some);
                        assert(false);
                    },
                    RecoveryState::RecoveryComplete => {
                        assert(pre_state.persistent_image is Some);
                        assert(false);
                    },
                }
            }
            assert(unified_cache_recovery_cache_quiescent_inv(pre));
            assert(pre.disk.requests[id] is ReadReq);
            assert(pre.disk.requests[id] is WriteReq);
            assert(false);
        }

        assert(unified_cache_component_refinement_inv(post));
        assert(unified_cache_superblockstore_refinement_inv(post));
    } else {
        assert(unified_cache_non_cache_write_request_inv(pre));
        assert(unified_cache_sync_phase_inv(pre));
        assert(pre_state.sync_phase is SuperblockWriteIssued);
        let phase = pre_state.sync_phase;
        let image = phase.image().unwrap();
        assert(id == phase->req_id);
        assert(addr == spec_superblock_addr());
        assert(unified_cache_superblock_write_pending(pre));
        assert(unified_cache_superblock_write_request_inv(pre));
        assert(superblock_matches(req->data, pre_state.atomic_inflight_superblock_i()));
        assert(pre_state.atomic_inflight_superblock_i() == image);
        assert(image.wf());
        assert(abstract_superblock_raw_wf(req->data));
        assert(post.disk.content.contains_key(spec_superblock_addr()));
        assert(post.disk.content[spec_superblock_addr()] == req->data);
        assert(UnifiedCacheJournalRefinement::async_disk_superblock_page_wf(
            post.disk.content,
        ));
        assert(UnifiedCacheBranchRefinement::async_disk_superblock_page_wf(
            post.disk.content,
        ));

        let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
        let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
        let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
        let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);
        assert(journal_pre.same_except_cache_and_disk(journal_post));
        assert(branch_pre.same_except_cache_and_disk(branch_post));
        assert(pre_state.client_ready()) by {
            assert(unified_cache_recovery_metadata_inv(pre));
            if !(pre_state.recovery_state is RecoveryComplete) {
                assert(pre_state.sync_phase is None);
                assert(false);
            }
        }
        assert(journal_pre.superblock_loaded()) by {
            assert(unified_cache_ready_inv(pre));
        }
        assert(branch_pre.superblock_loaded()) by {
            assert(unified_cache_ready_inv(pre));
        }
        assert(journal_pre.journal.ready()) by {
            assert(unified_cache_ready_inv(pre));
        }
        assert(branch_pre.branch.metadata_loaded()) by {
            assert(unified_cache_ready_inv(pre));
        }
        assert(journal_post.superblock_loaded());
        assert(branch_post.superblock_loaded());
        assert(journal_post.journal_projection_aus() =~=
            journal_pre.journal_projection_aus()) by {
            assert(journal_post.journal == journal_pre.journal);
        }
        assert(branch_post.branch_projection_aus() =~=
            branch_pre.branch_projection_aus()) by {
            assert(branch_post.branch == branch_pre.branch);
        }
        let journal_aus = journal_pre.journal_projection_aus();
        let branch_aus = branch_pre.branch_projection_aus();
        let system = unified_cache_system_i(pre);
        journal_projection_aus_subset_system_journal_owned(pre);
        branch_projection_aus_subset_system_branch_owned(pre);
        assert(system.component_disjoint());
        assert(CrashAwareCachingDiskSystem::State::reserved_aus().contains(
            spec_superblock_addr().au,
        ));
        assert(!journal_aus.contains(spec_superblock_addr().au)) by {
            if journal_aus.contains(spec_superblock_addr().au) {
                assert(system.journal_owned_aus().contains(spec_superblock_addr().au));
                assert(system.component_disjoint());
                assert(false);
            }
        }
        assert(!branch_aus.contains(spec_superblock_addr().au)) by {
            if branch_aus.contains(spec_superblock_addr().au) {
                assert(system.branch_owned_aus().contains(spec_superblock_addr().au));
                assert(system.component_disjoint());
                assert(false);
            }
        }
        assert(journal_post.journal_caching_disk_i()
            == journal_pre.journal_caching_disk_i()) by {
            assert_maps_equal!(
                journal_post.journal_caching_disk_i().cache,
                journal_pre.journal_caching_disk_i().cache,
                a => {}
            );
            assert_maps_equal!(
                journal_post.journal_caching_disk_i().status,
                journal_pre.journal_caching_disk_i().status,
                a => {}
            );
            assert_maps_equal!(
                journal_post.journal_caching_disk_i().persistent,
                journal_pre.journal_caching_disk_i().persistent,
                a => {
                    if journal_post.journal_caching_disk_i().persistent.contains_key(a) {
                        assert(addresses_in_aus(journal_aus).contains(a));
                        assert(journal_aus.contains(a.au));
                        assert(a.au != spec_superblock_addr().au);
                        assert(a != spec_superblock_addr());
                        assert(post.disk.content[a] == pre.disk.content[a]);
                    }
                    if journal_pre.journal_caching_disk_i().persistent.contains_key(a) {
                        assert(addresses_in_aus(journal_aus).contains(a));
                        assert(journal_aus.contains(a.au));
                        assert(a.au != spec_superblock_addr().au);
                        assert(a != spec_superblock_addr());
                        assert(post.disk.content[a] == pre.disk.content[a]);
                    }
                }
            );
        }
        assert(branch_post.branch_caching_disk_i()
            == branch_pre.branch_caching_disk_i()) by {
            assert_maps_equal!(
                branch_post.branch_caching_disk_i().cache,
                branch_pre.branch_caching_disk_i().cache,
                a => {}
            );
            assert_maps_equal!(
                branch_post.branch_caching_disk_i().status,
                branch_pre.branch_caching_disk_i().status,
                a => {}
            );
            assert_maps_equal!(
                branch_post.branch_caching_disk_i().persistent,
                branch_pre.branch_caching_disk_i().persistent,
                a => {
                    if branch_post.branch_caching_disk_i().persistent.contains_key(a) {
                        assert(addresses_in_aus(branch_aus).contains(a));
                        assert(branch_aus.contains(a.au));
                        assert(a.au != spec_superblock_addr().au);
                        assert(a != spec_superblock_addr());
                        assert(post.disk.content[a] == pre.disk.content[a]);
                    }
                    if branch_pre.branch_caching_disk_i().persistent.contains_key(a) {
                        assert(addresses_in_aus(branch_aus).contains(a));
                        assert(branch_aus.contains(a.au));
                        assert(a.au != spec_superblock_addr().au);
                        assert(a != spec_superblock_addr());
                        assert(post.disk.content[a] == pre.disk.content[a]);
                    }
                }
            );
        }
        journal_pre.journal_interpretation_unchanged_by_same_projection(journal_post);
        branch_pre.branch_interpretation_unchanged_by_same_projection(branch_post);
        assert(UnifiedCacheJournalRefinement::inv(journal_post)) by {
            assert(journal_post.inv()) by {
                assert(journal_post.journal.wf());
                assert(UnifiedCacheJournalRefinement::async_disk_superblock_page_wf(
                    post.disk.content,
                ));
                assert(journal_post.persistent_superblock_image_i()
                    == journal_pre.persistent_superblock_image_i());
                assert(journal_post.persistent_superblock_image_i().wf());
                assert(journal_post.cache.inv());
                assert(journal_post.disk.inv());
                assert(journal_post.journal_caching_disk_i().inv());
                assert(journal_post.in_flight == journal_pre.in_flight);
                assert(journal_post.in_flight_image == journal_pre.in_flight_image);
            }
            assert(journal_post.semantic_inv()) by {
                assert(journal_post.i() == journal_pre.i());
                assert(journal_pre.semantic_inv());
            }
        }
        assert(UnifiedCacheBranchRefinement::inv(branch_post)) by {
            assert(branch_post.inv()) by {
                assert(branch_post.branch.wf());
                assert(UnifiedCacheBranchRefinement::async_disk_superblock_page_wf(
                    post.disk.content,
                ));
                assert(branch_post.persistent_superblock_image_i()
                    == branch_pre.persistent_superblock_image_i());
                assert(branch_post.persistent_superblock_image_i().wf());
                assert(branch_post.cache.inv());
                assert(branch_post.disk.inv());
                assert(branch_post.branch_caching_disk_i().inv());
                assert(branch_post.in_flight == branch_pre.in_flight);
                assert(branch_post.in_flight_image == branch_pre.in_flight_image);
            }
            assert(branch_post.semantic_inv()) by {
                assert(branch_post.i() == branch_pre.i());
                assert(branch_pre.semantic_inv());
            }
        }

        assert(!unified_cache_superblock_write_pending(post)) by {
            assert(!post.disk.requests.contains_key(id));
        }
        assert(!unified_cache_in_flight_superblock_landed(pre_state, pre.disk)) by {
            if pre.disk.responses.contains_key(id) {
                assert(pre.disk.inv());
                assert(pre.disk.requests.dom().disjoint(pre.disk.responses.dom()));
                assert(false);
            }
        }
        assert(unified_cache_in_flight_superblock_landed(post_state, post.disk)) by {
            assert(post.disk.responses.contains_key(id));
            assert(post.disk.responses[id] is WriteResp);
            assert(!post_state.outstanding_cache_reqs.contains_key(id));
        }

        let src = unified_cache_system_i(pre);
        let dst = unified_cache_system_i(post);
        let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
        assert(target_lbl == CrashAwareCachingDiskSystem::Label::Sync);
        assert(src.journal == dst.journal);
        assert(src.branch == dst.branch);
        assert(src.progress == dst.progress);
        assert(src.sync_reqs == dst.sync_reqs);
        assert(src.free_aus == dst.free_aus);
        assert(src.superblockstore.in_flight == Option::Some(req->data)) by {
            assert(unified_cache_superblock_write_pending(pre));
        }
        assert(!src.superblockstore.landed);
        assert(dst.superblockstore.persistent == req->data);
        assert(dst.superblockstore.in_flight is None);
        assert(dst.superblockstore.landed);
        assert(SuperblockStore::State::land(
            src.superblockstore,
            dst.superblockstore,
            SuperblockStore::Label::Land,
        )) by {
        }
        assert(SuperblockStore::State::next_by(
            src.superblockstore,
            dst.superblockstore,
            SuperblockStore::Label::Land,
            SuperblockStore::Step::land(),
        )) by {
            reveal(SuperblockStore::State::next_by);
        }
        reveal(SuperblockStore::State::next);
        assert(CrashAwareCachingDiskSystem::State::superblock_write_lands(
            src,
            dst,
            target_lbl,
            dst.superblockstore,
        )) by {
        }
        assert(CrashAwareCachingDiskSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskSystem::Step::superblock_write_lands(dst.superblockstore),
        )) by {
            reveal(CrashAwareCachingDiskSystem::State::next_by);
        }
        reveal(CrashAwareCachingDiskSystem::State::next);
        system_i_inv_next(pre, post, target_lbl);

        assert(unified_cache_component_refinement_inv(post));
        assert(unified_cache_superblockstore_refinement_inv(post));
    }

    assert(unified_cache_cache_request_wf(post)) by {
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post_state.cache == pre_state.cache);
    }
    assert(unified_cache_shared_cache_disk_inv(post)) by {
        assert(post_state.cache == pre_state.cache);
        assert forall |content_addr: Address| {
            &&& #[trigger] post.disk.content.contains_key(content_addr)
            &&& content_addr != spec_superblock_addr()
        } implies content_addr.wf() by {
            if content_addr == addr {
                assert(addr.wf());
            } else {
                assert(pre.disk.content.contains_key(content_addr));
                assert(unified_cache_shared_cache_disk_inv(pre));
            }
        }
        assert forall |clean_addr: Address| {
            &&& #[trigger] filled_cache_status(post_state.cache).contains_key(clean_addr)
            &&& filled_cache_status(post_state.cache)[clean_addr] == PageStatus::Clean
            &&& clean_addr != spec_superblock_addr()
            &&& post.disk.content.contains_key(clean_addr)
        } implies post.disk.content[clean_addr] == cache_filled_page(post_state.cache, clean_addr) by {
            assert(filled_cache_status(pre_state.cache).contains_key(clean_addr));
            assert(filled_cache_status(pre_state.cache)[clean_addr] == PageStatus::Clean);
            assert(unified_cache_shared_cache_disk_inv(pre));
            if clean_addr == addr {
                assert(pre_state.outstanding_cache_reqs.contains_key(id)) by {
                    if !pre_state.outstanding_cache_reqs.contains_key(id) {
                        assert(addr == spec_superblock_addr());
                        assert(clean_addr != spec_superblock_addr());
                        assert(false);
                    }
                }
                let slot = pre_state.cache.lookup_map[addr];
                assert(pre_state.cache.status_map[slot] == Status::Writeback{});
                assert(cache_status_i(pre_state.cache, addr) == PageStatus::Writeback);
                assert(false);
            } else {
                assert(pre.disk.content.contains_key(clean_addr));
                assert(post.disk.content[clean_addr] == pre.disk.content[clean_addr]);
            }
        }
    }
    assert(unified_cache_outstanding_cache_reqs_disk_backed_inv(post)) by {
        assert(post_state.outstanding_cache_reqs == pre_state.outstanding_cache_reqs);
        assert(post_state.cache == pre_state.cache);
        assert(post_state.outstanding_cache_reqs.is_injective());
        assert forall |pending_id: ID|
            #[trigger] post_state.outstanding_cache_reqs.contains_key(pending_id)
            implies disk_has_pending_id(post.disk, pending_id)
        by {
            assert(pre_state.outstanding_cache_reqs.contains_key(pending_id));
            assert(disk_has_pending_id(pre.disk, pending_id));
            if pending_id == id {
                assert(post.disk.responses.contains_key(id));
            } else if pre.disk.requests.contains_key(pending_id) {
                assert(post.disk.requests.contains_key(pending_id));
            } else {
                assert(pre.disk.responses.contains_key(pending_id));
                assert(post.disk.responses.contains_key(pending_id));
            }
        }
        assert forall |pending_id: ID| {
            &&& #[trigger] post_state.outstanding_cache_reqs.contains_key(pending_id)
            &&& post.disk.requests.contains_key(pending_id)
        } implies {
            let pending_addr = post_state.outstanding_cache_reqs[pending_id];
            let pending_req = post.disk.requests[pending_id];
            &&& pending_req.addr() == pending_addr
            &&& pending_req is WriteReq ==> {
                &&& post_state.cache.lookup_map.contains_key(pending_addr)
                &&& post_state.cache.entries[
                    post_state.cache.lookup_map[pending_addr]
                ] is Filled
                &&& post_state.cache.entries[
                    post_state.cache.lookup_map[pending_addr]
                ]->data == pending_req->data
                &&& post_state.cache.status_map[
                    post_state.cache.lookup_map[pending_addr]
                ] == Status::Writeback{}
            }
        } by {
            assert(pending_id != id);
            assert(pre_state.outstanding_cache_reqs.contains_key(pending_id));
            assert(pre.disk.requests.contains_key(pending_id));
            assert(post.disk.requests[pending_id] == pre.disk.requests[pending_id]);
        }
    }
    assert(unified_cache_cache_disk_response_inv(post)) by {
        assert forall |resp_id: ID| {
            &&& #[trigger] post.disk.responses.contains_key(resp_id)
            &&& post_state.outstanding_cache_reqs.contains_key(resp_id)
        } implies {
            let resp_addr = post_state.outstanding_cache_reqs[resp_id];
            let resp = post.disk.responses[resp_id];
            &&& resp is ReadResp ==> {
                &&& resp->data == post.disk.content[resp_addr]
            }
            &&& resp is WriteResp ==> {
                &&& post.disk.content.contains_key(resp_addr)
                &&& cache_filled_addr(post_state.cache, resp_addr)
                &&& post.disk.content[resp_addr] == cache_filled_page(post_state.cache, resp_addr)
            }
        } by {
            let resp_addr = post_state.outstanding_cache_reqs[resp_id];
            if resp_id == id {
                assert(pre_state.outstanding_cache_reqs.contains_key(id));
                assert(resp_addr == addr);
                assert(post.disk.responses[id] == write_resp);
                assert(cache_filled_addr(post_state.cache, addr));
                assert(cache_filled_page(post_state.cache, addr) == req->data);
                assert(post.disk.content[addr] == req->data);
            } else {
                assert(pre.disk.responses.contains_key(resp_id));
                assert(pre_state.outstanding_cache_reqs.contains_key(resp_id));
                assert(post.disk.responses[resp_id] == pre.disk.responses[resp_id]);
                assert(unified_cache_cache_disk_response_inv(pre));
                if pre.disk.responses[resp_id] is WriteResp {
                    assert(cache_filled_addr(pre_state.cache, resp_addr));
                    assert(cache_filled_page(post_state.cache, resp_addr)
                        == cache_filled_page(pre_state.cache, resp_addr));
                    if resp_addr == addr {
                        assert(pre_state.outstanding_cache_reqs.is_injective());
                        assert(resp_id == id);
                        assert(false);
                    } else {
                        assert(post.disk.content[resp_addr]
                            == pre.disk.content[resp_addr]);
                    }
                } else {
                    if resp_addr == addr {
                        assert(pre_state.outstanding_cache_reqs.is_injective());
                        assert(resp_id == id);
                        assert(false);
                    } else {
                        assert(post.disk.content[resp_addr]
                            == pre.disk.content[resp_addr]);
                    }
                }
            }
        }
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        if post_state.recovery_state is Begin
            || post_state.recovery_state is AwaitingSuperblock {
            assert(pre_state.recovery_state == post_state.recovery_state);
            assert(unified_cache_recovery_superblock_io_inv(pre));
            assert(post_state.outstanding_cache_reqs
                == Map::<ID, Address>::empty());
            assert(!pre_state.outstanding_cache_reqs.contains_key(id));
            assert(pre.disk.requests[id] is WriteReq);
            assert(pre_state.sync_phase is SuperblockWriteIssued);
            assert(pre_state.sync_phase is None);
            assert(false);
        }
    }
    assert(unified_cache_recovery_cache_quiescent_inv(post));
    assert(unified_cache_recovery_metadata_inv(post));
    assert(unified_cache_ready_inv(post));
    assert(unified_cache_durable_image_inv(post));
    assert(unified_cache_sync_phase_inv(post)) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        if post_state.sync_phase is SuperblockWriteIssued {
            let phase = post_state.sync_phase;
            assert(!post_state.outstanding_cache_reqs.contains_key(phase->req_id));
            if phase->req_id == id {
                assert(post.disk.responses.contains_key(phase->req_id));
                assert(post.disk.responses[phase->req_id] is WriteResp);
            } else {
                if unified_cache_superblock_write_pending(pre) {
                    assert(pre.disk.requests.contains_key(phase->req_id));
                    assert(post.disk.requests.contains_key(phase->req_id));
                    assert(post.disk.requests[phase->req_id]
                        == pre.disk.requests[phase->req_id]);
                    assert(unified_cache_superblock_write_pending(post));
                } else {
                    assert(pre.disk.responses.contains_key(phase->req_id));
                    assert(post.disk.responses.contains_key(phase->req_id));
                    assert(post.disk.responses[phase->req_id]
                        == pre.disk.responses[phase->req_id]);
                }
            }
        }
    }
    assert(unified_cache_non_cache_write_request_inv(post)) by {
        assert forall |write_id: ID| {
            &&& #[trigger] post.disk.requests.contains_key(write_id)
            &&& post.disk.requests[write_id] is WriteReq
            &&& !post_state.outstanding_cache_reqs.contains_key(write_id)
        } implies {
            let phase = post_state.sync_phase;
            &&& phase is SuperblockWriteIssued
            &&& write_id == phase->req_id
            &&& post.disk.requests[write_id]->to == spec_superblock_addr()
        } by {
            assert(write_id != id);
            assert(pre.disk.requests.contains_key(write_id));
            assert(post.disk.requests[write_id] == pre.disk.requests[write_id]);
            assert(!pre_state.outstanding_cache_reqs.contains_key(write_id));
            assert(unified_cache_non_cache_write_request_inv(pre));
        }
    }
    assert(unified_cache_superblock_write_request_inv(post)) by {
        if post_state.sync_phase is SuperblockWriteIssued && unified_cache_superblock_write_pending(post) {
            let phase = post_state.sync_phase;
            assert(phase->req_id != id) by {
                if phase->req_id == id {
                    assert(!post.disk.requests.contains_key(id));
                    assert(false);
                }
            }
            assert(unified_cache_superblock_write_pending(pre));
            assert(unified_cache_superblock_write_request_inv(pre));
            assert(post.disk.requests[phase->req_id] == pre.disk.requests[phase->req_id]);
        }
    }
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(inv(post));
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
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::disk_internal(pre, post, lbl, new_disk));
    assert(lbl is DiskInternal);
    assert(post.program == pre.program);
    assert(post.disk == new_disk);
    assert(DiskModel::next(pre.disk, new_disk, DiskLabel::Internal{}));

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |step: AsyncDisk::Step|
        AsyncDisk::State::next_by(pre.disk, new_disk, DiskLabel::Internal{}, step);
    match disk_step {
        AsyncDisk::Step::process_read(id) => {
            assert(AsyncDisk::State::next_by(
                pre.disk,
                new_disk,
                DiskLabel::Internal{},
                AsyncDisk::Step::process_read(id),
            ));
            disk_internal_process_read_refines(pre, post, lbl, new_disk, id);
        },
        AsyncDisk::Step::process_write(id) => {
            assert(AsyncDisk::State::next_by(
                pre.disk,
                new_disk,
                DiskLabel::Internal{},
                AsyncDisk::Step::process_write(id),
            ));
            disk_internal_process_write_refines(pre, post, lbl, new_disk, id);
        },
        _ => {
            assert(false);
        },
    }
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
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::crash(pre, post, lbl, new_program, new_disk));
    assert(lbl is Crash);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(post.requests == Multiset::<Request>::empty());
    assert(post.replies == Multiset::<Reply>::empty());
    assert(post.sync_requests == Multiset::<SyncReqId>::empty());
    assert(UnifiedCacheProgramModel::init(post.program));
    assert(UnifiedCacheSystem::State::init(post.program.state));
    assert(DiskModel::next(pre.disk, post.disk, DiskLabel::Crash{}));

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |step: AsyncDisk::Step|
        AsyncDisk::State::next_by(pre.disk, post.disk, DiskLabel::Crash{}, step);
    match disk_step {
        AsyncDisk::Step::crash() => {
            assert(AsyncDisk::State::crash(pre.disk, post.disk, DiskLabel::Crash{})) by {
            }
        },
        _ => {
            assert(false);
        },
    }
    assert(post.disk.content == pre.disk.content);
    assert(post.disk.requests == Map::<ID, DiskRequest>::empty());
    assert(post.disk.responses == Map::<ID, DiskResponse>::empty());
    crate::spec::AsyncDisk_t::inv_next(pre.disk, post.disk, DiskLabel::Crash{});

    reveal(UnifiedCacheSystem::State::init);
    reveal(UnifiedCacheSystem::State::init_by);


    let config = choose |config: UnifiedCacheSystem::Config|
        UnifiedCacheSystem::State::init_by(post.program.state, config);
    match config {
        UnifiedCacheSystem::Config::initialize(cache_slots, free_aus) => {
            assert(UnifiedCacheSystem::State::initialize(
                post.program.state,
                cache_slots,
                free_aus,
            )) by {
            }
        },
        UnifiedCacheSystem::Config::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }

    let src = unified_cache_system_i(pre);
    let dst = unified_cache_system_i(post);
    let target_lbl = unified_cache_system_i_lbl(pre, post, lbl);
    let keep_in_flight = src.superblockstore.landed;
    assert(target_lbl == CrashAwareCachingDiskSystem::Label::Crash);

    assert(src.inv());
    assert(keep_in_flight == src.superblockstore.landed);
    assert(src.superblockstore.inv());
    assert(dst.superblockstore.in_flight is None);
    assert(!dst.superblockstore.landed);
    assert(SuperblockStore::State::next(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Crash,
    )) by {
        assert(SuperblockStore::State::crash(
            src.superblockstore,
            dst.superblockstore,
            SuperblockStore::Label::Crash,
        )) by {
        }
        assert(SuperblockStore::State::next_by(
            src.superblockstore,
            dst.superblockstore,
            SuperblockStore::Label::Crash,
            SuperblockStore::Step::crash(),
        )) by {
            reveal(SuperblockStore::State::next_by);
        }
        reveal(SuperblockStore::State::next);
    }

    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let journal_pre = UnifiedCacheJournalRefinement::unified_cache_journal_source(pre);
    let journal_post = UnifiedCacheJournalRefinement::unified_cache_journal_source(post);
    let branch_pre = UnifiedCacheBranchRefinement::unified_cache_branch_source(pre);
    let branch_post = UnifiedCacheBranchRefinement::unified_cache_branch_source(post);
    let journal_crash_image = if keep_in_flight {
        CachingDiskJournalImage::materialized_from_loaded_index(
            src.journal.ephemeral->v,
            src.journal.frozen.unwrap(),
        )
    } else if src.journal.ephemeral is Unknown {
        src.journal.persistent->image
    } else {
        CachingDiskJournalImage::materialized_from_loaded_index(
            src.journal.ephemeral->v,
            src.journal.persistent.metadata(),
        )
    };
    let branch_crash_image = if keep_in_flight && src.branch.ephemeral is Known {
        CachingDiskBranchImage::materialized_from_persistent(
            src.branch.ephemeral->v,
            src.branch.frozen.unwrap(),
        )
    } else if src.branch.ephemeral is Unknown {
        src.branch.persistent->image
    } else {
        CachingDiskBranchImage::materialized_from_persistent(
            src.branch.ephemeral->v,
            src.branch.persistent.metadata(),
        )
    };

    assert(src.journal == journal_pre.i());
    assert(dst.journal == journal_post.i());
    assert(src.branch == branch_pre.i());
    assert(dst.branch == branch_post.i());
    assert(journal_post.persistent_image is None);
    assert(branch_post.persistent_image is None);
    assert(journal_post.disk.content == journal_pre.disk.content);
    assert(branch_post.disk.content == branch_pre.disk.content);

    assert(dst.journal.persistent == PersistentCachingDiskJournal::Image{
        image: journal_crash_image,
    }) by {
        if keep_in_flight {
            assert(unified_cache_superblock_image_inv(pre));
            assert(parse_abstract_superblock(pre.disk.content[spec_superblock_addr()])
                == pre_state.atomic_inflight_superblock_i());
            assert(journal_post.persistent_superblock_image_i()
                == pre_state.atomic_inflight_superblock_i()) by {
                assert(post.disk.content == pre.disk.content);
                assert(journal_post.persistent_image is None);
                assert(UnifiedCacheJournalRefinement::async_disk_superblock_raw_i(post.disk.content)
                    == post.disk.content[spec_superblock_addr()]);
            }
            assert(journal_pre.in_flight_image is Some);
            assert(journal_pre.in_flight_image.unwrap()
                == pre_state.atomic_inflight_superblock_i());
            assert(pre_state.atomic_inflight_superblock_i().wf()) by {
                assert(journal_pre.in_flight_image.unwrap().wf());
            }
            assert(journal_pre.superblock_loaded());
            assert(journal_pre.journal.ready());
            assert(journal_pre.i().refinement_inv()) by {
                assert(journal_pre.semantic_inv());
            }
            assert(journal_post.journal == AtomicJournalState::State::empty());
            journal_pre.post_crash_persistent_image_matches_materialized(
                journal_post,
                pre_state.atomic_inflight_superblock_i(),
                src.journal.frozen.unwrap(),
            );
            assert(journal_post.persistent_journal_image_i() == journal_crash_image);
        } else if src.journal.ephemeral is Unknown {
            assert(!journal_pre.superblock_loaded());
            assert(journal_pre.persistent_superblock_image_i()
                == journal_post.persistent_superblock_image_i()) by {
                assert(post.disk.content == pre.disk.content);
                assert(UnifiedCacheJournalRefinement::async_disk_superblock_raw_i(post.disk.content)
                    == UnifiedCacheJournalRefinement::async_disk_superblock_raw_i(pre.disk.content));
            }
            assert(journal_post.persistent_journal_image_i()
                == journal_pre.persistent_journal_image_i()) by {
                let image = journal_pre.persistent_superblock_image_i();
                assert(journal_post.persistent_superblock_image_i() == image);
                assert_maps_equal!(
                    journal_post.persistent_journal_image_i().persistent,
                    journal_pre.persistent_journal_image_i().persistent,
                    addr => {}
                );
            }
        } else {
            assert(journal_pre.superblock_loaded());
            assert(unified_cache_superblock_image_inv(pre));
            assert(journal_post.persistent_superblock_image_i()
                == journal_pre.persistent_superblock_image_i()) by {
                assert(post.disk.content == pre.disk.content);
                assert(parse_abstract_superblock(pre.disk.content[spec_superblock_addr()])
                    == pre_state.persistent_image.unwrap());
                assert(journal_pre.persistent_image == pre_state.persistent_image);
                assert(journal_post.persistent_image is None);
                assert(UnifiedCacheJournalRefinement::async_disk_superblock_raw_i(post.disk.content)
                    == post.disk.content[spec_superblock_addr()]);
            }
            assert(journal_pre.persistent_superblock_image_i().wf());
            assert(journal_pre.i().refinement_inv()) by {
                assert(journal_pre.semantic_inv());
            }
            assert(journal_post.journal == AtomicJournalState::State::empty());
            if journal_pre.journal.ready() {
                journal_pre.post_crash_persistent_image_matches_materialized(
                    journal_post,
                    journal_pre.persistent_superblock_image_i(),
                    src.journal.persistent.metadata(),
                );
            } else {
                let image = journal_pre.persistent_superblock_image_i();
                assert(journal_pre.journal.journal.status is None);
                assert(src.journal.persistent.metadata()
                    == journal_pre.persistent_journal_image_i().metadata());
                journal_pre.unloaded_post_crash_persistent_image_matches_materialized(
                    journal_post,
                    image,
                    src.journal.persistent.metadata(),
                );
            }
            assert(journal_post.persistent_journal_image_i() == journal_crash_image);
        }
    }

    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight},
    )) by {
        assert(CrashAwareCachingDiskJournal::State::crash(
            src.journal,
            dst.journal,
            CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight},
        )) by {
        }
        assert(CrashAwareCachingDiskJournal::State::next_by(
            src.journal,
            dst.journal,
            CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight},
            CrashAwareCachingDiskJournal::Step::crash(),
        )) by {
            reveal(CrashAwareCachingDiskJournal::State::next_by);
        }
        reveal(CrashAwareCachingDiskJournal::State::next);
    }

    assert({
        &&& dst.branch.persistent == PersistentCachingDiskBranch::Image{
            image: branch_crash_image,
        }
        &&& branch_post.persistent_branch_image_i().loadable()
        &&& branch_post.persistent_branch_image_i().stack_wf()
    }) by {
        if keep_in_flight {
            assert(unified_cache_superblock_image_inv(pre));
            assert(parse_abstract_superblock(pre.disk.content[spec_superblock_addr()])
                == pre_state.atomic_inflight_superblock_i());
            assert(branch_post.persistent_superblock_image_i()
                == pre_state.atomic_inflight_superblock_i()) by {
                assert(post.disk.content == pre.disk.content);
                assert(branch_post.persistent_image is None);
                assert(UnifiedCacheBranchRefinement::async_disk_superblock_raw_i(post.disk.content)
                    == post.disk.content[spec_superblock_addr()]);
            }
            assert(branch_pre.in_flight_image is Some);
            assert(branch_pre.in_flight_image.unwrap()
                == pre_state.atomic_inflight_superblock_i());
            assert(pre_state.atomic_inflight_superblock_i().wf()) by {
                assert(branch_pre.in_flight_image.unwrap().wf());
            }
            assert(branch_pre.superblock_loaded());
            assert(branch_pre.i().refinement_inv()) by {
                assert(branch_pre.semantic_inv());
            }
            assert(branch_pre.branch.metadata_loaded()) by {
                assert(src.branch.prepared);
                assert(src.branch.frozen is Some);
                assert(branch_pre.branch.prepared);
                assert(pre_state.sync_phase is SuperblockWriteIssued);
                assert(pre_state.recovery_state is RecoveryComplete) by {
                    assert(unified_cache_recovery_metadata_inv(pre));
                    if !(pre_state.recovery_state is RecoveryComplete) {
                        assert(pre_state.sync_phase is None);
                        assert(false);
                    }
                }
                assert(unified_cache_ready_inv(pre));
                assert(pre_state.branch.metadata_loaded());
            }
            let image = pre_state.atomic_inflight_superblock_i();
            let frozen = src.branch.frozen.unwrap();
            assert(frozen.sealed_roots == image.branch_roots) by {
                assert(src.branch.frozen == branch_pre.frozen_branch_metadata_i());
                assert(branch_pre.branch.in_flight is Some);
                assert(branch_pre.branch.in_flight.unwrap().sealed_roots == image.branch_roots);
            }
            assert(frozen.seq_end == image.branch_seq_end) by {
                assert(src.branch.frozen == branch_pre.frozen_branch_metadata_i());
                assert(branch_pre.branch.in_flight is Some);
                assert(branch_pre.branch.in_flight.unwrap().seq_end == image.branch_seq_end);
            }
            assert(CachingDiskBranch::State::next(
                branch_pre.branch_caching_disk_state_i(),
                branch_pre.branch_caching_disk_state_i(),
                CachingDiskBranch::Label::FreezePrepared{image: frozen},
            )) by {
                assert(frozen.sealed_roots.len()
                    <= branch_pre.branch_caching_disk_state_i().persisted_root_count) by {
                    assert(src.branch.prepared);
                    assert(src.branch.inv());
                    assert(src.branch.ephemeral is Known);
                    assert(src.branch.ephemeral->v == branch_pre.branch_caching_disk_state_i());
                }
                assert(branch_pre.branch_caching_disk_state_i().sealed_roots.subrange(
                    0,
                    frozen.sealed_roots.len() as int,
                ) == frozen.sealed_roots) by {
                    assert(src.branch.inv());
                }
                assert(CachingDiskBranch::State::freeze_prepared(
                    branch_pre.branch_caching_disk_state_i(),
                    branch_pre.branch_caching_disk_state_i(),
                    CachingDiskBranch::Label::FreezePrepared{image: frozen},
                )) by {
                }
                assert(CachingDiskBranch::State::next_by(
                    branch_pre.branch_caching_disk_state_i(),
                    branch_pre.branch_caching_disk_state_i(),
                    CachingDiskBranch::Label::FreezePrepared{image: frozen},
                    CachingDiskBranch::Step::freeze_prepared(),
                )) by {
                    reveal(CachingDiskBranch::State::next_by);
                }
                reveal(CachingDiskBranch::State::next);
            }
            assert(branch_post.branch == AtomicBranchState::State::empty());
            branch_pre.post_crash_persistent_image_matches_materialized(
                branch_post,
                image,
                frozen,
            );
            assert(branch_post.persistent_branch_image_i() == branch_crash_image);
        } else if src.branch.ephemeral is Unknown {
            assert(!branch_pre.superblock_loaded());
            assert(branch_pre.persistent_superblock_image_i()
                == branch_post.persistent_superblock_image_i()) by {
                assert(post.disk.content == pre.disk.content);
                assert(UnifiedCacheBranchRefinement::async_disk_superblock_raw_i(post.disk.content)
                    == UnifiedCacheBranchRefinement::async_disk_superblock_raw_i(pre.disk.content));
            }
            assert(branch_post.persistent_branch_image_i()
                == branch_pre.persistent_branch_image_i()) by {
                let image = branch_pre.persistent_superblock_image_i();
                assert(branch_post.persistent_superblock_image_i() == image);
                assert_maps_equal!(
                    branch_post.persistent_branch_image_i().persistent,
                    branch_pre.persistent_branch_image_i().persistent,
                    addr => {}
                );
            }
            assert(branch_post.persistent_branch_image_i().loadable()) by {
                assert(branch_pre.persistent_image is None);
                assert(pre_state.persistent_image is None);
                assert(pre_state.recovery_state is Begin
                    || pre_state.recovery_state is AwaitingSuperblock) by {
                    assert(unified_cache_recovery_metadata_inv(pre));
                    match pre_state.recovery_state {
                        RecoveryState::Begin => {},
                        RecoveryState::AwaitingSuperblock => {},
                        RecoveryState::SuperblockAvailable => { assert(false); },
                        RecoveryState::MetadataLoadComplete => { assert(false); },
                        RecoveryState::RecoveryComplete => {
                            assert(unified_cache_ready_inv(pre));
                            assert(pre_state.persistent_image is Some);
                            assert(false);
                        },
                    }
                }
                assert(unified_cache_recovery_superblock_io_inv(pre));
            }
            assert(branch_post.persistent_branch_image_i().stack_wf()) by {
                assert(branch_pre.persistent_image is None);
                assert(pre_state.persistent_image is None);
                assert(pre_state.recovery_state is Begin
                    || pre_state.recovery_state is AwaitingSuperblock) by {
                    assert(unified_cache_recovery_metadata_inv(pre));
                    match pre_state.recovery_state {
                        RecoveryState::Begin => {},
                        RecoveryState::AwaitingSuperblock => {},
                        RecoveryState::SuperblockAvailable => { assert(false); },
                        RecoveryState::MetadataLoadComplete => { assert(false); },
                        RecoveryState::RecoveryComplete => {
                            assert(unified_cache_ready_inv(pre));
                            assert(pre_state.persistent_image is Some);
                            assert(false);
                        },
                    }
                }
                assert(unified_cache_recovery_superblock_io_inv(pre));
            }
        } else {
            assert(branch_pre.superblock_loaded());
            assert(unified_cache_superblock_image_inv(pre));
            assert(branch_post.persistent_superblock_image_i()
                == branch_pre.persistent_superblock_image_i()) by {
                assert(post.disk.content == pre.disk.content);
                assert(parse_abstract_superblock(pre.disk.content[spec_superblock_addr()])
                    == pre_state.persistent_image.unwrap());
                assert(branch_pre.persistent_image == pre_state.persistent_image);
                assert(branch_post.persistent_image is None);
                assert(UnifiedCacheBranchRefinement::async_disk_superblock_raw_i(post.disk.content)
                    == post.disk.content[spec_superblock_addr()]);
            }
            assert(branch_pre.persistent_superblock_image_i().wf());
            assert(branch_pre.i().refinement_inv()) by {
                assert(branch_pre.semantic_inv());
            }
            let image = branch_pre.persistent_superblock_image_i();
            let frozen = src.branch.persistent.metadata();
            assert(frozen.sealed_roots == image.branch_roots) by {
                assert(src.branch.persistent == branch_pre.persistent_branch_i());
                assert(branch_pre.persistent_branch_i() == PersistentCachingDiskBranch::Metadata{
                    meta: branch_pre.persistent_branch_image_i().metadata(),
                });
            }
            assert(frozen.seq_end == image.branch_seq_end) by {
                assert(src.branch.persistent == branch_pre.persistent_branch_i());
                assert(branch_pre.persistent_branch_i() == PersistentCachingDiskBranch::Metadata{
                    meta: branch_pre.persistent_branch_image_i().metadata(),
                });
            }
            assert(CachingDiskBranch::State::next(
                branch_pre.branch_caching_disk_state_i(),
                branch_pre.branch_caching_disk_state_i(),
                CachingDiskBranch::Label::FreezePrepared{image: frozen},
            )) by {
                assert(frozen.sealed_roots.len()
                    <= branch_pre.branch_caching_disk_state_i().persisted_root_count) by {
                    assert(branch_pre.branch.wf());
                    assert(branch_pre.branch.persistent_image.sealed_roots == image.branch_roots);
                }
                assert(branch_pre.branch_caching_disk_state_i().sealed_roots.subrange(
                    0,
                    frozen.sealed_roots.len() as int,
                ) == frozen.sealed_roots) by {
                    assert(branch_pre.branch.wf());
                    assert(branch_pre.branch.persistent_image.sealed_roots == image.branch_roots);
                    assert(branch_pre.branch.image.sealed_roots.take(
                        branch_pre.branch.persistent_image.sealed_roots.len() as int,
                    ) == branch_pre.branch.persistent_image.sealed_roots);
                }
                assert(CachingDiskBranch::State::freeze_prepared(
                    branch_pre.branch_caching_disk_state_i(),
                    branch_pre.branch_caching_disk_state_i(),
                    CachingDiskBranch::Label::FreezePrepared{image: frozen},
                )) by {
                }
                assert(CachingDiskBranch::State::next_by(
                    branch_pre.branch_caching_disk_state_i(),
                    branch_pre.branch_caching_disk_state_i(),
                    CachingDiskBranch::Label::FreezePrepared{image: frozen},
                    CachingDiskBranch::Step::freeze_prepared(),
                )) by {
                    reveal(CachingDiskBranch::State::next_by);
                }
                reveal(CachingDiskBranch::State::next);
            }
            assert(branch_post.branch == AtomicBranchState::State::empty());
            branch_pre.post_crash_persistent_image_matches_materialized(
                branch_post,
                image,
                frozen,
            );
            assert(branch_post.persistent_branch_image_i() == branch_crash_image);
        }
    }

    assert(CrashAwareCachingDiskBranch::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight},
    )) by {
        assert(CrashAwareCachingDiskBranch::State::crash(
            src.branch,
            dst.branch,
            CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight},
        )) by {
        }
        assert(CrashAwareCachingDiskBranch::State::next_by(
            src.branch,
            dst.branch,
            CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight},
            CrashAwareCachingDiskBranch::Step::crash(),
        )) by {
            reveal(CrashAwareCachingDiskBranch::State::next_by);
        }
        reveal(CrashAwareCachingDiskBranch::State::next);
    }
    src.journal.next_refines(
        dst.journal,
        CrashAwareCachingDiskJournal::Label::Crash{keep_in_flight},
    );
    src.branch.next_refines(
        dst.branch,
        CrashAwareCachingDiskBranch::Label::Crash{keep_in_flight},
    );

    match config {
        UnifiedCacheSystem::Config::initialize(cache_slots, free_aus) => {
            assert(Cache::State::initialize(post_state.cache, cache_slots)) by {
            }
            Cache::State::initialize_inductive(post_state.cache, cache_slots);
            assert(post_state.cache.inv());
            assert(journal_post.cache.inv());
            assert(branch_post.cache.inv());
        },
        UnifiedCacheSystem::Config::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }
    assert(UnifiedCacheJournalRefinement::inv(journal_post)) by {
        assert(journal_post.inv()) by {
            assert(journal_post.journal.wf());
            assert(UnifiedCacheJournalRefinement::async_disk_superblock_page_wf(
                post.disk.content,
            ));
            assert(journal_post.persistent_superblock_image_i().wf());
            assert(journal_post.cache.inv());
            assert(journal_post.disk.inv());
            assert(journal_post.cache.lookup_map == Map::<Address, Slot>::empty()) by {
                assert(journal_post.cache == post_state.cache);
                assert(post_state.cache.lookup_map == Map::<Address, Slot>::empty());
            }
            assert forall |addr: Address| #[trigger] filled_cache_status(journal_post.cache).contains_key(addr)
                && filled_cache_status(journal_post.cache)[addr] == PageStatus::Clean
                && addresses_in_aus(journal_post.journal_projection_aus()).contains(addr)
                implies {
                    &&& journal_post.disk.content.contains_key(addr)
                    &&& journal_post.disk.content[addr] == cache_filled_page(journal_post.cache, addr)
                } by {
                assert(cache_filled_addr(journal_post.cache, addr));
                assert(journal_post.cache.lookup_map.contains_key(addr));
                assert(false);
            }
            caching_disk_i_inv_from_clean_cache_coupling(
                journal_post.cache,
                journal_post.disk,
                journal_post.journal_projection_aus(),
            );
            assert(journal_post.journal_caching_disk_i().inv());
            assert(!journal_post.superblock_loaded());
            assert(journal_post.journal == AtomicJournalState::State::empty());
            assert(journal_post.in_flight is None);
            assert(journal_post.in_flight_image is None);
        }
        assert(journal_post.semantic_inv()) by {
            assert(journal_post.i() == dst.journal);
            assert(dst.journal.refinement_inv());
        }
    }
    assert(UnifiedCacheBranchRefinement::inv(branch_post)) by {
        assert(branch_post.inv()) by {
            assert(branch_post.branch.wf()) by {
                assert(branch_post.branch == AtomicBranchState::State::empty());
                assert(branch_post.branch.image.sealed_roots == Seq::<Address>::empty());
                assert(branch_post.branch.persistent_image.sealed_roots == Seq::<Address>::empty());
                assert(branch_post.branch.image.sealed_roots.take(
                    branch_post.branch.persistent_image.sealed_roots.len() as int,
                ) == branch_post.branch.persistent_image.sealed_roots);
            }
            assert(UnifiedCacheBranchRefinement::async_disk_superblock_page_wf(
                post.disk.content,
            ));
            assert(branch_post.persistent_superblock_image_i().wf());
            assert(branch_post.cache.inv());
            assert(branch_post.disk.inv());
            assert(branch_post.cache.lookup_map == Map::<Address, Slot>::empty()) by {
                assert(branch_post.cache == post_state.cache);
                assert(post_state.cache.lookup_map == Map::<Address, Slot>::empty());
            }
            assert forall |addr: Address| #[trigger] filled_cache_status(branch_post.cache).contains_key(addr)
                && filled_cache_status(branch_post.cache)[addr] == PageStatus::Clean
                && addresses_in_aus(branch_post.branch_projection_aus()).contains(addr)
                implies {
                    &&& branch_post.disk.content.contains_key(addr)
                    &&& branch_post.disk.content[addr] == cache_filled_page(branch_post.cache, addr)
                } by {
                assert(cache_filled_addr(branch_post.cache, addr));
                assert(branch_post.cache.lookup_map.contains_key(addr));
                assert(false);
            }
            caching_disk_i_inv_from_clean_cache_coupling(
                branch_post.cache,
                branch_post.disk,
                branch_post.branch_projection_aus(),
            );
            assert(branch_post.branch_caching_disk_i().inv());
            assert(!branch_post.superblock_loaded());
            assert(branch_post.branch == AtomicBranchState::State::empty());
            assert(branch_post.in_flight is None);
            assert(branch_post.in_flight_image is None);
        }
        assert(branch_post.semantic_inv()) by {
            assert(branch_post.i() == dst.branch);
            assert(dst.branch.refinement_inv());
        }
    }
    assert(unified_cache_recovery_superblock_io_inv(post)) by {
        assert(post_state.recovery_state is Begin);
        assert(post_state.persistent_image is None);
        assert(post_state.sync_phase is None);
        assert(post_state.sync_req_map == Map::<SyncReqId, nat>::empty());
        assert(post_state.outstanding_cache_reqs == Map::<ID, Address>::empty());
        assert(post.disk.requests == Map::<ID, DiskRequest>::empty());
        assert(post.disk.responses == Map::<ID, DiskResponse>::empty());
        assert(post_state.cache.lookup_map == Map::<Address, Slot>::empty()) by {
            match config {
                UnifiedCacheSystem::Config::initialize(cache_slots, free_aus) => {
                    assert(Cache::State::initialize(post_state.cache, cache_slots)) by {
                    }
                },
                UnifiedCacheSystem::Config::dummy_to_use_type_params(_) => {
                    assert(false);
                },
            }
        }
        assert(journal_post.journal_caching_disk_i().cache
            == Map::<Address, RawPage>::empty()) by {
            assert_maps_equal!(
                journal_post.journal_caching_disk_i().cache,
                Map::<Address, RawPage>::empty(),
                addr => {
                    if journal_post.journal_caching_disk_i().cache.contains_key(addr) {
                        assert(filled_cache_pages(post_state.cache).contains_key(addr));
                        assert(cache_filled_addr(post_state.cache, addr));
                        assert(post_state.cache.lookup_map.contains_key(addr));
                        assert(false);
                    }
                }
            );
        }
        assert(journal_post.journal_caching_disk_i().status
            == Map::<Address, PageStatus>::empty()) by {
            assert_maps_equal!(
                journal_post.journal_caching_disk_i().status,
                Map::<Address, PageStatus>::empty(),
                addr => {
                    if journal_post.journal_caching_disk_i().status.contains_key(addr) {
                        assert(filled_cache_status(post_state.cache).contains_key(addr));
                        assert(cache_filled_addr(post_state.cache, addr));
                        assert(post_state.cache.lookup_map.contains_key(addr));
                        assert(false);
                    }
                }
            );
        }
        assert(branch_post.branch_caching_disk_i().cache
            == Map::<Address, RawPage>::empty()) by {
            assert_maps_equal!(
                branch_post.branch_caching_disk_i().cache,
                Map::<Address, RawPage>::empty(),
                addr => {
                    if branch_post.branch_caching_disk_i().cache.contains_key(addr) {
                        assert(filled_cache_pages(post_state.cache).contains_key(addr));
                        assert(cache_filled_addr(post_state.cache, addr));
                        assert(post_state.cache.lookup_map.contains_key(addr));
                        assert(false);
                    }
                }
            );
        }
        assert(branch_post.branch_caching_disk_i().status
            == Map::<Address, PageStatus>::empty()) by {
            assert_maps_equal!(
                branch_post.branch_caching_disk_i().status,
                Map::<Address, PageStatus>::empty(),
                addr => {
                    if branch_post.branch_caching_disk_i().status.contains_key(addr) {
                        assert(filled_cache_status(post_state.cache).contains_key(addr));
                        assert(cache_filled_addr(post_state.cache, addr));
                        assert(post_state.cache.lookup_map.contains_key(addr));
                        assert(false);
                    }
                }
            );
        }
        let branch_image_aus =
            UnifiedCacheBranchRefinement::UnifiedCacheBranchSource::branch_image_summary_aus_i(
                post.disk.content,
                branch_post.persistent_superblock_image_i().branch_roots,
            );
        assert(project_cache_pages(post_state.cache, branch_image_aus)
            == Map::<Address, RawPage>::empty()) by {
            assert_maps_equal!(
                project_cache_pages(post_state.cache, branch_image_aus),
                Map::<Address, RawPage>::empty(),
                addr => {
                    if project_cache_pages(post_state.cache, branch_image_aus).contains_key(addr) {
                        assert(filled_cache_pages(post_state.cache).contains_key(addr));
                        assert(cache_filled_addr(post_state.cache, addr));
                        assert(post_state.cache.lookup_map.contains_key(addr));
                        assert(false);
                    }
                }
            );
        }
        assert(project_cache_status(post_state.cache, branch_image_aus)
            == Map::<Address, PageStatus>::empty()) by {
            assert_maps_equal!(
                project_cache_status(post_state.cache, branch_image_aus),
                Map::<Address, PageStatus>::empty(),
                addr => {
                    if project_cache_status(post_state.cache, branch_image_aus).contains_key(addr) {
                        assert(filled_cache_status(post_state.cache).contains_key(addr));
                        assert(cache_filled_addr(post_state.cache, addr));
                        assert(post_state.cache.lookup_map.contains_key(addr));
                        assert(false);
                    }
                }
            );
        }
        assert(branch_post.persistent_branch_image_i().loadable());
        assert(branch_post.persistent_branch_image_i().stack_wf());
    }

    assert(dst.free_aus == post.program.state.free_aus);
    assert(CrashAwareCachingDiskSystem::State::reserved_aus()
        == UnifiedCacheSystem::State::reserved_aus());
    assert(dst.free_aus - CrashAwareCachingDiskSystem::State::reserved_aus()
        =~= dst.free_aus) by {
        assert(post.program.state.free_aus.disjoint(UnifiedCacheSystem::State::reserved_aus()));
    }
    assert(dst.progress == crate::spec::MapSpec_t::AsyncMap::State::init_ephemeral_state()) by {
        assert(dst.progress == unified_cache_progress_i(
            Multiset::<Request>::empty(),
            Multiset::<Reply>::empty(),
        ));
        assert(system_multiset_to_set_i(Multiset::<Request>::empty()) == Set::<Request>::empty()) by {
            assert forall |req: Request| #[trigger] system_multiset_to_set_i(
                Multiset::<Request>::empty(),
            ).contains(req) <==> Set::<Request>::empty().contains(req) by {}
        }
        assert(system_multiset_to_set_i(Multiset::<Reply>::empty()) == Set::<Reply>::empty()) by {
            assert forall |reply: Reply| #[trigger] system_multiset_to_set_i(
                Multiset::<Reply>::empty(),
            ).contains(reply) <==> Set::<Reply>::empty().contains(reply) by {}
        }
    }
    assert(dst.sync_reqs == Map::<SyncReqId, LSN>::empty());

    assert(CrashAwareCachingDiskSystem::State::crash(
        src,
        dst,
        target_lbl,
        dst.journal,
        dst.branch,
        dst.superblockstore,
        dst.free_aus,
        keep_in_flight,
    )) by {
    }
    assert(CrashAwareCachingDiskSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskSystem::Step::crash(
            dst.journal,
            dst.branch,
            dst.superblockstore,
            dst.free_aus,
            keep_in_flight,
        ),
    )) by {
        reveal(CrashAwareCachingDiskSystem::State::next_by);
    }
    reveal(CrashAwareCachingDiskSystem::State::next);
    assert(CrashAwareCachingDiskSystem::State::next(src, dst, target_lbl));
    system_i_inv_next(pre, post, target_lbl);
    assert(unified_cache_system_i(post).inv());
    assert(inv(post));
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
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::noop(pre, post, lbl));
    assert(lbl is Noop);
    assert(post == pre);
    assert(unified_cache_system_i_lbl(pre, post, lbl) == CrashAwareCachingDiskSystem::Label::Noop);
    assert(unified_cache_system_i(post) == unified_cache_system_i(pre));
    assert(unified_cache_system_i(pre).inv());
    system_i_noop_next(pre, post, lbl);
    assert(inv(post));
}

pub proof fn dummy_to_use_type_params_refines(
    pre: SystemModel::State<UnifiedCacheProgramModel>,
    post: SystemModel::State<UnifiedCacheProgramModel>,
    lbl: SystemModel::Label,
    dummy: SystemModel::State<UnifiedCacheProgramModel>,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::dummy_to_use_type_params(dummy),
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
    assert(false);
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
        SystemModel::Step::dummy_to_use_type_params(dummy) => {
            dummy_to_use_type_params_refines(pre, post, lbl, dummy);
        },
    }
}

} // verus!
