// Copyright 2018-2024 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, University of Washington
// SPDX-License-Identifier: BSD-2-Clause
//
// Outer interpretation from the Betree-backed unified-cache program to the
// crash-aware caching-disk Betree coordination system.

#![allow(unused_imports)]
#![allow(unused_variables)]

use vstd::prelude::*;
use vstd::multiset::Multiset;
use vstd::assert_maps_equal;
use vstd::assert_sets_equal;

use crate::implementation::CrashAwareCachingDiskBetreeSystem_v::
    CrashAwareCachingDiskBetreeSystem;
use crate::implementation::AbstractSuperblock_v::{
    abstract_superblock_raw_wf, AbstractSuperblockImage,
    parse_abstract_superblock, superblock_matches,
    superblock_matches_image_wf,
};
use crate::implementation::CrashAwareCachingDiskBetreeSystemRefinement_v as
    CrashAwareCachingDiskBetreeSystemRefinement;
use crate::implementation::AtomicBranchBetreeState_v::
    AtomicBranchBetreeState;
use crate::implementation::AtomicJournalState_v::AtomicJournalState;
use crate::implementation::CachedBranchBetree_v::{
    cached_branch_alloc_aus, CachedBranchBetree, LoadedBetreePath,
    LoadedBetreeQueryReceipt,
};
use crate::implementation::CachingDiskBranchBetree_v::{
    CachingDiskBranchBetree, PageAccess,
};
use crate::implementation::CrashAwareCachingDiskBranchBetree_v::
    {BetreeMetadataRecoveryLabel, CachingDiskBranchBetreeImage,
        CrashAwareCachingDiskBranchBetree};
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    CachingDiskJournalImage, CrashAwareCachingDiskJournal,
    PersistentCachingDiskJournal,
};
use crate::implementation::SuperblockStore_v::
    SuperblockStore;
use crate::implementation::Cache_v::{
    Cache, Entry, Slot, Status,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_filled_addr, cache_filled_page, cache_status_i,
    cache_disk_ops_begin_preserves_filled_page,
    cache_disk_ops_end_preserves_filled_page,
    cache_internal_post_filled_addr_was_pre_filled,
    cache_internal_preserves_empty_projection,
    cache_internal_preserves_clean_filled_addr,
    cache_internal_preserves_protected_entries,
    caching_disk_i_domains_wf_from_sources,
    caching_disk_i_inv_from_clean_cache_coupling,
    async_disk_process_write_refines_projected_internal,
    async_disk_process_write_preserves_readable,
    disk_has_pending_id, filled_cache_pages, filled_cache_status,
    outstanding_cache_io_wf,
    project_persistent,
};
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, CachingDisk, PageStatus,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::to_journal_records;
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::implementation::MultisetMapRelation_v::{
    multiset_map_singleton, multiset_map_singleton_ensures,
    multiset_to_map,
};
use crate::betree::LinkedBetree_v::{
    PathAddrs, SplitAddrs, TwoAddrs,
};
use crate::betree::SplitRequest_v::SplitRequest;
use crate::disk::GenericDisk_v::Address;
use crate::implementation::UnifiedCacheBetreeProgramModel_v::
    UnifiedCacheBetreeProgramModel;
use crate::implementation::UnifiedCacheBetreeSystem_v::{
    betree_metadata_from_superblock, betree_superblock_image_wf,
    AtomicBetreeSyncPhase, UnifiedCacheBetreeSystem,
};
use crate::implementation::UnifiedCacheBranchBetreeRefinement_v as
    UnifiedCacheBranchBetreeRefinement;
use crate::implementation::UnifiedCacheJournalRefinement_v as
    UnifiedCacheJournalRefinement;
use crate::spec::MapSpec_t::{
    EphemeralState, ID, Input, Reply, Request,
};
use crate::abstract_system::MsgHistory_v::{
    KeyedMessage, MsgHistory,
};
use crate::spec::Messages_t::Message;
use crate::spec::AsyncDisk_t::{
    AsyncDisk, DiskRequest, DiskResponse, RawPage,
};
use crate::trusted::ProgramModelTrait_t::{
    DiskLabel, DiskModel, ProgramLabel, ProgramModelTrait,
    ProgramUserOp,
};
use crate::trusted::SystemModel_t::SystemModel;

verus! {

pub closed spec fn system_multiset_to_set_i<V>(
    m: Multiset<V>,
) -> Set<V> {
    Set::new(|v| m.contains(v))
}

pub open spec fn unified_cache_betree_progress_i(
    requests: Multiset<Request>,
    replies: Multiset<Reply>,
) -> EphemeralState {
    EphemeralState {
        requests: system_multiset_to_set_i(requests),
        replies: system_multiset_to_set_i(replies),
    }
}

pub open spec fn unified_cache_betree_journal_source(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> UnifiedCacheJournalRefinement::UnifiedCacheJournalSource {
    let state = model.program.state;
    UnifiedCacheJournalRefinement::UnifiedCacheJournalSource {
        journal: state.journal,
        cache: state.cache,
        disk: model.disk,
        persistent_image: state.persistent_image,
        in_flight: state.sync_phase.image(),
        in_flight_image: state.sync_phase.image(),
        publish_prepared:
            state.sync_phase is SuperblockWriteIssued,
    }
}

pub closed spec fn unified_cache_betree_superblock_write_pending(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let req_id = model.program.state.sync_phase.req_id();
    &&& req_id is Some
    &&& model.disk.requests.contains_key(req_id.unwrap())
    &&& model.disk.requests[req_id.unwrap()] is WriteReq
    &&& model.disk.requests[req_id.unwrap()]->to
        == spec_superblock_addr()
}

pub closed spec fn unified_cache_betree_superblock_landed(
    state: UnifiedCacheBetreeSystem::State,
    disk:
        crate::trusted::ProgramModelTrait_t::DiskModel,
) -> bool {
    let req_id = state.sync_phase.req_id();
    &&& req_id is Some
    &&& disk.responses.contains_key(req_id.unwrap())
}

pub open spec fn unified_cache_betree_superblockstore_i(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> SuperblockStore::State {
    let persistent =
        if model.disk.content.contains_key(spec_superblock_addr()) {
            model.disk.content[spec_superblock_addr()]
        } else {
            arbitrary()
        };
    let landed = unified_cache_betree_superblock_landed(
        model.program.state,
        model.disk,
    );
    let req_id = model.program.state.sync_phase.req_id();
    let pending_raw =
        if unified_cache_betree_superblock_write_pending(model) {
            model.disk.requests[req_id.unwrap()]->data
        } else {
            arbitrary()
        };
    SuperblockStore::State {
        persistent,
        in_flight:
            if unified_cache_betree_superblock_write_pending(model)
                && !landed
            {
                Some(pending_raw)
            } else {
                None
            },
        landed,
    }
}

pub open spec fn unified_cache_betree_system_i(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> CrashAwareCachingDiskBetreeSystem::State {
    CrashAwareCachingDiskBetreeSystem::State {
        journal:
            UnifiedCacheJournalRefinement::unified_cache_journal_i(
                unified_cache_betree_journal_source(model),
            ),
        branch:
            UnifiedCacheBranchBetreeRefinement::
                unified_cache_branch_betree_i(
                    UnifiedCacheBranchBetreeRefinement::
                        unified_cache_branch_betree_source(model),
                ),
        progress: unified_cache_betree_progress_i(
            model.requests,
            model.replies,
        ),
        sync_reqs: model.program.state.sync_req_map,
        superblockstore:
            unified_cache_betree_superblockstore_i(model),
        free_aus: model.program.state.free_aus,
    }
}

pub open spec fn unified_cache_betree_system_i_lbl(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
) -> CrashAwareCachingDiskBetreeSystem::Label {
    match lbl {
        SystemModel::Label::AcceptRequest{req} =>
            CrashAwareCachingDiskBetreeSystem::Label::Request{req},
        SystemModel::Label::DeliverReply{reply} =>
            CrashAwareCachingDiskBetreeSystem::Label::Reply{reply},
        SystemModel::Label::AcceptSyncRequest{..}
        | SystemModel::Label::DeliverSyncReply{..} =>
            CrashAwareCachingDiskBetreeSystem::Label::Noop,
        SystemModel::Label::ProgramUIOp{op} => match op {
            ProgramUserOp::Execute{req, reply} =>
                CrashAwareCachingDiskBetreeSystem::Label::Execute{
                    req,
                    reply,
                },
            ProgramUserOp::AcceptSyncRequest{sync_req_id} =>
                CrashAwareCachingDiskBetreeSystem::Label::ReqSync{
                    sync_req_id,
                },
            ProgramUserOp::DeliverSyncReply{sync_req_id} =>
                CrashAwareCachingDiskBetreeSystem::Label::ReplySync{
                    sync_req_id,
                },
        },
        SystemModel::Label::DiskInternal => {
            let pre_superblock =
                unified_cache_betree_superblockstore_i(pre);
            let post_superblock =
                unified_cache_betree_superblockstore_i(post);
            if !pre_superblock.landed
                && post_superblock.landed
            {
                CrashAwareCachingDiskBetreeSystem::Label::Sync
            } else {
                CrashAwareCachingDiskBetreeSystem::Label::Noop
            }
        },
        SystemModel::Label::Crash =>
            CrashAwareCachingDiskBetreeSystem::Label::Crash,
        SystemModel::Label::ProgramDiskOp{..}
        | SystemModel::Label::ProgramInternal
        | SystemModel::Label::Noop =>
            CrashAwareCachingDiskBetreeSystem::Label::Noop,
    }
}

pub closed spec fn unified_cache_betree_component_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    &&& UnifiedCacheJournalRefinement::inv(
        unified_cache_betree_journal_source(model),
    )
    &&& UnifiedCacheBranchBetreeRefinement::inv(
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(model),
    )
}

pub closed spec fn system_model_progress_history_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    &&& forall |req: Request|
        #[trigger] model.requests.contains(req)
        ==> model.id_history.contains(req.id)
    &&& forall |reply: Reply|
        #[trigger] model.replies.contains(reply)
        ==> model.id_history.contains(reply.id)
}

pub closed spec fn system_model_progress_unique_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    &&& forall |req: Request|
        #[trigger] model.requests.count(req) <= 1
    &&& forall |reply: Reply|
        #[trigger] model.replies.count(reply) <= 1
}

pub closed spec fn system_model_request_id_unique_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    forall |req1: Request, req2: Request| {
        &&& #[trigger] model.requests.contains(req1)
        &&& #[trigger] model.requests.contains(req2)
        &&& req1.id == req2.id
    } ==> req1 == req2
}

pub closed spec fn system_model_request_reply_disjoint_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    forall |req: Request, reply: Reply| {
        &&& #[trigger] model.requests.contains(req)
        &&& #[trigger] model.replies.contains(reply)
    } ==> req.id != reply.id
}

pub closed spec fn unified_cache_betree_ready_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    state.client_ready() ==> {
        &&& state.persistent_image is Some
        &&& state.journal.ready()
        &&& state.branch.control.metadata_loaded
        &&& state.journal.journal.seq_end()
            == state.branch.betree.memtable.seq_end
    }
}

pub closed spec fn unified_cache_betree_recovery_state_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    let journal_src =
        unified_cache_betree_journal_source(model);
    &&& (state.recovery_state is Begin
        || state.recovery_state is AwaitingSuperblock) ==> {
        &&& state.journal
            == AtomicJournalState::State::empty()
        &&& state.branch
            == AtomicBranchBetreeState::State::empty()
        &&& state.persistent_image is None
        &&& state.sync_phase is None
        &&& state.sync_req_map
            == Map::<
                crate::spec::MapSpec_t::SyncReqId,
                nat,
            >::empty()
        &&& state.outstanding_cache_reqs
            == Map::<ID, Address>::empty()
        &&& journal_src.journal_caching_disk_i().cache
            == Map::<Address, RawPage>::empty()
        &&& journal_src.journal_caching_disk_i().status
            == Map::<Address, PageStatus>::empty()
        &&& forall |id: ID|
            #[trigger] model.disk.requests.contains_key(id)
            ==> {
                &&& model.disk.requests[id] is ReadReq
                &&& model.disk.requests[id]->from
                    == spec_superblock_addr()
            }
        &&& forall |id: ID|
            #[trigger] model.disk.responses.contains_key(id)
            ==> {
                &&& model.disk.responses[id] is ReadResp
                &&& model.disk.content.contains_key(
                    spec_superblock_addr(),
                )
                &&& model.disk.responses[id]->data
                    == model.disk.content[
                        spec_superblock_addr()
                    ]
            }
    }
    &&& (state.recovery_state is Begin) ==> {
        &&& model.disk.requests
            == Map::<ID, DiskRequest>::empty()
        &&& model.disk.responses
            == Map::<ID, DiskResponse>::empty()
    }
    &&& (state.recovery_state is AwaitingSuperblock) ==> {
        &&& exists |id: ID|
            disk_has_pending_id(model.disk, id)
        &&& forall |left: ID, right: ID| {
            &&& #[trigger] disk_has_pending_id(
                model.disk,
                left,
            )
            &&& #[trigger] disk_has_pending_id(
                model.disk,
                right,
            )
        } ==> left == right
    }
    &&& (!(state.recovery_state is Begin)
        && !(state.recovery_state is AwaitingSuperblock)) ==> {
        &&& state.persistent_image is Some
    }
    &&& (state.recovery_state is MetadataLoadComplete
        || state.recovery_state is RecoveryComplete) ==> {
        &&& state.journal.ready()
        &&& state.branch.control.metadata_loaded
    }
}

pub closed spec fn unified_cache_betree_shared_cache_disk_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    &&& forall |addr: crate::disk::GenericDisk_v::Address|
        #[trigger] filled_cache_pages(state.cache).contains_key(addr)
        ==> addr.wf()
    &&& forall |addr: crate::disk::GenericDisk_v::Address|
        #[trigger] model.disk.content.contains_key(addr)
        && addr != spec_superblock_addr()
        ==> addr.wf()
    &&& forall |addr: crate::disk::GenericDisk_v::Address| {
        &&& #[trigger] filled_cache_status(state.cache)
            .contains_key(addr)
        &&& filled_cache_status(state.cache)[addr]
            == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& model.disk.content.contains_key(addr)
    } ==> {
        model.disk.content[addr]
            == cache_filled_page(state.cache, addr)
    }
}

pub closed spec fn unified_cache_betree_cache_response_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    forall |id: ID| {
        &&& #[trigger] model.disk.responses.contains_key(id)
        &&& state.outstanding_cache_reqs.contains_key(id)
    } ==> {
        let addr = state.outstanding_cache_reqs[id];
        let resp = model.disk.responses[id];
        &&& addr.wf()
        &&& resp is ReadResp ==> {
            resp->data == model.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& model.disk.content.contains_key(addr)
            &&& cache_filled_addr(state.cache, addr)
            &&& model.disk.content[addr]
                == cache_filled_page(state.cache, addr)
        }
    }
}

pub closed spec fn unified_cache_betree_outstanding_io_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    outstanding_cache_io_wf(
        model.program.state.cache,
        model.disk,
        model.program.state.outstanding_cache_reqs,
    )
}

pub closed spec fn unified_cache_betree_cache_request_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    &&& state.outstanding_cache_reqs.is_injective()
    &&& !state.outstanding_cache_reqs.contains_value(
        spec_superblock_addr(),
    )
    &&& state.outstanding_cache_reqs.values()
        <= state.cache.lookup_map.dom()
    &&& forall |id: ID|
        #[trigger] state.outstanding_cache_reqs
            .contains_key(id)
        ==> {
            let addr = state.outstanding_cache_reqs[id];
            let slot = state.cache.lookup_map[addr];
            match state.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} =>
                    entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr
                        && state.cache.status_map[slot]
                            is Writeback,
                _ => false,
            }
        }
}

pub closed spec fn unified_cache_betree_allocation_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    let journal_aus =
        unified_cache_betree_journal_source(model)
            .journal_projection_aus();
    let branch_aus =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(model)
                .branch_projection_aus();
    let reserved = UnifiedCacheBetreeSystem::State::reserved_aus();
    &&& state.free_aus.disjoint(reserved)
    &&& reserved.disjoint(journal_aus)
    &&& reserved.disjoint(branch_aus)
    &&& journal_aus.disjoint(branch_aus)
    &&& state.journal.ready() ==>
        state.free_aus.disjoint(journal_aus)
    &&& state.branch.control.metadata_loaded ==>
        state.free_aus.disjoint(branch_aus)
}

proof fn cache_access_preserves_shared_cache_disk_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    writes: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_betree_shared_cache_disk_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        writes.dom() <= Set::new(
            |addr: crate::disk::GenericDisk_v::Address| addr.wf(),
        ),
        post.disk.content == pre.disk.content,
    ensures
        unified_cache_betree_shared_cache_disk_inv(post),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    let cache_lbl = Cache::Label::Access{reads, writes};
    Cache::State::inv_next(pre_cache, post_cache, cache_lbl);
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre_cache,
            post_cache,
            cache_lbl,
            step,
        );
    match step {
        Cache::Step::access() => {}
        _ => {
            assert(false);
        }
    }

    assert forall |addr: crate::disk::GenericDisk_v::Address|
        #[trigger] filled_cache_pages(post_cache)
            .contains_key(addr)
        implies addr.wf()
    by {
        assert(cache_filled_addr(post_cache, addr));
        if writes.contains_key(addr) {
            assert(Cache::State::access(
                pre_cache,
                post_cache,
                cache_lbl,
            ));
        } else {
            Cache::State::access_unwritten_addr_unchanged(
                pre_cache,
                post_cache,
                reads,
                writes,
                addr,
            );
            assert(cache_filled_addr(pre_cache, addr));
            assert(filled_cache_pages(pre_cache)
                .contains_key(addr));
        }
    }
    assert forall |addr: crate::disk::GenericDisk_v::Address|
        #[trigger] post.disk.content.contains_key(addr)
        && addr != spec_superblock_addr()
        implies addr.wf()
    by {
        assert(pre.disk.content.contains_key(addr));
    }
    assert forall |addr: crate::disk::GenericDisk_v::Address| {
        &&& #[trigger] filled_cache_status(post_cache)
            .contains_key(addr)
        &&& filled_cache_status(post_cache)[addr]
            == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& post.disk.content.contains_key(addr)
    } implies post.disk.content[addr]
        == cache_filled_page(post_cache, addr)
    by {
        assert(cache_filled_addr(post_cache, addr));
        if writes.contains_key(addr) {
            assert(Cache::State::access(
                pre_cache,
                post_cache,
                cache_lbl,
            ));
            let slot = pre_cache.lookup_map[addr];
            assert(pre_cache.valid_write(addr));
            assert(pre_cache.lookup_map.contains_key(addr));
            let restricted =
                pre_cache.lookup_map.restrict(writes.dom());
            assert(restricted.contains_key(addr));
            assert(restricted[addr] == slot);
            assert(restricted.values().contains(slot));
            assert(pre_cache.write_updated_status(writes)
                .contains_key(slot));
            assert(post_cache.status_map[slot]
                == Status::Dirty);
            assert(post_cache.lookup_map[addr] == slot) by {
                assert(post_cache.build_lookup_map_props(
                    post_cache.lookup_map,
                ));
            }
            assert(cache_status_i(post_cache, addr)
                == PageStatus::Dirty);
            assert(filled_cache_status(post_cache)[addr]
                == PageStatus::Dirty);
            assert(false);
        } else {
            Cache::State::access_unwritten_addr_unchanged(
                pre_cache,
                post_cache,
                reads,
                writes,
                addr,
            );
            assert(cache_filled_addr(pre_cache, addr));
            assert(filled_cache_status(pre_cache)
                .contains_key(addr));
            assert(filled_cache_status(pre_cache)[addr]
                == PageStatus::Clean);
            assert(cache_filled_page(post_cache, addr)
                == cache_filled_page(pre_cache, addr));
            assert(pre.disk.content.contains_key(addr));
        }
    }
}

pub closed spec fn unified_cache_betree_superblock_cache_id_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let req_id = model.program.state.sync_phase.req_id();
    req_id is Some ==> {
        &&& disk_has_pending_id(model.disk, req_id.unwrap())
        &&& !model.program.state.outstanding_cache_reqs
            .contains_key(req_id.unwrap())
        &&& model.disk.requests.contains_key(req_id.unwrap())
            ==> {
                &&& model.disk.requests[req_id.unwrap()]
                    is WriteReq
                &&& model.disk.requests[req_id.unwrap()]->to
                    == spec_superblock_addr()
            }
        &&& model.disk.responses.contains_key(req_id.unwrap())
            ==> model.disk.responses[req_id.unwrap()]
                is WriteResp
    }
}

pub closed spec fn unified_cache_betree_sync_state_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    let journal_image_matches =
        |image: AbstractSuperblockImage| {
            &&& state.journal.in_flight is Some
            &&& state.journal.in_flight.unwrap().snapshot
                == image.journal_snapshot
            &&& state.journal.in_flight.unwrap().seq_end
                == image.journal_seq_end
        };
    match state.sync_phase {
        AtomicBetreeSyncPhase::None => {
            &&& state.journal.in_flight is None
            &&& state.branch.control.frozen is None
        },
        AtomicBetreeSyncPhase::Preparing{
            image,
            journal_ready,
            branch_ready,
        } => {
            &&& state.client_ready()
            &&& journal_image_matches(image)
            &&& journal_ready ==> {
                &&& state.journal.in_flight is Some
                &&& state.journal.journal.status is Some
                &&& state.journal.in_flight.unwrap().snapshot
                    .freshest_rec() is Some ==> {
                    state.journal.in_flight.unwrap().seq_end
                        <= state.journal.journal.clean_watermark()
                }
            }
            &&& state.branch.control.frozen is None ==> {
                &&& branch_ready
                &&& betree_metadata_from_superblock(image)
                    == state.branch.control.metadata
            }
            &&& state.branch.control.frozen is Some ==> {
                &&& state.branch.control.frozen.unwrap().metadata
                    == betree_metadata_from_superblock(image)
            }
        },
        AtomicBetreeSyncPhase::SuperblockWriteIssued{
            image,
            req_id,
        } => {
            &&& state.client_ready()
            &&& journal_image_matches(image)
            &&& state.journal.journal.status is Some
            &&& state.journal.in_flight.unwrap().snapshot
                .freshest_rec() is Some ==> {
                state.journal.in_flight.unwrap().seq_end
                    <= state.journal.journal.clean_watermark()
            }
            &&& state.branch.control.frozen is None ==> {
                betree_metadata_from_superblock(image)
                    == state.branch.control.metadata
            }
            &&& state.branch.control.frozen is Some ==> {
                state.branch.control.frozen.unwrap().metadata
                    == betree_metadata_from_superblock(image)
            }
            &&& model.disk.responses.contains_key(req_id)
                ==> superblock_matches(
                    model.disk.content[spec_superblock_addr()],
                    image,
                )
        },
    }
}

pub closed spec fn unified_cache_betree_disk_request_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    forall |id: ID|
        #[trigger] model.disk.requests.contains_key(id)
        && !state.outstanding_cache_reqs.contains_key(id)
        ==> {
            ||| {
                &&& state.recovery_state
                    is AwaitingSuperblock
                &&& model.disk.requests[id] is ReadReq
                &&& model.disk.requests[id]->from
                    == spec_superblock_addr()
            }
            ||| {
                &&& state.sync_phase.req_id() is Some
                &&& state.sync_phase.req_id().unwrap() == id
                &&& model.disk.requests[id] is WriteReq
                &&& model.disk.requests[id]->to
                    == spec_superblock_addr()
                &&& state.sync_phase.image() is Some
                &&& superblock_matches(
                    model.disk.requests[id]->data,
                    state.sync_phase.image().unwrap(),
                )
            }
    }
}

pub closed spec fn unified_cache_betree_superblock_image_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    state.persistent_image is Some
        && !unified_cache_betree_superblock_landed(
            state,
            model.disk,
        )
        ==> superblock_matches(
            model.disk.content[spec_superblock_addr()],
            state.persistent_image.unwrap(),
        )
}

pub closed spec fn unified_cache_betree_unready_cache_clean_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    (!model.program.state.journal.ready()
        || !model.program.state.branch.control.metadata_loaded)
    ==> {
        forall |slot: Slot|
            #[trigger] model.program.state.cache.entries
                .contains_key(slot)
            && model.program.state.cache.entries[slot]
                is Filled
            ==> model.program.state.cache.status_map[slot]
                is Clean
    }
}

pub open spec fn unified_cache_betree_branch_clean_aus(
    state: UnifiedCacheBetreeSystem::State,
) -> Set<crate::disk::GenericDisk_v::AU> {
    state.branch.control.persistent_aus
        + if state.sync_phase.branch_ready()
            && state.branch.control.frozen is Some
        {
            state.branch.control.frozen.unwrap().aus
        } else {
            Set::empty()
        }
}

pub closed spec fn unified_cache_betree_persistent_branch_cache_clean_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    let clean_aus = unified_cache_betree_branch_clean_aus(state);
    state.branch.control.metadata_loaded ==> {
        forall |slot: Slot|
            #[trigger] state.cache.entries.contains_key(slot)
            && state.cache.entries[slot] is Filled
            && clean_aus.contains(
                state.cache.entries[slot].get_addr().au,
            )
            ==> state.cache.status_map[slot] is Clean
    }
}

pub closed spec fn unified_cache_betree_wip_persistent_disjoint_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    let state = model.program.state;
    state.branch.control.metadata_loaded ==> {
        cached_branch_alloc_aus(
            state.branch.betree.wip_branches,
        ).disjoint(state.branch.control.persistent_aus)
    }
}

proof fn cache_internal_preserves_shared_cache_disk_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_betree_shared_cache_disk_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
        post.disk.content == pre.disk.content,
    ensures
        unified_cache_betree_shared_cache_disk_inv(post),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    Cache::State::inv_next(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
    );

    assert forall |addr:
        crate::disk::GenericDisk_v::Address|
        #[trigger] filled_cache_pages(post_cache)
            .contains_key(addr)
        implies addr.wf()
    by {
        assert(cache_filled_addr(post_cache, addr));
        cache_internal_post_filled_addr_was_pre_filled(
            pre_cache,
            post_cache,
            addr,
        );
        assert(filled_cache_pages(pre_cache)
            .contains_key(addr));
    }
    assert forall |addr:
        crate::disk::GenericDisk_v::Address|
        #[trigger] post.disk.content.contains_key(addr)
            && addr != spec_superblock_addr()
        implies addr.wf()
    by {
        assert(pre.disk.content.contains_key(addr));
    }
    assert forall |addr:
        crate::disk::GenericDisk_v::Address| {
        &&& #[trigger] filled_cache_status(post_cache)
            .contains_key(addr)
        &&& filled_cache_status(post_cache)[addr]
            == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& post.disk.content.contains_key(addr)
    } implies post.disk.content[addr]
        == cache_filled_page(post_cache, addr)
    by {
        cache_internal_preserves_clean_filled_addr(
            pre_cache,
            post_cache,
            addr,
        );
        assert(filled_cache_status(pre_cache)
            .contains_key(addr));
        assert(filled_cache_status(pre_cache)[addr]
            == PageStatus::Clean);
        assert(pre.disk.content.contains_key(addr));
        assert(pre.disk.content[addr]
            == cache_filled_page(pre_cache, addr));
    }
}

proof fn cache_internal_preserves_unready_cache_clean_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
)
    requires
        refinement_inv(pre),
        post.program.state.journal.ready()
            == pre.program.state.journal.ready(),
        post.program.state.branch.control.metadata_loaded
            == pre.program.state.branch.control.metadata_loaded,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
    ensures
        unified_cache_betree_unready_cache_clean_inv(post),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    Cache::State::inv_next(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
    );
    if !post.program.state.journal.ready()
        || !post.program.state.branch.control.metadata_loaded
    {
        post_cache.build_lookup_map_ensures();
        assert forall |slot: Slot|
            #[trigger] post_cache.entries.contains_key(slot)
            && post_cache.entries[slot] is Filled
            implies post_cache.status_map[slot] is Clean
        by {
            let addr = post_cache.entries[slot].get_addr();
            assert(post_cache.lookup_map.contains_key(addr));
            assert(post_cache.lookup_map[addr] == slot);
            assert(cache_filled_addr(post_cache, addr));
            cache_internal_post_filled_addr_was_pre_filled(
                pre_cache,
                post_cache,
                addr,
            );
            assert(pre_cache.lookup_map.contains_key(addr));
            assert(pre_cache.entries[
                pre_cache.lookup_map[addr]
            ] is Filled);
            assert(pre_cache.status_map[
                pre_cache.lookup_map[addr]
            ] is Clean);
            assert(post_cache.status_map[slot]
                == pre_cache.status_map[
                    pre_cache.lookup_map[addr]
                ]);
        }
    }
}

proof fn cache_disk_ops_begin_preserves_unready_cache_clean_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    requests: Set<DiskRequest>,
)
    requires
        refinement_inv(pre),
        post.program.state.journal.ready()
            == pre.program.state.journal.ready(),
        post.program.state.branch.control.metadata_loaded
            == pre.program.state.branch.control.metadata_loaded,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps {
                requests,
                responses: Map::empty(),
            },
        ),
    ensures
        unified_cache_betree_unready_cache_clean_inv(post),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    let cache_lbl = Cache::Label::DiskOps {
        requests,
        responses: Map::empty(),
    };
    Cache::State::inv_next(pre_cache, post_cache, cache_lbl);
    pre_cache.build_lookup_map_ensures();
    if !post.program.state.journal.ready()
        || !post.program.state.branch.control.metadata_loaded
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_step = choose |step: Cache::Step|
            Cache::State::next_by(
                pre_cache,
                post_cache,
                cache_lbl,
                step,
            );
        match cache_step {
            Cache::Step::load_initiate(
                new_slots_mapping,
            ) => {
                reveal(Cache::State::load_initiate);
                let updated_entries = Map::new(
                    |slot: Slot|
                        new_slots_mapping.contains_key(slot),
                    |slot: Slot| Entry::Loading {
                        addr: new_slots_mapping[slot],
                    },
                );
                assert(post_cache.status_map
                    == pre_cache.status_map);
                assert forall |slot: Slot|
                    #[trigger] post_cache.entries
                        .contains_key(slot)
                    && post_cache.entries[slot] is Filled
                    implies post_cache.status_map[slot]
                        is Clean
                by {
                    assert(!updated_entries
                        .contains_key(slot)) by {
                        if updated_entries
                            .contains_key(slot)
                        {
                            assert(post_cache.entries[slot]
                                is Loading);
                            assert(false);
                        }
                    }
                    assert(post_cache.entries[slot]
                        == pre_cache.entries[slot]);
                    assert(pre_cache.entries[slot]
                        is Filled);
                    assert(pre_cache.status_map[slot]
                        is Clean);
                }
            },
            Cache::Step::writeback_initiate() => {
                reveal(Cache::State::
                    writeback_initiate);
                let request = choose |request: DiskRequest|
                    requests.contains(request);
                assert(requests.contains(request));
                assert(pre_cache.valid_writeback_requests(
                    requests,
                ));
                assert(request is WriteReq);
                assert(pre_cache.lookup_map
                    .contains_key(request->to));
                let slot = pre_cache.lookup_map[request->to];
                assert(pre_cache.build_lookup_map_props(
                    pre_cache.lookup_map,
                ));
                assert(pre_cache.entries.contains_key(slot));
                assert(pre_cache.entries[slot] is Filled);
                assert(pre_cache.status_map[slot] is Dirty);
                assert(unified_cache_betree_unready_cache_clean_inv(
                    pre,
                ));
                assert(pre_cache.status_map[slot] is Clean);
                assert(false);
            },
            _ => {
                assert(false);
            },
        }
    }
}

proof fn cache_disk_ops_end_preserves_unready_cache_clean_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    responses: Map<Address, DiskResponse>,
)
    requires
        refinement_inv(pre),
        post.program.state.journal.ready()
            == pre.program.state.journal.ready(),
        post.program.state.branch.control.metadata_loaded
            == pre.program.state.branch.control.metadata_loaded,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps {
                requests: Set::empty(),
                responses,
            },
        ),
    ensures
        unified_cache_betree_unready_cache_clean_inv(post),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    let cache_lbl = Cache::Label::DiskOps {
        requests: Set::empty(),
        responses,
    };
    Cache::State::inv_next(pre_cache, post_cache, cache_lbl);
    pre_cache.build_lookup_map_ensures();
    if !post.program.state.journal.ready()
        || !post.program.state.branch.control.metadata_loaded
    {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_step = choose |step: Cache::Step|
            Cache::State::next_by(
                pre_cache,
                post_cache,
                cache_lbl,
                step,
            );
        match cache_step {
            Cache::Step::load_complete() => {
                reveal(Cache::State::load_complete);
                let slot_addr_map =
                    pre_cache.lookup_map
                        .restrict(responses.dom())
                        .invert();
                let updated_entries = Map::new(
                    |slot: Slot|
                        slot_addr_map.contains_key(slot),
                    |slot: Slot| Entry::Filled {
                        addr: slot_addr_map[slot],
                        data: responses[
                            slot_addr_map[slot]
                        ]->data,
                    },
                );
                let updated_status_map = Map::new(
                    |slot: Slot|
                        slot_addr_map.contains_key(slot),
                    |slot: Slot| Status::Clean,
                );
                assert forall |slot: Slot|
                    #[trigger] post_cache.entries
                        .contains_key(slot)
                    && post_cache.entries[slot] is Filled
                    implies post_cache.status_map[slot]
                        is Clean
                by {
                    if updated_entries.contains_key(slot) {
                        assert(updated_status_map
                            .contains_key(slot));
                        assert(post_cache.status_map[slot]
                            is Clean);
                    } else {
                        assert(!updated_status_map
                            .contains_key(slot));
                        assert(post_cache.entries[slot]
                            == pre_cache.entries[slot]);
                        assert(pre_cache.entries[slot]
                            is Filled);
                        assert(pre_cache.status_map[slot]
                            is Clean);
                        assert(post_cache.status_map[slot]
                            == pre_cache.status_map[slot]);
                    }
                }
            },
            Cache::Step::writeback_complete() => {
                reveal(Cache::State::
                    writeback_complete);
                let addr = choose |addr: Address|
                    responses.contains_key(addr);
                assert(responses.contains_key(addr));
                assert(pre_cache.valid_writeback_responses(
                    responses,
                ));
                assert(pre_cache.lookup_map
                    .contains_key(addr));
                let slot = pre_cache.lookup_map[addr];
                assert(pre_cache.build_lookup_map_props(
                    pre_cache.lookup_map,
                ));
                assert(pre_cache.entries.contains_key(slot));
                assert(pre_cache.entries[slot] is Filled);
                assert(pre_cache.status_map[slot]
                    is Writeback);
                assert(unified_cache_betree_unready_cache_clean_inv(
                    pre,
                ));
                assert(pre_cache.status_map[slot] is Clean);
                assert(false);
            },
            _ => {
                assert(false);
            },
        }
    }
}

proof fn cache_internal_preserves_persistent_branch_cache_clean_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
)
    requires
        refinement_inv(pre),
        post.program.state.branch.control
            == pre.program.state.branch.control,
        post.program.state.sync_phase
            == pre.program.state.sync_phase,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
    ensures
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        ),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    Cache::State::inv_next(
        pre_cache,
        post_cache,
        Cache::Label::Internal{},
    );
    if post.program.state.branch.control.metadata_loaded {
        pre_cache.build_lookup_map_ensures();
        post_cache.build_lookup_map_ensures();
        assert forall |slot: Slot|
            #[trigger] post_cache.entries.contains_key(slot)
            && post_cache.entries[slot] is Filled
            && unified_cache_betree_branch_clean_aus(
                post.program.state,
            ).contains(post_cache.entries[slot].get_addr().au)
            implies post_cache.status_map[slot] is Clean
        by {
            let addr = post_cache.entries[slot].get_addr();
            assert(post_cache.lookup_map.contains_key(addr));
            assert(post_cache.lookup_map[addr] == slot);
            cache_internal_post_filled_addr_was_pre_filled(
                pre_cache,
                post_cache,
                addr,
            );
            let pre_slot = pre_cache.lookup_map[addr];
            assert(pre_cache.entries.contains_key(pre_slot));
            assert(pre_cache.entries[pre_slot] is Filled);
            assert(pre_cache.entries[pre_slot].get_addr() == addr);
            assert(unified_cache_betree_branch_clean_aus(
                pre.program.state,
            ).contains(addr.au));
            assert(unified_cache_betree_persistent_branch_cache_clean_inv(
                pre,
            ));
            assert(pre_cache.status_map[pre_slot] is Clean);
            assert(post_cache.status_map[slot]
                == pre_cache.status_map[pre_slot]);
        }
    }
}

proof fn cache_access_preserves_persistent_branch_cache_clean_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        refinement_inv(pre),
        post.program.state.branch.control
            == pre.program.state.branch.control,
        post.program.state.sync_phase
            == pre.program.state.sync_phase,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        writes.dom().disjoint(addresses_in_aus(
            unified_cache_betree_branch_clean_aus(
                pre.program.state,
            ),
        )),
    ensures
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        ),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    Cache::State::inv_next(
        pre_cache,
        post_cache,
        Cache::Label::Access{reads, writes},
    );
    if post.program.state.branch.control.metadata_loaded {
        pre_cache.build_lookup_map_ensures();
        post_cache.build_lookup_map_ensures();
        assert forall |slot: Slot|
            #[trigger] post_cache.entries.contains_key(slot)
            && post_cache.entries[slot] is Filled
            && unified_cache_betree_branch_clean_aus(
                post.program.state,
            ).contains(post_cache.entries[slot].get_addr().au)
            implies post_cache.status_map[slot] is Clean
        by {
            let addr = post_cache.entries[slot].get_addr();
            assert(addresses_in_aus(
                unified_cache_betree_branch_clean_aus(
                    pre.program.state,
                ),
            ).contains(addr));
            assert(!writes.contains_key(addr));
            Cache::State::access_unwritten_addr_unchanged(
                pre_cache,
                post_cache,
                reads,
                writes,
                addr,
            );
            let pre_slot = pre_cache.lookup_map[addr];
            assert(pre_cache.entries.contains_key(pre_slot));
            assert(pre_cache.entries[pre_slot] is Filled);
            assert(pre_cache.entries[pre_slot].get_addr() == addr);
            assert(unified_cache_betree_branch_clean_aus(
                pre.program.state,
            ).contains(addr.au));
            assert(unified_cache_betree_persistent_branch_cache_clean_inv(
                pre,
            ));
            assert(pre_cache.status_map[pre_slot] is Clean);
            assert(post_cache.lookup_map[addr] == slot);
            assert(post_cache.status_map[slot]
                == pre_cache.status_map[pre_slot]);
        }
    }
}

proof fn cache_disk_ops_begin_preserves_persistent_branch_cache_clean_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    requests: Set<DiskRequest>,
)
    requires
        refinement_inv(pre),
        post.program.state.branch.control
            == pre.program.state.branch.control,
        post.program.state.sync_phase
            == pre.program.state.sync_phase,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps {
                requests,
                responses: Map::empty(),
            },
        ),
    ensures
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        ),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    let cache_lbl = Cache::Label::DiskOps {
        requests,
        responses: Map::empty(),
    };
    Cache::State::inv_next(pre_cache, post_cache, cache_lbl);
    pre_cache.build_lookup_map_ensures();
    if post.program.state.branch.control.metadata_loaded {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_step = choose |step: Cache::Step|
            Cache::State::next_by(
                pre_cache,
                post_cache,
                cache_lbl,
                step,
            );
        match cache_step {
            Cache::Step::load_initiate(
                new_slots_mapping,
            ) => {
                reveal(Cache::State::load_initiate);
                let updated_entries = Map::new(
                    |slot: Slot|
                        new_slots_mapping.contains_key(slot),
                    |slot: Slot| Entry::Loading {
                        addr: new_slots_mapping[slot],
                    },
                );
                assert forall |slot: Slot|
                    #[trigger] post_cache.entries
                        .contains_key(slot)
                    && post_cache.entries[slot] is Filled
                    && unified_cache_betree_branch_clean_aus(
                        post.program.state,
                    ).contains(
                            post_cache.entries[slot]
                                .get_addr().au,
                        )
                    implies post_cache.status_map[slot]
                        is Clean
                by {
                    assert(!updated_entries.contains_key(slot));
                    assert(post_cache.entries[slot]
                        == pre_cache.entries[slot]);
                    assert(pre_cache.entries[slot] is Filled);
                    assert(pre_cache.status_map[slot] is Clean);
                }
            },
            Cache::Step::writeback_initiate() => {
                reveal(Cache::State::writeback_initiate);
                assert forall |slot: Slot|
                    #[trigger] post_cache.entries
                        .contains_key(slot)
                    && post_cache.entries[slot] is Filled
                    && unified_cache_betree_branch_clean_aus(
                        post.program.state,
                    ).contains(
                            post_cache.entries[slot]
                                .get_addr().au,
                        )
                    implies post_cache.status_map[slot]
                        is Clean
                by {
                    assert(post_cache.entries
                        == pre_cache.entries);
                    assert(pre_cache.entries[slot] is Filled);
                    assert(pre_cache.status_map[slot] is Clean);
                    if post_cache.status_map[slot]
                        is Writeback
                    {
                        let request = choose |request: DiskRequest|
                            #[trigger] requests.contains(request)
                            && request is WriteReq
                            && pre_cache.lookup_map[
                                request->to
                            ] == slot;
                        assert(pre_cache.valid_writeback_requests(
                            requests,
                        ));
                        assert(pre_cache.status_map[slot]
                            is Dirty);
                        assert(false);
                    }
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

proof fn cache_disk_ops_end_preserves_persistent_branch_cache_clean_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    responses: Map<Address, DiskResponse>,
)
    requires
        refinement_inv(pre),
        post.program.state.branch.control
            == pre.program.state.branch.control,
        post.program.state.sync_phase
            == pre.program.state.sync_phase,
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps {
                requests: Set::empty(),
                responses,
            },
        ),
    ensures
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        ),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    let cache_lbl = Cache::Label::DiskOps {
        requests: Set::empty(),
        responses,
    };
    Cache::State::inv_next(pre_cache, post_cache, cache_lbl);
    pre_cache.build_lookup_map_ensures();
    if post.program.state.branch.control.metadata_loaded {
        reveal(Cache::State::next);
        reveal(Cache::State::next_by);
        let cache_step = choose |step: Cache::Step|
            Cache::State::next_by(
                pre_cache,
                post_cache,
                cache_lbl,
                step,
            );
        match cache_step {
            Cache::Step::load_complete() => {
                reveal(Cache::State::load_complete);
                let slot_addr_map =
                    pre_cache.lookup_map
                        .restrict(responses.dom())
                        .invert();
                let updated_entries = Map::new(
                    |slot: Slot|
                        slot_addr_map.contains_key(slot),
                    |slot: Slot| Entry::Filled {
                        addr: slot_addr_map[slot],
                        data: responses[
                            slot_addr_map[slot]
                        ]->data,
                    },
                );
                assert forall |slot: Slot|
                    #[trigger] post_cache.entries
                        .contains_key(slot)
                    && post_cache.entries[slot] is Filled
                    && unified_cache_betree_branch_clean_aus(
                        post.program.state,
                    ).contains(
                            post_cache.entries[slot]
                                .get_addr().au,
                        )
                    implies post_cache.status_map[slot]
                        is Clean
                by {
                    if updated_entries.contains_key(slot) {
                        assert(post_cache.status_map[slot]
                            is Clean);
                    } else {
                        assert(post_cache.entries[slot]
                            == pre_cache.entries[slot]);
                        assert(pre_cache.entries[slot] is Filled);
                        assert(pre_cache.status_map[slot] is Clean);
                        assert(post_cache.status_map[slot]
                            == pre_cache.status_map[slot]);
                    }
                }
            },
            Cache::Step::writeback_complete() => {
                reveal(Cache::State::writeback_complete);
                assert forall |slot: Slot|
                    #[trigger] post_cache.entries
                        .contains_key(slot)
                    && post_cache.entries[slot] is Filled
                    && unified_cache_betree_branch_clean_aus(
                        post.program.state,
                    ).contains(
                            post_cache.entries[slot]
                                .get_addr().au,
                        )
                    implies post_cache.status_map[slot]
                        is Clean
                by {
                    assert(post_cache.entries
                        == pre_cache.entries);
                    if post_cache.status_map[slot] is Clean {
                    } else {
                        assert(post_cache.status_map[slot]
                            == pre_cache.status_map[slot]);
                        assert(pre_cache.status_map[slot]
                            is Clean);
                    }
                }
            },
            _ => {
                assert(false);
            },
        }
    }
}

proof fn cache_internal_preserves_protocol_invs(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
)
    requires
        refinement_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Internal{},
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
        post.disk.requests == pre.disk.requests,
        post.disk.responses == pre.disk.responses,
        post.disk.content == pre.disk.content,
    ensures
        unified_cache_betree_cache_request_inv(post),
        unified_cache_betree_outstanding_io_inv(post),
        unified_cache_betree_cache_response_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let tracked_reqs = pre_state.outstanding_cache_reqs;
    let protected = tracked_reqs.values();

    assert(protected <= pre_state.cache.lookup_map.dom());
    assert forall |addr: Address|
        #[trigger] protected.contains(addr)
        implies {
            let slot = pre_state.cache.lookup_map[addr];
            match pre_state.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} =>
                    entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr
                        && pre_state.cache.status_map[slot]
                            is Writeback,
                _ => false,
            }
        }
    by {
        let id = choose |id: ID|
            #[trigger] tracked_reqs.contains_key(id)
                && tracked_reqs[id] == addr;
        assert(tracked_reqs.contains_key(id));
        assert(unified_cache_betree_cache_request_inv(pre));
    }
    cache_internal_preserves_protected_entries(
        pre_state.cache,
        post_state.cache,
        protected,
    );

    assert(post_state.outstanding_cache_reqs.is_injective());
    assert(!post_state.outstanding_cache_reqs
        .contains_value(spec_superblock_addr()));
    assert forall |addr: Address|
        #[trigger] post_state.outstanding_cache_reqs
            .values().contains(addr)
        implies post_state.cache.lookup_map
            .contains_key(addr)
    by {
        assert(protected.contains(addr));
    }
    assert(post_state.outstanding_cache_reqs.values()
        <= post_state.cache.lookup_map.dom());
    assert forall |id: ID|
        #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        implies {
            let addr = post_state.outstanding_cache_reqs[id];
            let slot = post_state.cache.lookup_map[addr];
            match post_state.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} =>
                    entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr
                        && post_state.cache.status_map[slot]
                            is Writeback,
                _ => false,
            }
        }
    by {
        assert(tracked_reqs.contains_key(id));
        let addr = tracked_reqs[id];
        assert(protected.contains(addr));
        assert(post_state.cache.lookup_map[addr]
            == pre_state.cache.lookup_map[addr]);
    }
    assert(unified_cache_betree_cache_request_inv(post));

    assert(post_state.outstanding_cache_reqs.is_injective());
    assert forall |id: ID|
        #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        implies disk_has_pending_id(post.disk, id)
    by {
        assert(tracked_reqs.contains_key(id));
        assert(disk_has_pending_id(pre.disk, id));
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map
                .contains_key(addr)
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ] is Filled
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ]->data == req->data
            &&& post_state.cache.status_map[
                post_state.cache.lookup_map[addr]
            ] == Status::Writeback{}
        }
    } by {
        assert(tracked_reqs.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        let addr = tracked_reqs[id];
        let req = pre.disk.requests[id];
        assert(protected.contains(addr));
        assert(post_state.cache.lookup_map[addr]
            == pre_state.cache.lookup_map[addr]);
    }
    assert(unified_cache_betree_outstanding_io_inv(post));

    assert forall |id: ID| {
        &&& #[trigger] post.disk.responses.contains_key(id)
        &&& post_state.outstanding_cache_reqs.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let resp = post.disk.responses[id];
        &&& addr.wf()
        &&& resp is ReadResp ==> {
            resp->data == post.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& cache_filled_addr(post_state.cache, addr)
            &&& post.disk.content[addr]
                == cache_filled_page(post_state.cache, addr)
        }
    } by {
        assert(pre.disk.responses.contains_key(id));
        assert(tracked_reqs.contains_key(id));
        let addr = tracked_reqs[id];
        assert(protected.contains(addr));
        assert(unified_cache_betree_cache_response_inv(pre));
        if pre.disk.responses[id] is WriteResp {
            assert(post_state.cache.lookup_map[addr]
                == pre_state.cache.lookup_map[addr]);
            assert(cache_filled_addr(
                post_state.cache,
                addr,
            ));
            assert(cache_filled_page(post_state.cache, addr)
                == cache_filled_page(pre_state.cache, addr));
        }
    }
    assert(unified_cache_betree_cache_response_inv(post));
}

proof fn cache_access_preserves_protocol_invs(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        refinement_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
        post.disk.requests == pre.disk.requests,
        post.disk.responses == pre.disk.responses,
        post.disk.content == pre.disk.content,
    ensures
        unified_cache_betree_cache_request_inv(post),
        unified_cache_betree_outstanding_io_inv(post),
        unified_cache_betree_cache_response_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let tracked_reqs = pre_state.outstanding_cache_reqs;
    let protected = tracked_reqs.values();
    let cache_lbl = Cache::Label::Access{reads, writes};

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre_state.cache,
            post_state.cache,
            cache_lbl,
            step,
        );
    match cache_step {
        Cache::Step::access() => {}
        _ => {
            assert(false);
        }
    }

    assert(protected <= pre_state.cache.lookup_map.dom());
    assert forall |addr: Address|
        #[trigger] protected.contains(addr)
        implies {
            let slot = pre_state.cache.lookup_map[addr];
            match pre_state.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} =>
                    entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr
                        && pre_state.cache.status_map[slot]
                            is Writeback,
                _ => false,
            }
        }
    by {
        let id = choose |id: ID|
            #[trigger] tracked_reqs.contains_key(id)
                && tracked_reqs[id] == addr;
        assert(tracked_reqs.contains_key(id));
        assert(unified_cache_betree_cache_request_inv(pre));
    }
    assert forall |addr: Address|
        #[trigger] protected.contains(addr)
        implies !writes.contains_key(addr)
    by {
        if writes.contains_key(addr) {
            assert(Cache::State::access(
                pre_state.cache,
                post_state.cache,
                cache_lbl,
            ));
            assert(pre_state.cache.valid_write(addr));
            let slot = pre_state.cache.lookup_map[addr];
            match pre_state.cache.entries[slot] {
                Entry::Loading{..} => {
                    assert(false);
                }
                Entry::Filled{..} => {
                    assert(pre_state.cache.status_map[slot]
                        is Writeback);
                    assert(false);
                }
                _ => {
                    assert(false);
                }
            }
        }
    }
    assert forall |addr: Address|
        #[trigger] protected.contains(addr)
        implies {
            &&& post_state.cache.lookup_map
                .contains_key(addr)
            &&& post_state.cache.lookup_map[addr]
                == pre_state.cache.lookup_map[addr]
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ] == pre_state.cache.entries[
                pre_state.cache.lookup_map[addr]
            ]
            &&& post_state.cache.status_map[
                post_state.cache.lookup_map[addr]
            ] == pre_state.cache.status_map[
                pre_state.cache.lookup_map[addr]
            ]
        }
    by {
        Cache::State::access_unwritten_addr_unchanged(
            pre_state.cache,
            post_state.cache,
            reads,
            writes,
            addr,
        );
    }

    assert(post_state.outstanding_cache_reqs.is_injective());
    assert(!post_state.outstanding_cache_reqs
        .contains_value(spec_superblock_addr()));
    assert(post_state.outstanding_cache_reqs.values()
        <= post_state.cache.lookup_map.dom()) by {
        assert forall |addr: Address|
            #[trigger] post_state.outstanding_cache_reqs
                .values().contains(addr)
            implies post_state.cache.lookup_map
                .contains_key(addr)
        by {
            assert(protected.contains(addr));
        }
    }
    assert forall |id: ID|
        #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        implies {
            let addr = post_state.outstanding_cache_reqs[id];
            let slot = post_state.cache.lookup_map[addr];
            match post_state.cache.entries[slot] {
                Entry::Loading{addr: entry_addr} =>
                    entry_addr == addr,
                Entry::Filled{addr: entry_addr, ..} =>
                    entry_addr == addr
                        && post_state.cache.status_map[slot]
                            is Writeback,
                _ => false,
            }
        }
    by {
        assert(tracked_reqs.contains_key(id));
        let addr = tracked_reqs[id];
        assert(protected.contains(addr));
    }
    assert(unified_cache_betree_cache_request_inv(post));

    assert forall |id: ID|
        #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        implies disk_has_pending_id(post.disk, id)
    by {
        assert(tracked_reqs.contains_key(id));
        assert(disk_has_pending_id(pre.disk, id));
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map
                .contains_key(addr)
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ] is Filled
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ]->data == req->data
            &&& post_state.cache.status_map[
                post_state.cache.lookup_map[addr]
            ] == Status::Writeback{}
        }
    } by {
        assert(tracked_reqs.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        let addr = tracked_reqs[id];
        assert(protected.contains(addr));
    }
    assert(unified_cache_betree_outstanding_io_inv(post));

    assert forall |id: ID| {
        &&& #[trigger] post.disk.responses.contains_key(id)
        &&& post_state.outstanding_cache_reqs.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let resp = post.disk.responses[id];
        &&& addr.wf()
        &&& resp is ReadResp ==> {
            resp->data == post.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& cache_filled_addr(post_state.cache, addr)
            &&& post.disk.content[addr]
                == cache_filled_page(post_state.cache, addr)
        }
    } by {
        assert(pre.disk.responses.contains_key(id));
        assert(tracked_reqs.contains_key(id));
        let addr = tracked_reqs[id];
        assert(protected.contains(addr));
        assert(unified_cache_betree_cache_response_inv(pre));
        if pre.disk.responses[id] is WriteResp {
            assert(cache_filled_addr(post_state.cache, addr));
            assert(cache_filled_page(post_state.cache, addr)
                == cache_filled_page(pre_state.cache, addr));
        }
    }
    assert(unified_cache_betree_cache_response_inv(post));
}

proof fn cache_responses_coherent(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    resp_map: Map<ID, DiskResponse>,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        refinement_inv(pre),
        resp_map <= pre.disk.responses,
        resp_map.dom()
            <= pre.program.state.outstanding_cache_reqs.dom(),
        cache_resps == Map::new(
            |addr|
                pre.program.state.outstanding_cache_reqs
                    .restrict(resp_map.dom())
                    .invert()
                    .contains_key(addr),
            |addr|
                resp_map[
                    pre.program.state.outstanding_cache_reqs
                        .restrict(resp_map.dom())
                        .invert()[addr]
                ],
        ),
    ensures
        cache_resps.dom()
            <= Set::new(|addr: Address| addr.wf()),
        forall |addr: Address|
            #[trigger] cache_resps.contains_key(addr)
            ==> {
                &&& cache_resps[addr] is ReadResp ==> {
                    cache_resps[addr]->data
                        == pre.disk.content[addr]
                }
                &&& cache_resps[addr] is WriteResp ==> {
                    &&& pre.disk.content.contains_key(addr)
                    &&& cache_filled_addr(
                        pre.program.state.cache,
                        addr,
                    )
                    &&& pre.disk.content[addr]
                        == cache_filled_page(
                            pre.program.state.cache,
                            addr,
                        )
                }
            },
{
    let state = pre.program.state;
    let restricted =
        state.outstanding_cache_reqs.restrict(
            resp_map.dom(),
        );
    let finished = restricted.invert();

    assert forall |addr: Address|
        #[trigger] cache_resps.contains_key(addr)
        implies {
            &&& addr.wf()
            &&& cache_resps[addr] is ReadResp ==> {
                cache_resps[addr]->data
                    == pre.disk.content[addr]
            }
            &&& cache_resps[addr] is WriteResp ==> {
                &&& pre.disk.content.contains_key(addr)
                &&& cache_filled_addr(state.cache, addr)
                &&& pre.disk.content[addr]
                    == cache_filled_page(state.cache, addr)
            }
        }
    by {
        assert(finished.contains_key(addr));
        Cache::State::invert_contains_pair(
            restricted,
            addr,
        );
        let id = finished[addr];
        assert(restricted.contains_pair(id, addr));
        assert(resp_map.contains_key(id));
        assert(state.outstanding_cache_reqs
            .contains_key(id));
        assert(state.outstanding_cache_reqs[id] == addr);
        assert(pre.disk.responses.contains_key(id));
        assert(pre.disk.responses[id] == resp_map[id]);
        assert(unified_cache_betree_cache_response_inv(pre));
    }
}

proof fn cache_io_begin_preserves_shared_cache_disk_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_betree_shared_cache_disk_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{
                requests: req_map.values(),
                responses: Map::empty(),
            },
        ),
        post.disk.content == pre.disk.content,
    ensures
        unified_cache_betree_shared_cache_disk_inv(post),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    let cache_lbl = Cache::Label::DiskOps{
        requests: req_map.values(),
        responses: Map::<Address, DiskResponse>::empty(),
    };
    Cache::State::inv_next(
        pre_cache,
        post_cache,
        cache_lbl,
    );
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre_cache,
            post_cache,
            cache_lbl,
            step,
        );
    match step {
        Cache::Step::load_initiate(new_slots_mapping) => {
            assert(Cache::State::load_initiate(
                pre_cache,
                post_cache,
                cache_lbl,
                new_slots_mapping,
            )) by {
                reveal(Cache::State::load_initiate);
            }
        }
        Cache::Step::writeback_initiate() => {
            assert(Cache::State::writeback_initiate(
                pre_cache,
                post_cache,
                cache_lbl,
            )) by {
                reveal(Cache::State::writeback_initiate);
            }
        }
        _ => {
            assert(false);
        }
    }

    assert forall |addr: Address|
        #[trigger] filled_cache_pages(post_cache)
            .contains_key(addr)
        implies addr.wf()
    by {
        assert(cache_filled_addr(post_cache, addr));
        match step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Loading{
                        addr: new_slots_mapping[slot],
                    },
                );
                let post_slot = post_cache.lookup_map[addr];
                assert(!new_slots_mapping.invert()
                    .contains_key(addr)) by {
                    if new_slots_mapping.invert()
                        .contains_key(addr)
                    {
                        Cache::State::invert_contains_pair(
                            new_slots_mapping,
                            addr,
                        );
                        let slot =
                            new_slots_mapping.invert()[addr];
                        assert(updated_entries
                            .contains_key(slot));
                        assert(post_cache.entries[slot]
                            == Entry::Loading{addr});
                        assert(false);
                    }
                }
                assert(pre_cache.lookup_map
                    .contains_key(addr));
                assert(pre_cache.lookup_map[addr]
                    == post_slot);
                assert(!updated_entries
                    .contains_key(post_slot));
                assert(post_cache.entries[post_slot]
                    == pre_cache.entries[post_slot]);
                assert(cache_filled_addr(pre_cache, addr));
                assert(filled_cache_pages(pre_cache)
                    .contains_key(addr));
            }
            Cache::Step::writeback_initiate() => {
                assert(post_cache.lookup_map
                    == pre_cache.lookup_map);
                assert(post_cache.entries == pre_cache.entries);
                assert(cache_filled_addr(pre_cache, addr));
                assert(filled_cache_pages(pre_cache)
                    .contains_key(addr));
            }
            _ => {
                assert(false);
            }
        }
    }
    assert forall |addr: Address|
        #[trigger] post.disk.content.contains_key(addr)
            && addr != spec_superblock_addr()
        implies addr.wf()
    by {
        assert(pre.disk.content.contains_key(addr));
    }
    assert forall |addr: Address| {
        &&& #[trigger] filled_cache_status(post_cache)
            .contains_key(addr)
        &&& filled_cache_status(post_cache)[addr]
            == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& post.disk.content.contains_key(addr)
    } implies {
        post.disk.content[addr]
            == cache_filled_page(post_cache, addr)
    }
    by {
        assert(cache_filled_addr(post_cache, addr));
        match step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                let updated_entries = Map::new(
                    |slot| new_slots_mapping.contains_key(slot),
                    |slot| Entry::Loading{
                        addr: new_slots_mapping[slot],
                    },
                );
                let post_slot = post_cache.lookup_map[addr];
                assert(!new_slots_mapping.invert()
                    .contains_key(addr)) by {
                    if new_slots_mapping.invert()
                        .contains_key(addr)
                    {
                        Cache::State::invert_contains_pair(
                            new_slots_mapping,
                            addr,
                        );
                        let slot =
                            new_slots_mapping.invert()[addr];
                        assert(updated_entries
                            .contains_key(slot));
                        assert(post_cache.entries[slot]
                            == Entry::Loading{addr});
                        assert(false);
                    }
                }
                assert(pre_cache.lookup_map
                    .contains_key(addr));
                assert(pre_cache.lookup_map[addr]
                    == post_slot);
                assert(!updated_entries
                    .contains_key(post_slot));
                assert(post_cache.entries[post_slot]
                    == pre_cache.entries[post_slot]);
                assert(post_cache.status_map
                    == pre_cache.status_map);
                assert(cache_filled_addr(pre_cache, addr));
                assert(filled_cache_status(pre_cache)
                    .contains_key(addr));
                assert(filled_cache_status(pre_cache)[addr]
                    == PageStatus::Clean);
                assert(cache_filled_page(post_cache, addr)
                    == cache_filled_page(pre_cache, addr));
            }
            Cache::Step::writeback_initiate() => {
                let writeback_slots = Map::new(
                    |req: DiskRequest|
                        req_map.values().contains(req),
                    |req: DiskRequest|
                        pre_cache.lookup_map[req->to],
                ).values();
                let post_slot = post_cache.lookup_map[addr];
                assert(post_cache.lookup_map
                    == pre_cache.lookup_map);
                assert(post_cache.entries == pre_cache.entries);
                assert(!writeback_slots
                    .contains(post_slot)) by {
                    if writeback_slots.contains(post_slot) {
                        let updated_status = Map::new(
                            |slot: Slot|
                                writeback_slots.contains(slot),
                            |slot: Slot| Status::Writeback{},
                        );
                        assert(updated_status
                            .contains_key(post_slot));
                        assert(post_cache.status_map[post_slot]
                            is Writeback);
                        assert(cache_status_i(post_cache, addr)
                            == PageStatus::Writeback);
                        assert(false);
                    }
                }
                let updated_status = Map::new(
                    |slot: Slot|
                        writeback_slots.contains(slot),
                    |slot: Slot| Status::Writeback{},
                );
                assert(!updated_status
                    .contains_key(post_slot));
                assert(post_cache.status_map[post_slot]
                    == pre_cache.status_map[post_slot]);
                assert(cache_filled_addr(pre_cache, addr));
                assert(filled_cache_status(pre_cache)
                    .contains_key(addr));
                assert(filled_cache_status(pre_cache)[addr]
                    == PageStatus::Clean);
                assert(cache_filled_page(post_cache, addr)
                    == cache_filled_page(pre_cache, addr));
            }
            _ => {
                assert(false);
            }
        }
        assert(pre.disk.content[addr]
            == cache_filled_page(pre_cache, addr));
    }
}

proof fn cache_io_begin_preserves_cache_request_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_betree_cache_request_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{
                requests: req_map.values(),
                responses: Map::empty(),
            },
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs
                .union_prefer_right(Map::new(
                    |id| req_map.contains_key(id),
                    |id| req_map[id].addr(),
                )),
        Map::new(
            |id| req_map.contains_key(id),
            |id| req_map[id].addr(),
        ).is_injective(),
        !Map::new(
            |id| req_map.contains_key(id),
            |id| req_map[id].addr(),
        ).contains_value(spec_superblock_addr()),
    ensures
        unified_cache_betree_cache_request_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let updated = Map::new(
        |id| req_map.contains_key(id),
        |id| req_map[id].addr(),
    );
    let new_outstanding =
        pre_state.outstanding_cache_reqs
            .union_prefer_right(updated);
    let cache_lbl = Cache::Label::DiskOps{
        requests: req_map.values(),
        responses: Map::<Address, DiskResponse>::empty(),
    };

    Cache::State::inv_next(
        pre_state.cache,
        post_state.cache,
        cache_lbl,
    );
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();
    assert(pre_state.cache.build_lookup_map_props(
        pre_state.cache.lookup_map,
    ));
    assert(post_state.cache.build_lookup_map_props(
        post_state.cache.lookup_map,
    ));
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre_state.cache,
            post_state.cache,
            cache_lbl,
            step,
        );

    assert forall |addr: Address|
        #[trigger] updated.values().contains(addr)
        implies !pre_state.outstanding_cache_reqs
            .values().contains(addr)
    by {
        let new_id = choose |id: ID|
            #[trigger] updated.contains_key(id)
                && updated[id] == addr;
        let req = req_map[new_id];
        assert(req.addr() == addr);
        if pre_state.outstanding_cache_reqs
            .values().contains(addr)
        {
            let old_id = choose |id: ID|
                #[trigger] pre_state.outstanding_cache_reqs
                    .contains_key(id)
                    && pre_state.outstanding_cache_reqs[id]
                        == addr;
            let old_slot = pre_state.cache.lookup_map[addr];
            assert(unified_cache_betree_cache_request_inv(pre));
            match step {
                Cache::Step::load_initiate(
                    new_slots_mapping,
                ) => {
                    assert(Cache::State::load_initiate(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                        new_slots_mapping,
                    ));
                    assert(req_map.values().contains(req));
                    assert(req is ReadReq);
                    assert(Cache::State::valid_load_requests(
                        req_map.values(),
                        new_slots_mapping,
                    ));
                    assert(crate::implementation::Cache_v::
                        addr_maps_to_req(
                            req_map.values(),
                            req,
                            addr,
                        ));
                    assert(exists |r: DiskRequest|
                        crate::implementation::Cache_v::
                            addr_maps_to_req(
                                req_map.values(),
                                r,
                                addr,
                            ));
                    assert(new_slots_mapping
                        .contains_value(addr));
                    assert(pre_state.cache.lookup_map
                        .contains_key(addr));
                    assert(new_slots_mapping.values()
                        .disjoint(
                            pre_state.cache.lookup_map.dom(),
                        ));
                    assert(false);
                }
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                    ));
                    assert(req_map.values().contains(req));
                    assert(req is WriteReq);
                    assert(pre_state.cache
                        .valid_writeback_requests(
                            req_map.values(),
                        ));
                    assert(pre_state.cache.entries[old_slot]
                        == Entry::Filled{
                            addr,
                            data: req->data,
                        });
                    assert(pre_state.cache.status_map[old_slot]
                        is Dirty);
                    assert(pre_state.cache.status_map[old_slot]
                        is Writeback);
                    assert(false);
                }
                _ => {
                    assert(false);
                }
            }
        }
    }

    assert(new_outstanding.is_injective()) by {
        assert forall |id1: ID, id2: ID|
            id1 != id2
                && new_outstanding.contains_key(id1)
                && new_outstanding.contains_key(id2)
            implies
                #[trigger] new_outstanding[id1]
                    != #[trigger] new_outstanding[id2]
        by {
            if updated.contains_key(id1)
                && updated.contains_key(id2)
            {
                assert(updated[id1] != updated[id2]);
            } else if !updated.contains_key(id1)
                && !updated.contains_key(id2)
            {
                assert(pre_state.outstanding_cache_reqs[id1]
                    != pre_state.outstanding_cache_reqs[id2]);
            } else if updated.contains_key(id1) {
                assert(updated.values()
                    .contains(updated[id1]));
                assert(!pre_state.outstanding_cache_reqs
                    .values().contains(updated[id1]));
            } else {
                assert(updated.values()
                    .contains(updated[id2]));
                assert(!pre_state.outstanding_cache_reqs
                    .values().contains(updated[id2]));
            }
        }
    }
    assert(!new_outstanding
        .contains_value(spec_superblock_addr())) by {
        if new_outstanding
            .contains_value(spec_superblock_addr())
        {
            let id = choose |id: ID|
                #[trigger] new_outstanding.contains_key(id)
                    && new_outstanding[id]
                        == spec_superblock_addr();
            if updated.contains_key(id) {
                assert(updated.contains_value(
                    spec_superblock_addr(),
                ));
            } else {
                assert(pre_state.outstanding_cache_reqs
                    .contains_value(
                        spec_superblock_addr(),
                    ));
            }
            assert(false);
        }
    }

    assert forall |id: ID|
        #[trigger] new_outstanding.contains_key(id)
        implies {
            let addr = new_outstanding[id];
            &&& post_state.cache.lookup_map
                .contains_key(addr)
            &&& {
                let slot = post_state.cache.lookup_map[addr];
                match post_state.cache.entries[slot] {
                    Entry::Loading{addr: entry_addr} =>
                        entry_addr == addr,
                    Entry::Filled{addr: entry_addr, ..} =>
                        entry_addr == addr
                            && post_state.cache.status_map[slot]
                                is Writeback,
                    _ => false,
                }
            }
        }
    by {
        let addr = new_outstanding[id];
        if updated.contains_key(id) {
            let req = req_map[id];
            assert(req.addr() == addr);
            match step {
                Cache::Step::load_initiate(
                    new_slots_mapping,
                ) => {
                    assert(Cache::State::load_initiate(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                        new_slots_mapping,
                    ));
                    assert(req_map.values().contains(req));
                    assert(req is ReadReq);
                    assert(Cache::State::valid_load_requests(
                        req_map.values(),
                        new_slots_mapping,
                    ));
                    assert(crate::implementation::Cache_v::
                        addr_maps_to_req(
                            req_map.values(),
                            req,
                            addr,
                        ));
                    assert(exists |r: DiskRequest|
                        crate::implementation::Cache_v::
                            addr_maps_to_req(
                                req_map.values(),
                                r,
                                addr,
                            ));
                    assert(new_slots_mapping
                        .contains_value(addr));
                    Cache::State::invert_contains_pair(
                        new_slots_mapping,
                        addr,
                    );
                    let slot =
                        new_slots_mapping.invert()[addr];
                    assert(new_slots_mapping
                        .contains_pair(slot, addr));
                    assert(post_state.cache.lookup_map[addr]
                        == slot);
                    assert(post_state.cache.entries[slot]
                        == Entry::Loading{addr});
                }
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                    ));
                    assert(req_map.values().contains(req));
                    assert(req is WriteReq);
                    assert(pre_state.cache
                        .valid_writeback_requests(
                            req_map.values(),
                        ));
                    let slot = pre_state.cache.lookup_map[addr];
                    assert(post_state.cache.lookup_map
                        == pre_state.cache.lookup_map);
                    assert(post_state.cache.entries[slot]
                        == Entry::Filled{
                            addr,
                            data: req->data,
                        });
                    let writeback_slots = Map::new(
                        |r: DiskRequest|
                            req_map.values().contains(r),
                        |r: DiskRequest|
                            pre_state.cache.lookup_map[r->to],
                    ).values();
                    let writeback_slot_map = Map::new(
                        |r: DiskRequest|
                            req_map.values().contains(r),
                        |r: DiskRequest|
                            pre_state.cache.lookup_map[r->to],
                    );
                    assert(writeback_slot_map
                        .contains_key(req));
                    assert(writeback_slot_map[req] == slot);
                    assert(writeback_slots.contains(slot));
                    assert(post_state.cache.status_map[slot]
                        is Writeback);
                }
                _ => {
                    assert(false);
                }
            }
        } else {
            assert(pre_state.outstanding_cache_reqs
                .contains_key(id));
            assert(pre_state.outstanding_cache_reqs[id]
                == addr);
            assert(unified_cache_betree_cache_request_inv(pre));
            assert(pre_state.cache.lookup_map
                .contains_key(addr));
            let pre_slot =
                pre_state.cache.lookup_map[addr];
            assert(pre_state.cache.entries
                .contains_key(pre_slot)) by {
                assert(pre_state.cache.build_lookup_map_props(
                    pre_state.cache.lookup_map,
                ));
            }
            assert(pre_state.cache.status_map.dom()
                =~= pre_state.cache.entries.dom());
            assert(pre_state.cache.status_map
                .contains_key(pre_slot));
            assert(!updated.values().contains(addr));
            match step {
                Cache::Step::load_initiate(
                    new_slots_mapping,
                ) => {
                    assert(Cache::State::load_initiate(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                        new_slots_mapping,
                    ));
                    assert(!new_slots_mapping
                        .contains_value(addr)) by {
                        if new_slots_mapping
                            .contains_value(addr)
                        {
                            let req = choose |req: DiskRequest|
                                crate::implementation::Cache_v::
                                    addr_maps_to_req(
                                        req_map.values(),
                                        req,
                                        addr,
                                    );
                            let new_id = choose |new_id: ID|
                                #[trigger] req_map
                                    .contains_key(new_id)
                                    && req_map[new_id] == req;
                            assert(updated.contains_key(new_id));
                            assert(updated[new_id] == addr);
                            assert(false);
                        }
                    }
                    assert(!new_slots_mapping
                        .contains_key(pre_slot)) by {
                        if new_slots_mapping
                            .contains_key(pre_slot)
                        {
                            assert(pre_state.cache
                                .valid_new_slots_mapping(
                                    new_slots_mapping,
                                ));
                            assert(pre_state.cache.entries[pre_slot]
                                is Empty);
                            assert(false);
                        }
                    }
                    let updated_entries = Map::new(
                        |slot: Slot|
                            new_slots_mapping.contains_key(slot),
                        |slot: Slot| Entry::Loading{
                            addr: new_slots_mapping[slot],
                        },
                    );
                    assert(!updated_entries
                        .contains_key(pre_slot));
                    assert(post_state.cache.entries
                        == pre_state.cache.entries
                            .union_prefer_right(
                                updated_entries,
                            ));
                    assert(post_state.cache.lookup_map[addr]
                        == pre_slot);
                    assert(pre_state.cache.entries
                        .contains_key(pre_slot));
                    assert(post_state.cache.entries
                        .contains_key(pre_slot));
                    assert(post_state.cache.entries[pre_slot]
                        == pre_state.cache.entries
                            .union_prefer_right(
                                updated_entries,
                            )[pre_slot]);
                    assert(pre_state.cache.entries
                        .union_prefer_right(
                            updated_entries,
                        )[pre_slot]
                        == pre_state.cache.entries[pre_slot]);
                    assert(post_state.cache.entries[pre_slot]
                        == pre_state.cache.entries[pre_slot]);
                    assert(post_state.cache.status_map[pre_slot]
                        == pre_state.cache.status_map[pre_slot]);
                }
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(
                        pre_state.cache,
                        post_state.cache,
                        cache_lbl,
                    ));
                    assert(post_state.cache.lookup_map
                        == pre_state.cache.lookup_map);
                    assert(post_state.cache.entries
                        == pre_state.cache.entries);
                    let writeback_slots = Map::new(
                        |r: DiskRequest|
                            req_map.values().contains(r),
                        |r: DiskRequest|
                            pre_state.cache.lookup_map[r->to],
                    ).values();
                    assert(!writeback_slots
                        .contains(pre_slot)) by {
                        if writeback_slots.contains(pre_slot) {
                            let req = choose |req: DiskRequest|
                                #[trigger] req_map.values()
                                    .contains(req)
                                    && pre_state.cache.lookup_map[
                                        req->to
                                    ] == pre_slot;
                            let new_id = choose |new_id: ID|
                                #[trigger] req_map
                                    .contains_key(new_id)
                                    && req_map[new_id] == req;
                            assert(updated.contains_key(new_id));
                            assert(updated[new_id] == addr);
                            assert(false);
                        }
                    }
                    let updated_status = Map::new(
                        |slot: Slot|
                            writeback_slots.contains(slot),
                        |slot: Slot| Status::Writeback{},
                    );
                    assert(!updated_status
                        .contains_key(pre_slot));
                    assert(post_state.cache.status_map
                        == pre_state.cache.status_map
                            .union_prefer_right(
                                updated_status,
                            ));
                    assert(pre_state.cache.status_map
                        .contains_key(pre_slot));
                    assert(post_state.cache.status_map
                        .contains_key(pre_slot));
                    assert(post_state.cache.status_map[pre_slot]
                        == pre_state.cache.status_map
                            .union_prefer_right(
                                updated_status,
                            )[pre_slot]);
                    assert(pre_state.cache.status_map
                        .union_prefer_right(
                            updated_status,
                        )[pre_slot]
                        == pre_state.cache.status_map[pre_slot]);
                    assert(post_state.cache.status_map[pre_slot]
                        == pre_state.cache.status_map[pre_slot]);
                }
                _ => {
                    assert(false);
                }
            }
        }
    }
    assert(new_outstanding.values()
        <= post_state.cache.lookup_map.dom());
    assert(unified_cache_betree_cache_request_inv(post));
}

proof fn cache_io_begin_preserves_protocol_invs(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        refinement_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{
                requests: req_map.values(),
                responses: Map::empty(),
            },
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs
                .union_prefer_right(Map::new(
                    |id| req_map.contains_key(id),
                    |id| req_map[id].addr(),
                )),
        Map::new(
            |id| req_map.contains_key(id),
            |id| req_map[id].addr(),
        ).is_injective(),
        !Map::new(
            |id| req_map.contains_key(id),
            |id| req_map[id].addr(),
        ).contains_value(spec_superblock_addr()),
        post.disk.requests
            == pre.disk.requests.union_prefer_right(req_map),
        post.disk.responses == pre.disk.responses,
        post.disk.content == pre.disk.content,
        req_map.dom().disjoint(pre.disk.requests.dom()),
        req_map.dom().disjoint(pre.disk.responses.dom()),
    ensures
        unified_cache_betree_cache_request_inv(post),
        unified_cache_betree_outstanding_io_inv(post),
        unified_cache_betree_cache_response_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let updated = Map::new(
        |id| req_map.contains_key(id),
        |id| req_map[id].addr(),
    );
    let cache_lbl = Cache::Label::DiskOps{
        requests: req_map.values(),
        responses: Map::<Address, DiskResponse>::empty(),
    };

    cache_io_begin_preserves_cache_request_inv(
        pre,
        post,
        req_map,
    );
    Cache::State::inv_next(
        pre_state.cache,
        post_state.cache,
        cache_lbl,
    );
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();
    assert(post_state.outstanding_cache_reqs.is_injective());

    assert forall |id: ID|
        #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        implies disk_has_pending_id(post.disk, id)
    by {
        if updated.contains_key(id) {
            assert(req_map.contains_key(id));
            assert(post.disk.requests.contains_key(id));
        } else {
            assert(pre_state.outstanding_cache_reqs
                .contains_key(id));
            assert(disk_has_pending_id(pre.disk, id));
            if pre.disk.requests.contains_key(id) {
                assert(post.disk.requests.contains_key(id));
            } else {
                assert(pre.disk.responses.contains_key(id));
                assert(post.disk.responses.contains_key(id));
            }
        }
    }

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre_state.cache,
            post_state.cache,
            cache_lbl,
            step,
        );
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map
                .contains_key(addr)
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ] is Filled
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ]->data == req->data
            &&& post_state.cache.status_map[
                post_state.cache.lookup_map[addr]
            ] == Status::Writeback{}
        }
    } by {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        if updated.contains_key(id) {
            assert(req_map.contains_key(id));
            assert(post_state.outstanding_cache_reqs[id]
                == updated[id]);
            assert(post.disk.requests[id] == req_map[id]);
            assert(req.addr() == addr);
            if req is WriteReq {
                match cache_step {
                    Cache::Step::writeback_initiate() => {
                        assert(Cache::State::
                            writeback_initiate(
                                pre_state.cache,
                                post_state.cache,
                                cache_lbl,
                            ));
                        assert(pre_state.cache
                            .valid_writeback_requests(
                                req_map.values(),
                            ));
                        assert(req_map.values().contains(req));
                        let slot =
                            pre_state.cache.lookup_map[addr];
                        assert(pre_state.cache.entries[slot]
                            == Entry::Filled{
                                addr,
                                data: req->data,
                            });
                        assert(post_state.cache.lookup_map
                            == pre_state.cache.lookup_map);
                        assert(post_state.cache.entries
                            == pre_state.cache.entries);
                        assert(unified_cache_betree_cache_request_inv(
                            post,
                        ));
                    }
                    Cache::Step::load_initiate(
                        new_slots_mapping,
                    ) => {
                        assert(Cache::State::load_initiate(
                            pre_state.cache,
                            post_state.cache,
                            cache_lbl,
                            new_slots_mapping,
                        ));
                        assert(Cache::State::valid_load_requests(
                            req_map.values(),
                            new_slots_mapping,
                        ));
                        assert(req_map.values().contains(req));
                        assert(req is ReadReq);
                        assert(false);
                    }
                    _ => {
                        assert(false);
                    }
                }
            }
        } else {
            assert(pre_state.outstanding_cache_reqs
                .contains_key(id));
            assert(!req_map.contains_key(id)) by {
                if req_map.contains_key(id) {
                    assert(disk_has_pending_id(pre.disk, id));
                    if pre.disk.requests.contains_key(id) {
                        assert(req_map.dom().disjoint(
                            pre.disk.requests.dom(),
                        ));
                    } else {
                        assert(pre.disk.responses
                            .contains_key(id));
                        assert(req_map.dom().disjoint(
                            pre.disk.responses.dom(),
                        ));
                    }
                    assert(false);
                }
            }
            assert(pre.disk.requests.contains_key(id));
            assert(post.disk.requests[id]
                == pre.disk.requests[id]);
            assert(req == pre.disk.requests[id]);
            assert(pre_state.outstanding_cache_reqs[id]
                == addr);
            assert(req.addr() == addr);
            if req is WriteReq {
                assert(cache_filled_addr(
                    pre_state.cache,
                    addr,
                ));
                cache_disk_ops_begin_preserves_filled_page(
                    pre_state.cache,
                    post_state.cache,
                    req_map.values(),
                    addr,
                );
                assert(unified_cache_betree_cache_request_inv(
                    post,
                ));
            }
        }
    }
    assert(unified_cache_betree_outstanding_io_inv(post));

    assert forall |id: ID| {
        &&& #[trigger] post.disk.responses.contains_key(id)
        &&& post_state.outstanding_cache_reqs.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let resp = post.disk.responses[id];
        &&& addr.wf()
        &&& resp is ReadResp ==> {
            resp->data == post.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& cache_filled_addr(post_state.cache, addr)
            &&& post.disk.content[addr]
                == cache_filled_page(post_state.cache, addr)
        }
    } by {
        assert(pre.disk.responses.contains_key(id));
        assert(!req_map.contains_key(id));
        assert(pre_state.outstanding_cache_reqs
            .contains_key(id));
        let addr = pre_state.outstanding_cache_reqs[id];
        assert(post_state.outstanding_cache_reqs[id]
            == addr);
        assert(post.disk.responses[id]
            == pre.disk.responses[id]);
        assert(unified_cache_betree_cache_response_inv(pre));
        if pre.disk.responses[id] is WriteResp {
            cache_disk_ops_begin_preserves_filled_page(
                pre_state.cache,
                post_state.cache,
                req_map.values(),
                addr,
            );
        }
    }
    assert(unified_cache_betree_cache_response_inv(post));
}

proof fn cache_io_end_preserves_shared_cache_disk_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_betree_shared_cache_disk_inv(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{
                requests: Set::empty(),
                responses: cache_resps,
            },
        ),
        post.disk.content == pre.disk.content,
        !cache_resps.contains_key(spec_superblock_addr()),
        cache_resps.dom()
            <= Set::new(|addr: Address| addr.wf()),
        forall |addr: Address|
            #[trigger] cache_resps.contains_key(addr)
            ==> {
                &&& cache_resps[addr] is ReadResp ==> {
                    pre.disk.content.contains_key(addr)
                        ==> cache_resps[addr]->data
                            == pre.disk.content[addr]
                }
                &&& cache_resps[addr] is WriteResp ==> {
                    &&& pre.disk.content.contains_key(addr)
                    &&& cache_filled_addr(
                        pre.program.state.cache,
                        addr,
                    )
                    &&& pre.disk.content[addr]
                        == cache_filled_page(
                            pre.program.state.cache,
                            addr,
                        )
                }
            },
    ensures
        unified_cache_betree_shared_cache_disk_inv(post),
{
    let pre_cache = pre.program.state.cache;
    let post_cache = post.program.state.cache;
    let cache_lbl = Cache::Label::DiskOps{
        requests: Set::empty(),
        responses: cache_resps,
    };
    Cache::State::inv_next(
        pre_cache,
        post_cache,
        cache_lbl,
    );
    pre_cache.build_lookup_map_ensures();
    post_cache.build_lookup_map_ensures();

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre_cache,
            post_cache,
            cache_lbl,
            step,
        );
    match step {
        Cache::Step::load_complete() => {
            assert(Cache::State::load_complete(
                pre_cache,
                post_cache,
                cache_lbl,
            )) by {
                reveal(Cache::State::load_complete);
            }
        }
        Cache::Step::writeback_complete() => {
            assert(Cache::State::writeback_complete(
                pre_cache,
                post_cache,
                cache_lbl,
            )) by {
                reveal(Cache::State::writeback_complete);
            }
        }
        _ => {
            assert(false);
        }
    }

    assert forall |addr: Address|
        #[trigger] filled_cache_pages(post_cache)
            .contains_key(addr)
        implies addr.wf()
    by {
        assert(cache_filled_addr(post_cache, addr));
        match step {
            Cache::Step::load_complete() => {
                if cache_resps.contains_key(addr) {
                    assert(addr.wf());
                } else {
                    let slot = post_cache.lookup_map[addr];
                    let slot_addr_map =
                        pre_cache.lookup_map
                            .restrict(cache_resps.dom())
                            .invert();
                    let updated_entries = Map::new(
                        |s| slot_addr_map.contains_key(s),
                        |s| Entry::Filled{
                            addr: slot_addr_map[s],
                            data:
                                cache_resps[
                                    slot_addr_map[s]
                                ]->data,
                        },
                    );
                    assert(post_cache.lookup_map
                        == pre_cache.lookup_map);
                    assert(!slot_addr_map.contains_key(slot)) by {
                        if slot_addr_map.contains_key(slot) {
                            assert(slot_addr_map[slot] == addr);
                            assert(cache_resps.contains_key(addr));
                            assert(false);
                        }
                    }
                    assert(!updated_entries.contains_key(slot));
                    assert(post_cache.entries[slot]
                        == pre_cache.entries[slot]);
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(filled_cache_pages(pre_cache)
                        .contains_key(addr));
                }
            }
            Cache::Step::writeback_complete() => {
                assert(post_cache.lookup_map
                    == pre_cache.lookup_map);
                assert(post_cache.entries == pre_cache.entries);
                assert(cache_filled_addr(pre_cache, addr));
                assert(filled_cache_pages(pre_cache)
                    .contains_key(addr));
            }
            _ => {
                assert(false);
            }
        }
    }
    assert forall |addr: Address|
        #[trigger] post.disk.content.contains_key(addr)
            && addr != spec_superblock_addr()
        implies addr.wf()
    by {
        assert(pre.disk.content.contains_key(addr));
    }
    assert forall |addr: Address| {
        &&& #[trigger] filled_cache_status(post_cache)
            .contains_key(addr)
        &&& filled_cache_status(post_cache)[addr]
            == PageStatus::Clean
        &&& addr != spec_superblock_addr()
        &&& post.disk.content.contains_key(addr)
    } implies {
        post.disk.content[addr]
            == cache_filled_page(post_cache, addr)
    }
    by {
        assert(cache_filled_addr(post_cache, addr));
        match step {
            Cache::Step::load_complete() => {
                if cache_resps.contains_key(addr) {
                    assert(cache_resps[addr] is ReadResp);
                    assert(pre.disk.content.contains_key(addr));
                    let slot = post_cache.lookup_map[addr];
                    let slot_addr_map =
                        pre_cache.lookup_map
                            .restrict(cache_resps.dom())
                            .invert();
                    assert(slot_addr_map.contains_key(slot)) by {
                        if !slot_addr_map.contains_key(slot) {
                            let updated_status = Map::new(
                                |s: Slot|
                                    slot_addr_map.contains_key(s),
                                |s: Slot| Status::Clean,
                            );
                            assert(post_cache.status_map[slot]
                                == pre_cache.status_map[slot]);
                            assert(pre_cache
                                .valid_load_responses(
                                    cache_resps,
                                ));
                            assert(pre_cache.entries[slot]
                                is Loading);
                            assert(false);
                        }
                    }
                    assert(slot_addr_map[slot] == addr);
                    let updated_entries = Map::new(
                        |s| slot_addr_map.contains_key(s),
                        |s| Entry::Filled{
                            addr: slot_addr_map[s],
                            data:
                                cache_resps[
                                    slot_addr_map[s]
                                ]->data,
                        },
                    );
                    assert(updated_entries.contains_key(slot));
                    assert(post_cache.entries[slot]
                        == Entry::Filled{
                            addr,
                            data: cache_resps[addr]->data,
                        });
                    assert(cache_filled_page(post_cache, addr)
                        == cache_resps[addr]->data);
                } else {
                    let slot = post_cache.lookup_map[addr];
                    let slot_addr_map =
                        pre_cache.lookup_map
                            .restrict(cache_resps.dom())
                            .invert();
                    let updated_entries = Map::new(
                        |s| slot_addr_map.contains_key(s),
                        |s| Entry::Filled{
                            addr: slot_addr_map[s],
                            data:
                                cache_resps[
                                    slot_addr_map[s]
                                ]->data,
                        },
                    );
                    let updated_status = Map::new(
                        |s: Slot|
                            slot_addr_map.contains_key(s),
                        |s: Slot| Status::Clean,
                    );
                    assert(post_cache.lookup_map
                        == pre_cache.lookup_map);
                    assert(!slot_addr_map.contains_key(slot)) by {
                        if slot_addr_map.contains_key(slot) {
                            assert(slot_addr_map[slot] == addr);
                            assert(cache_resps.contains_key(addr));
                            assert(false);
                        }
                    }
                    assert(!updated_entries.contains_key(slot));
                    assert(!updated_status.contains_key(slot));
                    assert(post_cache.entries[slot]
                        == pre_cache.entries[slot]);
                    assert(post_cache.status_map[slot]
                        == pre_cache.status_map[slot]);
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(filled_cache_status(pre_cache)
                        .contains_key(addr));
                    assert(filled_cache_status(pre_cache)[addr]
                        == PageStatus::Clean);
                    assert(cache_filled_page(post_cache, addr)
                        == cache_filled_page(pre_cache, addr));
                }
            }
            Cache::Step::writeback_complete() => {
                assert(post_cache.lookup_map
                    == pre_cache.lookup_map);
                assert(post_cache.entries == pre_cache.entries);
                if cache_resps.contains_key(addr) {
                    assert(cache_resps[addr] is WriteResp);
                    assert(pre.disk.content.contains_key(addr));
                    cache_disk_ops_end_preserves_filled_page(
                        pre_cache,
                        post_cache,
                        cache_resps,
                        addr,
                    );
                } else {
                    let slot = post_cache.lookup_map[addr];
                    let response_slots =
                        pre_cache.lookup_map
                            .restrict(cache_resps.dom())
                            .values();
                    let updated_status = Map::new(
                        |s: Slot|
                            response_slots.contains(s),
                        |s: Slot| Status::Clean,
                    );
                    assert(!response_slots.contains(slot)) by {
                        if response_slots.contains(slot) {
                            let response_addr =
                                choose |response_addr: Address|
                                    #[trigger] cache_resps
                                        .contains_key(
                                            response_addr,
                                        )
                                        && pre_cache.lookup_map[
                                            response_addr
                                        ] == slot;
                            assert(pre_cache.lookup_map[
                                response_addr
                            ] == pre_cache.lookup_map[addr]);
                            assert(response_addr == addr);
                            assert(false);
                        }
                    }
                    assert(!updated_status.contains_key(slot));
                    assert(post_cache.status_map[slot]
                        == pre_cache.status_map[slot]);
                    assert(cache_filled_addr(pre_cache, addr));
                    assert(filled_cache_status(pre_cache)
                        .contains_key(addr));
                    assert(filled_cache_status(pre_cache)[addr]
                        == PageStatus::Clean);
                    assert(cache_filled_page(post_cache, addr)
                        == cache_filled_page(pre_cache, addr));
                }
            }
            _ => {
                assert(false);
            }
        }
    }
}

proof fn cache_io_end_preserves_cache_request_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    resp_map: Map<ID, DiskResponse>,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        pre.program.state.cache.inv(),
        unified_cache_betree_cache_request_inv(pre),
        resp_map.dom()
            <= pre.program.state.outstanding_cache_reqs.dom(),
        cache_resps == Map::new(
            |addr|
                pre.program.state.outstanding_cache_reqs
                    .restrict(resp_map.dom())
                    .invert()
                    .contains_key(addr),
            |addr|
                resp_map[
                    pre.program.state.outstanding_cache_reqs
                        .restrict(resp_map.dom())
                        .invert()[addr]
                ],
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs
                .remove_keys(resp_map.dom()),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{
                requests: Set::empty(),
                responses: cache_resps,
            },
        ),
    ensures
        unified_cache_betree_cache_request_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let new_outstanding =
        pre_state.outstanding_cache_reqs
            .remove_keys(resp_map.dom());
    let restricted =
        pre_state.outstanding_cache_reqs
            .restrict(resp_map.dom());
    let finished = restricted.invert();
    let cache_lbl = Cache::Label::DiskOps{
        requests: Set::empty(),
        responses: cache_resps,
    };

    Cache::State::inv_next(
        pre_state.cache,
        post_state.cache,
        cache_lbl,
    );
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre_state.cache,
            post_state.cache,
            cache_lbl,
            step,
        );

    assert(new_outstanding.is_injective());
    assert(!new_outstanding
        .contains_value(spec_superblock_addr()));
    assert forall |id: ID|
        #[trigger] new_outstanding.contains_key(id)
        implies {
            let addr = new_outstanding[id];
            &&& post_state.cache.lookup_map
                .contains_key(addr)
            &&& {
                let slot = post_state.cache.lookup_map[addr];
                match post_state.cache.entries[slot] {
                    Entry::Loading{addr: entry_addr} =>
                        entry_addr == addr,
                    Entry::Filled{addr: entry_addr, ..} =>
                        entry_addr == addr
                            && post_state.cache.status_map[slot]
                                is Writeback,
                    _ => false,
                }
            }
        }
    by {
        assert(pre_state.outstanding_cache_reqs
            .contains_key(id));
        assert(!resp_map.contains_key(id));
        let addr = new_outstanding[id];
        assert(pre_state.outstanding_cache_reqs[id]
            == addr);
        assert(unified_cache_betree_cache_request_inv(pre));
        assert(!cache_resps.contains_key(addr)) by {
            if cache_resps.contains_key(addr) {
                assert(finished.contains_key(addr));
                Cache::State::invert_contains_pair(
                    restricted,
                    addr,
                );
                let finished_id = finished[addr];
                assert(restricted.contains_pair(
                    finished_id,
                    addr,
                ));
                assert(pre_state.outstanding_cache_reqs[
                    finished_id
                ] == addr);
                assert(pre_state.outstanding_cache_reqs
                    .is_injective());
                assert(finished_id == id);
                assert(resp_map.contains_key(id));
                assert(false);
            }
        }
        let pre_slot = pre_state.cache.lookup_map[addr];
        assert(pre_state.cache.lookup_map.contains_key(addr));
        assert(pre_state.cache.build_lookup_map_props(
            pre_state.cache.lookup_map,
        ));
        assert(pre_state.cache.entries
            .contains_key(pre_slot));
        assert(pre_state.cache.status_map.dom()
            =~= pre_state.cache.entries.dom());
        assert(pre_state.cache.status_map
            .contains_key(pre_slot));
        match step {
            Cache::Step::load_complete() => {
                assert(Cache::State::load_complete(
                    pre_state.cache,
                    post_state.cache,
                    cache_lbl,
                ));
                let slot_addr_map =
                    pre_state.cache.lookup_map
                        .restrict(cache_resps.dom())
                        .invert();
                let updated_entries = Map::new(
                    |slot: Slot|
                        slot_addr_map.contains_key(slot),
                    |slot: Slot| Entry::Filled{
                        addr: slot_addr_map[slot],
                        data:
                            cache_resps[
                                slot_addr_map[slot]
                            ]->data,
                    },
                );
                let updated_status = Map::new(
                    |slot: Slot|
                        slot_addr_map.contains_key(slot),
                    |slot: Slot| Status::Clean,
                );
                assert(post_state.cache.lookup_map
                    == pre_state.cache.lookup_map);
                assert(!slot_addr_map
                    .contains_key(pre_slot)) by {
                    if slot_addr_map.contains_key(pre_slot) {
                        let response_addr =
                            slot_addr_map[pre_slot];
                        assert(cache_resps
                            .contains_key(response_addr));
                        assert(pre_state.cache.lookup_map[
                            response_addr
                        ] == pre_slot);
                        assert(pre_state.cache.lookup_map[
                            response_addr
                        ] == pre_state.cache.lookup_map[addr]);
                        assert(response_addr == addr);
                        assert(false);
                    }
                }
                assert(!updated_entries
                    .contains_key(pre_slot));
                assert(!updated_status
                    .contains_key(pre_slot));
                assert(post_state.cache.entries
                    == pre_state.cache.entries
                        .union_prefer_right(updated_entries));
                assert(post_state.cache.status_map
                    == pre_state.cache.status_map
                        .union_prefer_right(updated_status));
                assert(post_state.cache.entries[pre_slot]
                    == pre_state.cache.entries
                        .union_prefer_right(
                            updated_entries,
                        )[pre_slot]);
                assert(pre_state.cache.entries
                    .union_prefer_right(
                        updated_entries,
                    )[pre_slot]
                    == pre_state.cache.entries[pre_slot]);
                assert(post_state.cache.status_map[pre_slot]
                    == pre_state.cache.status_map
                        .union_prefer_right(
                            updated_status,
                        )[pre_slot]);
                assert(pre_state.cache.status_map
                    .union_prefer_right(
                        updated_status,
                    )[pre_slot]
                    == pre_state.cache.status_map[pre_slot]);
                assert(post_state.cache.entries[pre_slot]
                    == pre_state.cache.entries[pre_slot]);
                assert(post_state.cache.status_map[pre_slot]
                    == pre_state.cache.status_map[pre_slot]);
            }
            Cache::Step::writeback_complete() => {
                assert(Cache::State::writeback_complete(
                    pre_state.cache,
                    post_state.cache,
                    cache_lbl,
                ));
                let response_slots =
                    pre_state.cache.lookup_map
                        .restrict(cache_resps.dom())
                        .values();
                let updated_status = Map::new(
                    |slot: Slot|
                        response_slots.contains(slot),
                    |slot: Slot| Status::Clean,
                );
                assert(post_state.cache.lookup_map
                    == pre_state.cache.lookup_map);
                assert(post_state.cache.entries
                    == pre_state.cache.entries);
                assert(!response_slots
                    .contains(pre_slot)) by {
                    if response_slots.contains(pre_slot) {
                        let response_addr =
                            choose |response_addr: Address|
                                #[trigger] cache_resps
                                    .contains_key(response_addr)
                                    && pre_state.cache.lookup_map[
                                        response_addr
                                    ] == pre_slot;
                        assert(pre_state.cache.lookup_map[
                            response_addr
                        ] == pre_state.cache.lookup_map[addr]);
                        assert(response_addr == addr);
                        assert(false);
                    }
                }
                assert(!updated_status
                    .contains_key(pre_slot));
                assert(post_state.cache.status_map
                    == pre_state.cache.status_map
                        .union_prefer_right(updated_status));
                assert(post_state.cache.status_map[pre_slot]
                    == pre_state.cache.status_map
                        .union_prefer_right(
                            updated_status,
                        )[pre_slot]);
                assert(pre_state.cache.status_map
                    .union_prefer_right(
                        updated_status,
                    )[pre_slot]
                    == pre_state.cache.status_map[pre_slot]);
                assert(post_state.cache.status_map[pre_slot]
                    == pre_state.cache.status_map[pre_slot]);
            }
            _ => {
                assert(false);
            }
        }
    }
    assert(new_outstanding.values()
        <= post_state.cache.lookup_map.dom()) by {
        assert forall |addr: Address|
            #[trigger] new_outstanding.values()
                .contains(addr)
            implies post_state.cache.lookup_map
                .contains_key(addr)
        by {
            let id = choose |id: ID|
                #[trigger] new_outstanding
                    .contains_key(id)
                    && new_outstanding[id] == addr;
            assert(new_outstanding.contains_key(id));
        }
    }
    assert(unified_cache_betree_cache_request_inv(post));
}

proof fn cache_io_end_preserves_protocol_invs(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    resp_map: Map<ID, DiskResponse>,
    cache_resps: Map<Address, DiskResponse>,
)
    requires
        refinement_inv(pre),
        resp_map.dom()
            <= pre.program.state.outstanding_cache_reqs.dom(),
        cache_resps == Map::new(
            |addr|
                pre.program.state.outstanding_cache_reqs
                    .restrict(resp_map.dom())
                    .invert()
                    .contains_key(addr),
            |addr|
                resp_map[
                    pre.program.state.outstanding_cache_reqs
                        .restrict(resp_map.dom())
                        .invert()[addr]
                ],
        ),
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs
                .remove_keys(resp_map.dom()),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{
                requests: Set::empty(),
                responses: cache_resps,
            },
        ),
        post.disk.requests == pre.disk.requests,
        post.disk.responses
            == pre.disk.responses.remove_keys(resp_map.dom()),
        post.disk.content == pre.disk.content,
    ensures
        unified_cache_betree_cache_request_inv(post),
        unified_cache_betree_outstanding_io_inv(post),
        unified_cache_betree_cache_response_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;

    cache_io_end_preserves_cache_request_inv(
        pre,
        post,
        resp_map,
        cache_resps,
    );
    Cache::State::inv_next(
        pre_state.cache,
        post_state.cache,
        Cache::Label::DiskOps{
            requests: Set::empty(),
            responses: cache_resps,
        },
    );
    pre_state.cache.build_lookup_map_ensures();
    post_state.cache.build_lookup_map_ensures();

    assert(post_state.outstanding_cache_reqs.is_injective());
    assert forall |id: ID|
        #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        implies disk_has_pending_id(post.disk, id)
    by {
        assert(pre_state.outstanding_cache_reqs
            .contains_key(id));
        assert(!resp_map.contains_key(id));
        assert(disk_has_pending_id(pre.disk, id));
        if pre.disk.requests.contains_key(id) {
            assert(post.disk.requests.contains_key(id));
        } else {
            assert(pre.disk.responses.contains_key(id));
            assert(post.disk.responses.contains_key(id));
        }
    }
    assert forall |id: ID| {
        &&& #[trigger] post_state.outstanding_cache_reqs
            .contains_key(id)
        &&& post.disk.requests.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let req = post.disk.requests[id];
        &&& req.addr() == addr
        &&& req is WriteReq ==> {
            &&& post_state.cache.lookup_map
                .contains_key(addr)
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ] is Filled
            &&& post_state.cache.entries[
                post_state.cache.lookup_map[addr]
            ]->data == req->data
            &&& post_state.cache.status_map[
                post_state.cache.lookup_map[addr]
            ] == Status::Writeback{}
        }
    } by {
        assert(pre_state.outstanding_cache_reqs
            .contains_key(id));
        assert(!resp_map.contains_key(id));
        assert(pre.disk.requests.contains_key(id));
        assert(post_state.outstanding_cache_reqs[id]
            == pre_state.outstanding_cache_reqs[id]);
        let addr = pre_state.outstanding_cache_reqs[id];
        let req = pre.disk.requests[id];
        assert(req.addr() == addr);
        if req is WriteReq {
            assert(cache_filled_addr(
                pre_state.cache,
                addr,
            ));
            cache_disk_ops_end_preserves_filled_page(
                pre_state.cache,
                post_state.cache,
                cache_resps,
                addr,
            );
            assert(unified_cache_betree_cache_request_inv(
                post,
            ));
        }
    }
    assert(unified_cache_betree_outstanding_io_inv(post));

    assert forall |id: ID| {
        &&& #[trigger] post.disk.responses.contains_key(id)
        &&& post_state.outstanding_cache_reqs.contains_key(id)
    } implies {
        let addr = post_state.outstanding_cache_reqs[id];
        let resp = post.disk.responses[id];
        &&& addr.wf()
        &&& resp is ReadResp ==> {
            resp->data == post.disk.content[addr]
        }
        &&& resp is WriteResp ==> {
            &&& post.disk.content.contains_key(addr)
            &&& cache_filled_addr(post_state.cache, addr)
            &&& post.disk.content[addr]
                == cache_filled_page(post_state.cache, addr)
        }
    } by {
        assert(!resp_map.contains_key(id));
        assert(pre.disk.responses.contains_key(id));
        assert(pre_state.outstanding_cache_reqs
            .contains_key(id));
        assert(post_state.outstanding_cache_reqs[id]
            == pre_state.outstanding_cache_reqs[id]);
        let addr = pre_state.outstanding_cache_reqs[id];
        assert(post.disk.responses[id]
            == pre.disk.responses[id]);
        assert(unified_cache_betree_cache_response_inv(pre));
        if pre.disk.responses[id] is WriteResp {
            cache_disk_ops_end_preserves_filled_page(
                pre_state.cache,
                post_state.cache,
                cache_resps,
                addr,
            );
        }
    }
    assert(unified_cache_betree_cache_response_inv(post));
}

proof fn journal_fill_shared_projection_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    aus: Set<crate::disk::GenericDisk_v::AU>,
)
    requires
        refinement_inv(model),
        model.program.state.allocation_metadata_loaded(),
        aus <= model.program.state.free_aus,
    ensures
        unified_cache_betree_journal_source(model)
            .journal_fill_aus_shared_projection_inv(aus),
{
    let state = model.program.state;
    let journal = unified_cache_betree_journal_source(model);
    let owned = journal.journal_projection_aus() + aus;
    let reserved = UnifiedCacheBetreeSystem::State::reserved_aus();
    assert(owned.disjoint(reserved)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] owned.contains(au)
            implies !reserved.contains(au)
        by {
            if aus.contains(au) {
                assert(state.free_aus.contains(au));
            }
        }
    }
    assert forall |addr: crate::disk::GenericDisk_v::Address| {
        &&& #[trigger] filled_cache_status(state.cache)
            .contains_key(addr)
        &&& filled_cache_status(state.cache)[addr]
            == PageStatus::Clean
        &&& addresses_in_aus(owned).contains(addr)
        &&& project_persistent(model.disk, owned)
            .contains_key(addr)
    } implies model.disk.content[addr]
        == cache_filled_page(state.cache, addr)
    by {
        assert(owned.contains(addr.au));
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(reserved.contains(addr.au));
                assert(false);
            }
        }
    }
    caching_disk_i_inv_from_clean_cache_coupling(
        state.cache,
        model.disk,
        owned,
    );
    assert forall |addr: crate::disk::GenericDisk_v::Address| {
        &&& #[trigger] model.disk.content.contains_key(addr)
        &&& addresses_in_aus(owned).contains(addr)
    } implies addr.wf()
    by {
        assert(owned.contains(addr.au));
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(reserved.contains(addr.au));
                assert(false);
            }
        }
    }
    caching_disk_i_domains_wf_from_sources(
        state.cache,
        model.disk,
        owned,
    );
}

proof fn branch_alloc_clean_cache_disk_coupling(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
)
    requires
        refinement_inv(model),
        model.program.state.branch.control.metadata_loaded,
        allocs <= model.program.state.free_aus,
    ensures
        UnifiedCacheBranchBetreeRefinement::
            clean_cache_disk_coupling_on_aus(
                model.program.state.cache,
                model.disk,
                UnifiedCacheBranchBetreeRefinement::
                    unified_cache_branch_betree_source(model)
                        .branch_projection_aus()
                    + allocs,
            ),
{
    let state = model.program.state;
    let branch =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(model);
    let owned = branch.branch_projection_aus() + allocs;
    let reserved = UnifiedCacheBetreeSystem::State::reserved_aus();
    assert(owned.disjoint(reserved)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] owned.contains(au)
            implies !reserved.contains(au)
        by {
            if allocs.contains(au) {
                assert(state.free_aus.contains(au));
            }
        }
    }
    reveal(UnifiedCacheBranchBetreeRefinement::
        clean_cache_disk_coupling_on_aus);
    assert forall |addr: crate::disk::GenericDisk_v::Address| {
        &&& #[trigger] filled_cache_status(state.cache)
            .contains_key(addr)
        &&& filled_cache_status(state.cache)[addr]
            == PageStatus::Clean
        &&& addresses_in_aus(owned).contains(addr)
        &&& project_persistent(model.disk, owned)
            .contains_key(addr)
    } implies model.disk.content[addr]
        == cache_filled_page(state.cache, addr)
    by {
        assert(owned.contains(addr.au));
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(reserved.contains(addr.au));
                assert(false);
            }
        }
    }
}

proof fn branch_alloc_preserves_allocation_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    reclaimed: Set<crate::disk::GenericDisk_v::AU>,
)
    requires
        unified_cache_betree_allocation_inv(pre),
        pre.program.state.journal.ready(),
        pre.program.state.branch.control.metadata_loaded,
        post.program.state.journal.ready(),
        post.program.state.branch.control.metadata_loaded,
        allocs <= pre.program.state.free_aus,
        reclaimed <=
            UnifiedCacheBranchBetreeRefinement::
                unified_cache_branch_betree_source(pre)
                    .branch_projection_aus(),
        unified_cache_betree_journal_source(post)
            .journal_projection_aus()
            =~= unified_cache_betree_journal_source(pre)
                .journal_projection_aus(),
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post)
                .branch_projection_aus()
            == (
                UnifiedCacheBranchBetreeRefinement::
                    unified_cache_branch_betree_source(pre)
                        .branch_projection_aus()
                + allocs
            ) - reclaimed,
        post.program.state.free_aus
            == (pre.program.state.free_aus - allocs)
                + reclaimed,
    ensures
        unified_cache_betree_allocation_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let pre_journal =
        unified_cache_betree_journal_source(pre)
            .journal_projection_aus();
    let post_journal =
        unified_cache_betree_journal_source(post)
            .journal_projection_aus();
    let pre_branch =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre)
                .branch_projection_aus();
    let post_branch =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post)
                .branch_projection_aus();
    let reserved =
        UnifiedCacheBetreeSystem::State::reserved_aus();
    let remaining_free = pre_state.free_aus - allocs;

    assert(allocs.disjoint(pre_journal)) by {
        assert(pre_state.free_aus.disjoint(pre_journal));
    }
    assert(allocs.disjoint(pre_branch)) by {
        assert(pre_state.free_aus.disjoint(pre_branch));
    }
    assert(allocs.disjoint(reserved)) by {
        assert(pre_state.free_aus.disjoint(reserved));
    }
    assert(reclaimed.disjoint(pre_journal)) by {
        assert(pre_branch.disjoint(pre_journal));
    }
    assert(reclaimed.disjoint(reserved)) by {
        assert(reserved.disjoint(pre_branch));
    }
    assert(post_branch.disjoint(post_journal)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] post_branch.contains(au)
            implies !post_journal.contains(au)
        by {
            assert((pre_branch + allocs).contains(au));
            if pre_branch.contains(au) {
                assert(!pre_journal.contains(au));
            } else {
                assert(allocs.contains(au));
                assert(!pre_journal.contains(au));
            }
        }
    }
    assert(reserved.disjoint(post_branch)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] reserved.contains(au)
            implies !post_branch.contains(au)
        by {
            if post_branch.contains(au) {
                assert((pre_branch + allocs).contains(au));
                if pre_branch.contains(au) {
                    assert(!reserved.contains(au));
                } else {
                    assert(allocs.contains(au));
                    assert(!reserved.contains(au));
                }
            }
        }
    }
    assert(remaining_free.disjoint(post_branch)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] remaining_free.contains(au)
            implies !post_branch.contains(au)
        by {
            if post_branch.contains(au) {
                assert((pre_branch + allocs).contains(au));
                if pre_branch.contains(au) {
                    assert(pre_state.free_aus.disjoint(
                        pre_branch,
                    ));
                } else {
                    assert(allocs.contains(au));
                }
            }
        }
    }
    assert(reclaimed.disjoint(post_branch)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] reclaimed.contains(au)
            implies !post_branch.contains(au)
        by {
            assert(!((
                pre_branch + allocs
            ) - reclaimed).contains(au));
        }
    }
    assert(post_state.free_aus.disjoint(post_branch)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] post_state.free_aus.contains(au)
            implies !post_branch.contains(au)
        by {
            if remaining_free.contains(au) {
                assert(!post_branch.contains(au));
            } else {
                assert(reclaimed.contains(au));
                assert(!post_branch.contains(au));
            }
        }
    }
    assert(post_state.free_aus.disjoint(post_journal)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] post_state.free_aus.contains(au)
            implies !post_journal.contains(au)
        by {
            if remaining_free.contains(au) {
                assert(pre_state.free_aus.contains(au));
                assert(!pre_journal.contains(au));
            } else {
                assert(reclaimed.contains(au));
                assert(!pre_journal.contains(au));
            }
        }
    }
    assert(post_state.free_aus.disjoint(reserved)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] post_state.free_aus.contains(au)
            implies !reserved.contains(au)
        by {
            if remaining_free.contains(au) {
                assert(pre_state.free_aus.contains(au));
            } else {
                assert(reclaimed.contains(au));
            }
        }
    }
    assert(reserved.disjoint(post_journal));
    assert(unified_cache_betree_allocation_inv(post));
}

proof fn branch_wip_update_preserves_persistent_disjoint_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
)
    requires
        refinement_inv(pre),
        post.program.state.branch.control.metadata_loaded
            == pre.program.state.branch.control.metadata_loaded,
        post.program.state.branch.control.persistent_aus
            == pre.program.state.branch.control.persistent_aus,
        cached_branch_alloc_aus(
            post.program.state.branch.betree.wip_branches,
        ) <= cached_branch_alloc_aus(
            pre.program.state.branch.betree.wip_branches,
        ) + allocs,
        allocs <= pre.program.state.free_aus,
    ensures
        unified_cache_betree_wip_persistent_disjoint_inv(
            post,
        ),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    if post_state.branch.control.metadata_loaded {
        assert(cached_branch_alloc_aus(
            pre_state.branch.betree.wip_branches,
        ).disjoint(
            pre_state.branch.control.persistent_aus,
        ));
        assert(allocs.disjoint(
            pre_state.branch.control.persistent_aus,
        )) by {
            assert(pre_state.free_aus.disjoint(
                UnifiedCacheBranchBetreeRefinement::
                    unified_cache_branch_betree_source(pre)
                        .branch_projection_aus(),
            ));
            assert(pre_state.branch.control.persistent_aus
                <= UnifiedCacheBranchBetreeRefinement::
                    unified_cache_branch_betree_source(pre)
                        .branch_projection_aus());
        }
        assert(cached_branch_alloc_aus(
            post_state.branch.betree.wip_branches,
        ).disjoint(
            post_state.branch.control.persistent_aus,
        ));
    }
}

proof fn sync_discard_preserves_allocation_inv(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    journal_discarded: Set<crate::disk::GenericDisk_v::AU>,
    branch_discarded: Set<crate::disk::GenericDisk_v::AU>,
)
    requires
        unified_cache_betree_allocation_inv(pre),
        pre.program.state.journal.ready(),
        pre.program.state.branch.control.metadata_loaded,
        post.program.state.journal.ready(),
        post.program.state.branch.control.metadata_loaded,
        journal_discarded
            <= unified_cache_betree_journal_source(pre)
                .journal_projection_aus(),
        branch_discarded
            <= UnifiedCacheBranchBetreeRefinement::
                unified_cache_branch_betree_source(pre)
                    .branch_projection_aus(),
        unified_cache_betree_journal_source(post)
            .journal_projection_aus()
            =~= unified_cache_betree_journal_source(pre)
                .journal_projection_aus()
                .difference(journal_discarded),
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post)
                .branch_projection_aus()
            =~= UnifiedCacheBranchBetreeRefinement::
                unified_cache_branch_betree_source(pre)
                    .branch_projection_aus()
                .difference(branch_discarded),
        post.program.state.free_aus
            == pre.program.state.free_aus
                + journal_discarded
                + branch_discarded,
    ensures
        unified_cache_betree_allocation_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let pre_journal =
        unified_cache_betree_journal_source(pre)
            .journal_projection_aus();
    let post_journal =
        unified_cache_betree_journal_source(post)
            .journal_projection_aus();
    let pre_branch =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre)
                .branch_projection_aus();
    let post_branch =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post)
                .branch_projection_aus();
    let reserved =
        UnifiedCacheBetreeSystem::State::reserved_aus();

    assert(post_journal <= pre_journal);
    assert(post_branch <= pre_branch);
    assert(post_journal.disjoint(post_branch)) by {
        assert(pre_journal.disjoint(pre_branch));
    }
    assert(reserved.disjoint(post_journal)) by {
        assert(reserved.disjoint(pre_journal));
    }
    assert(reserved.disjoint(post_branch)) by {
        assert(reserved.disjoint(pre_branch));
    }
    assert(post_state.free_aus.disjoint(reserved)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] post_state.free_aus.contains(au)
            implies !reserved.contains(au)
        by {
            if pre_state.free_aus.contains(au) {
                assert(pre_state.free_aus.disjoint(reserved));
            } else if journal_discarded.contains(au) {
                assert(pre_journal.contains(au));
                assert(reserved.disjoint(pre_journal));
            } else {
                assert(branch_discarded.contains(au));
                assert(pre_branch.contains(au));
                assert(reserved.disjoint(pre_branch));
            }
        }
    }
    assert(post_state.free_aus.disjoint(post_journal)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] post_state.free_aus.contains(au)
            implies !post_journal.contains(au)
        by {
            if pre_state.free_aus.contains(au) {
                assert(pre_state.free_aus.disjoint(pre_journal));
            } else if journal_discarded.contains(au) {
                assert(!pre_journal
                    .difference(journal_discarded)
                    .contains(au));
            } else {
                assert(branch_discarded.contains(au));
                assert(pre_branch.contains(au));
                assert(pre_journal.disjoint(pre_branch));
            }
        }
    }
    assert(post_state.free_aus.disjoint(post_branch)) by {
        assert forall |au: crate::disk::GenericDisk_v::AU|
            #[trigger] post_state.free_aus.contains(au)
            implies !post_branch.contains(au)
        by {
            if pre_state.free_aus.contains(au) {
                assert(pre_state.free_aus.disjoint(pre_branch));
            } else if branch_discarded.contains(au) {
                assert(!pre_branch
                    .difference(branch_discarded)
                    .contains(au));
            } else {
                assert(journal_discarded.contains(au));
                assert(pre_journal.contains(au));
                assert(pre_journal.disjoint(pre_branch));
            }
        }
    }
    assert(unified_cache_betree_allocation_inv(post));
}

pub open spec fn refinement_inv(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
) -> bool {
    &&& unified_cache_betree_component_inv(model)
    &&& CrashAwareCachingDiskBetreeSystemRefinement::refinement_inv(
        unified_cache_betree_system_i(model),
    )
    &&& unified_cache_betree_system_i(model).coordination_i().inv()
    &&& system_model_progress_history_inv(model)
    &&& system_model_progress_unique_inv(model)
    &&& system_model_request_id_unique_inv(model)
    &&& system_model_request_reply_disjoint_inv(model)
    &&& unified_cache_betree_ready_inv(model)
    &&& unified_cache_betree_recovery_state_inv(model)
    &&& unified_cache_betree_shared_cache_disk_inv(model)
    &&& unified_cache_betree_cache_response_inv(model)
    &&& unified_cache_betree_outstanding_io_inv(model)
    &&& unified_cache_betree_cache_request_inv(model)
    &&& unified_cache_betree_superblock_cache_id_inv(model)
    &&& unified_cache_betree_sync_state_inv(model)
    &&& unified_cache_betree_disk_request_inv(model)
    &&& unified_cache_betree_superblock_image_inv(model)
    &&& unified_cache_betree_unready_cache_clean_inv(model)
    &&& unified_cache_betree_persistent_branch_cache_clean_inv(
        model,
    )
    &&& unified_cache_betree_wip_persistent_disjoint_inv(model)
    &&& unified_cache_betree_allocation_inv(model)
}

pub proof fn init_refines(
    model: SystemModel::State<UnifiedCacheBetreeProgramModel>,
)
    requires
        SystemModel::State::initialize(
            model,
            model.program,
            model.disk,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::init(
            unified_cache_betree_system_i(model),
        ),
        refinement_inv(model),
{
    reveal(SystemModel::State::initialize);
    assert(UnifiedCacheBetreeProgramModel::is_mkfs(model.disk));
    assert(UnifiedCacheBetreeProgramModel::init(model.program));

    reveal(UnifiedCacheBetreeSystem::State::init);
    reveal(UnifiedCacheBetreeSystem::State::init_by);
    let config = choose |config: UnifiedCacheBetreeSystem::Config|
        UnifiedCacheBetreeSystem::State::init_by(
            model.program.state,
            config,
        );

    match config {
        UnifiedCacheBetreeSystem::Config::initialize(
            cache_slots,
            free_aus,
        ) => {
            reveal(UnifiedCacheBetreeSystem::State::initialize);
            let journal_src = unified_cache_betree_journal_source(model);
            let branch_src =
                UnifiedCacheBranchBetreeRefinement::
                    unified_cache_branch_betree_source(model);
            let dst = unified_cache_betree_system_i(model);
            let initial_superblock =
                model.disk.content[spec_superblock_addr()];

            assert(model.program.state.cache.inv()) by {
                assert(Cache::State::initialize(
                    model.program.state.cache,
                    cache_slots,
                )) by {
                    reveal(Cache::State::initialize);
                }
                Cache::State::initialize_inductive(
                    model.program.state.cache,
                    cache_slots,
                );
            }
            assert(UnifiedCacheJournalRefinement::
                init_shared_facts(journal_src));
            assert(UnifiedCacheBranchBetreeRefinement::
                init_shared_facts(branch_src));

            UnifiedCacheJournalRefinement::
                empty_source_init_refines(journal_src);
            UnifiedCacheBranchBetreeRefinement::init_refines(model);

            assert(dst.progress
                == crate::spec::MapSpec_t::AsyncMap::State::
                    init_ephemeral_state());
            assert(dst.sync_reqs
                == Map::<crate::spec::MapSpec_t::SyncReqId, nat>::
                    empty());
            assert(dst.superblockstore == SuperblockStore::State {
                persistent: initial_superblock,
                in_flight: None,
                landed: false,
            });
            assert(CrashAwareCachingDiskJournal::State::initialize(
                dst.journal,
            )) by {
                assert(CrashAwareCachingDiskJournal::State::init(
                    dst.journal,
                ));
                reveal(CrashAwareCachingDiskJournal::State::init);
                reveal(CrashAwareCachingDiskJournal::State::init_by);
                let journal_config = choose |config:
                    CrashAwareCachingDiskJournal::Config|
                    CrashAwareCachingDiskJournal::State::init_by(
                        dst.journal,
                        config,
                    );
                match journal_config {
                    CrashAwareCachingDiskJournal::Config::
                        initialize() => {
                        reveal(CrashAwareCachingDiskJournal::State::
                            initialize);
                    }
                    CrashAwareCachingDiskJournal::Config::
                        dummy_to_use_type_params(_) => {
                        assert(false);
                    }
                }
            }
            assert(
                CrashAwareCachingDiskBranchBetree::State::initialize(
                    dst.branch,
                )
            ) by {
                assert(CrashAwareCachingDiskBranchBetree::State::init(
                    dst.branch,
                ));
                reveal(CrashAwareCachingDiskBranchBetree::State::init);
                reveal(CrashAwareCachingDiskBranchBetree::State::init_by);
                let branch_config = choose |config:
                    CrashAwareCachingDiskBranchBetree::Config|
                    CrashAwareCachingDiskBranchBetree::State::init_by(
                        dst.branch,
                        config,
                    );
                match branch_config {
                    CrashAwareCachingDiskBranchBetree::Config::
                        initialize() => {
                        reveal(
                            CrashAwareCachingDiskBranchBetree::State::
                                initialize,
                        );
                    }
                    CrashAwareCachingDiskBranchBetree::Config::
                        dummy_to_use_type_params(_) => {
                        assert(false);
                    }
                }
            }
            assert(CrashAwareCachingDiskBetreeSystem::State::initialize(
                dst,
                free_aus,
                initial_superblock,
                dst.journal,
                dst.branch,
            )) by {
                reveal(CrashAwareCachingDiskBetreeSystem::State::
                    initialize);
            }
            assert(CrashAwareCachingDiskBetreeSystem::State::init_by(
                dst,
                CrashAwareCachingDiskBetreeSystem::Config::initialize(
                    free_aus,
                    initial_superblock,
                    dst.journal,
                    dst.branch,
                ),
            )) by {
                reveal(CrashAwareCachingDiskBetreeSystem::State::init_by);
            }
            reveal(CrashAwareCachingDiskBetreeSystem::State::init);
            CrashAwareCachingDiskBetreeSystemRefinement::
                init_refines_ctam(dst);

            assert(unified_cache_betree_component_inv(model));
            assert(system_model_progress_history_inv(model));
            assert(system_model_progress_unique_inv(model));
            assert(system_model_request_id_unique_inv(model));
            assert(system_model_request_reply_disjoint_inv(model));
            assert(unified_cache_betree_ready_inv(model));
            assert(journal_src.journal_caching_disk_i().cache
                == Map::<Address, RawPage>::empty()) by {
                assert_maps_equal!(
                    journal_src.journal_caching_disk_i().cache,
                    Map::<Address, RawPage>::empty(),
                    addr => {
                        assert(!addresses_in_aus(
                            journal_src.journal_projection_aus(),
                        ).contains(addr));
                    }
                );
            }
            assert(journal_src.journal_caching_disk_i().status
                == Map::<Address, PageStatus>::empty()) by {
                assert_maps_equal!(
                    journal_src.journal_caching_disk_i().status,
                    Map::<Address, PageStatus>::empty(),
                    addr => {
                        assert(!addresses_in_aus(
                            journal_src.journal_projection_aus(),
                        ).contains(addr));
                    }
                );
            }
            assert(unified_cache_betree_recovery_state_inv(model));
            assert(unified_cache_betree_shared_cache_disk_inv(model));
            assert(unified_cache_betree_allocation_inv(model));
            assert(refinement_inv(model));
        }
        UnifiedCacheBetreeSystem::Config::
            dummy_to_use_type_params(_) => {
            assert(false);
        }
    }
}

proof fn program_execute_progress_invs(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_execute(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
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
        assert forall |r: Request|
            #[trigger] post.requests.contains(r)
            implies post.id_history.contains(r.id) by {
            assert(pre.requests.contains(r));
            assert(pre.id_history.contains(r.id));
        }
        assert forall |r: Reply|
            #[trigger] post.replies.contains(r)
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
                    assert(r == req);
                    assert(!post.requests.contains(req));
                    assert(false);
                }
            } else {
                assert(pre.replies.contains(p));
            }
        }
    }
}

proof fn program_internal_finish_refinement(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        unified_cache_betree_component_inv(post),
        unified_cache_betree_ready_inv(post),
        unified_cache_betree_recovery_state_inv(post),
        unified_cache_betree_shared_cache_disk_inv(post),
        unified_cache_betree_cache_response_inv(post),
        unified_cache_betree_outstanding_io_inv(post),
        unified_cache_betree_cache_request_inv(post),
        unified_cache_betree_superblock_cache_id_inv(post),
        unified_cache_betree_sync_state_inv(post),
        unified_cache_betree_disk_request_inv(post),
        unified_cache_betree_superblock_image_inv(post),
        unified_cache_betree_unready_cache_clean_inv(post),
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        ),
        unified_cache_betree_wip_persistent_disjoint_inv(post),
        unified_cache_betree_allocation_inv(post),
    ensures
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        );
    assert(refinement_inv(post));
}

proof fn program_internal_branch_alloc_finish_refinement(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    op: CachingDiskBranchBetree::Label,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    reclaimed: Set<crate::disk::GenericDisk_v::AU>,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        pre.program.state.client_ready(),
        post.program.state.client_ready(),
        post.program.state.branch.control.persistent_aus
            == pre.program.state.branch.control.persistent_aus,
        op is InternalAlloc,
        crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs(op) == allocs,
        allocs <= pre.program.state.free_aus,
        CrashAwareCachingDiskBranchBetree::State::next(
            unified_cache_betree_system_i(pre).branch,
            unified_cache_betree_system_i(post).branch,
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op,
                    deallocs: reclaimed,
                },
        ),
        unified_cache_betree_system_i(post).journal
            == unified_cache_betree_system_i(pre).journal,
        unified_cache_betree_system_i(post).progress
            == unified_cache_betree_system_i(pre).progress,
        unified_cache_betree_system_i(post).sync_reqs
            == unified_cache_betree_system_i(pre).sync_reqs,
        unified_cache_betree_system_i(post).superblockstore
            == unified_cache_betree_system_i(pre).superblockstore,
        unified_cache_betree_journal_source(post)
            .journal_projection_aus()
            =~= unified_cache_betree_journal_source(pre)
                .journal_projection_aus(),
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post)
                .branch_projection_aus()
            == (
                UnifiedCacheBranchBetreeRefinement::
                    unified_cache_branch_betree_source(pre)
                        .branch_projection_aus()
                + allocs
            ) - reclaimed,
        reclaimed <=
            UnifiedCacheBranchBetreeRefinement::
                unified_cache_branch_betree_source(pre)
                    .branch_projection_aus(),
        post.program.state.free_aus
            == (pre.program.state.free_aus - allocs)
                + reclaimed,
        cached_branch_alloc_aus(
            post.program.state.branch.betree.wip_branches,
        ) <= cached_branch_alloc_aus(
            pre.program.state.branch.betree.wip_branches,
        ) + allocs,
        unified_cache_betree_component_inv(post),
        unified_cache_betree_ready_inv(post),
        unified_cache_betree_recovery_state_inv(post),
        unified_cache_betree_shared_cache_disk_inv(post),
        unified_cache_betree_cache_response_inv(post),
        unified_cache_betree_outstanding_io_inv(post),
        unified_cache_betree_cache_request_inv(post),
        unified_cache_betree_superblock_cache_id_inv(post),
        unified_cache_betree_sync_state_inv(post),
        unified_cache_betree_disk_request_inv(post),
        unified_cache_betree_superblock_image_inv(post),
        unified_cache_betree_unready_cache_clean_inv(post),
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    branch_wip_update_preserves_persistent_disjoint_inv(
        pre,
        post,
        allocs,
    );
    branch_alloc_preserves_allocation_inv(
        pre,
        post,
        allocs,
        reclaimed,
    );
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(src.allocation_ready());
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            branch_internal_alloc(
                dst.branch,
                op,
                allocs,
                reclaimed,
            ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                branch_internal_alloc,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    program_internal_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn accept_request_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::accept_request(pre, post, lbl),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::accept_request);

    let req = lbl->req;
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Request{req};

    assert(dst.progress.requests
        == src.progress.requests.insert(req));
    assert(!src.progress.requests.contains(req)) by {
        if src.progress.requests.contains(req) {
            assert(pre.requests.contains(req));
            assert(pre.id_history.contains(req.id));
            assert(false);
        }
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::accept_request(),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            accept_request);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(system_model_progress_history_inv(post)) by {
        assert forall |r: Request|
            #[trigger] post.requests.contains(r)
            implies post.id_history.contains(r.id) by {
            if r == req {
                assert(post.id_history.contains(req.id));
            } else {
                assert(pre.requests.contains(r));
                assert(pre.id_history.contains(r.id));
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
            }
        }
    }
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |r: Request, p: Reply| {
            &&& #[trigger] post.requests.contains(r)
            &&& #[trigger] post.replies.contains(p)
        } implies r.id != p.id by {
            if r == req {
                assert(pre.replies.contains(p));
                assert(pre.id_history.contains(p.id));
            } else {
                assert(pre.requests.contains(r));
                assert(pre.replies.contains(p));
            }
        }
    }
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(refinement_inv(post));
}

pub proof fn deliver_reply_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::deliver_reply(pre, post, lbl),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::deliver_reply);

    let reply = lbl->reply;
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Reply{reply};

    assert(dst.progress.replies
        == src.progress.replies.remove(reply));
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::deliver_reply(),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            deliver_reply);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(system_model_progress_history_inv(post)) by {
        assert forall |r: Reply|
            #[trigger] post.replies.contains(r)
            implies post.id_history.contains(r.id) by {
            assert(pre.replies.contains(r));
        }
    }
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post)) by {
        assert forall |r: Request, p: Reply| {
            &&& #[trigger] post.requests.contains(r)
            &&& #[trigger] post.replies.contains(p)
        } implies r.id != p.id by {
            assert(pre.requests.contains(r));
            assert(pre.replies.contains(p));
        }
    }
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(refinement_inv(post));
}

proof fn interpreted_noop_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        refinement_inv(pre),
        unified_cache_betree_system_i(post)
            == unified_cache_betree_system_i(pre),
        unified_cache_betree_system_i_lbl(pre, post, lbl) is Noop,
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        CrashAwareCachingDiskBetreeSystemRefinement::refinement_inv(
            unified_cache_betree_system_i(post),
        ),
        unified_cache_betree_system_i(post).coordination_i().inv(),
{
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = unified_cache_betree_system_i_lbl(
        pre,
        post,
        lbl,
    );
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::noop(),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(CrashAwareCachingDiskBetreeSystem::State::noop);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
}

pub proof fn accept_sync_request_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::accept_sync_request(pre, post, lbl),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::accept_sync_request);
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre));
    interpreted_noop_refines(pre, post, lbl);
    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(refinement_inv(post));
}

pub proof fn deliver_sync_reply_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::deliver_sync_reply(pre, post, lbl),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::deliver_sync_reply);
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre));
    interpreted_noop_refines(pre, post, lbl);
    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(refinement_inv(post));
}

pub proof fn system_noop_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::noop(pre, post, lbl),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::noop);
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre));
    interpreted_noop_refines(pre, post, lbl);
    assert(unified_cache_betree_ready_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_execute_noop_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_execute(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        lbl is ProgramUIOp,
        lbl->op is Execute,
        lbl->op->req.input is NoopInput,
        UnifiedCacheBetreeSystem::State::execute_noop(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Execute {
                req: lbl->op->req,
                reply: lbl->op->reply,
            },
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::program_execute);
    reveal(UnifiedCacheBetreeSystem::State::execute_noop);
    let req = lbl->op->req;
    let reply = lbl->op->reply;
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Execute{
            req,
            reply,
        };

    assert(src.progress.requests.contains(req));
    assert(!src.progress.replies.contains(reply)) by {
        if src.progress.replies.contains(reply) {
            assert(pre.replies.contains(reply));
            assert(req.id != reply.id);
        }
    }
    assert(dst.progress.requests
        == src.progress.requests.remove(req));
    assert(dst.progress.replies
        == src.progress.replies.insert(reply));
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::execute_noop(),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::execute_noop,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    program_execute_progress_invs(
        pre,
        post,
        lbl,
        new_program,
    );
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_execute_query_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_cache: Cache::State,
    receipt: LoadedBetreeQueryReceipt,
    access: PageAccess,
)
    requires
        SystemModel::State::program_execute(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        lbl is ProgramUIOp,
        lbl->op is Execute,
        lbl->op->req.input is QueryInput,
        UnifiedCacheBetreeSystem::State::execute_query(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Execute {
                req: lbl->op->req,
                reply: lbl->op->reply,
            },
            new_cache,
            receipt,
            access,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::program_execute);
    reveal(UnifiedCacheBetreeSystem::State::execute_query);

    let req = lbl->op->req;
    let reply = lbl->op->reply;
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let key = req.input.arrow_QueryInput_key();
    let value = reply.output.arrow_QueryOutput_value();
    let cache_lbl = Cache::Label::Access {
        reads: access.reads(),
        writes: access.writes(),
    };
    let branch_lbl =
        AtomicBranchBetreeState::Label::Betree {
            cached_op: CachedBranchBetree::Label::Query {
                end_lsn: pre_state.branch.betree.memtable.seq_end,
                key,
                value,
            },
        };

    Cache::State::inv_next(
        pre_state.cache,
        post_state.cache,
        cache_lbl,
    );
    assert(access.writes() == Map::<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >::empty()) by {
        reveal(PageAccess::read_only);
    }
    Cache::State::access_read_only_is_noop(
        pre_state.cache,
        post_state.cache,
        access.reads(),
    );
    reveal(AtomicBranchBetreeState::State::query);
    assert(CachedBranchBetree::State::query(
        pre_state.branch.betree,
        pre_state.branch.betree,
        CachedBranchBetree::Label::Query {
            end_lsn: pre_state.branch.betree.memtable.seq_end,
            key,
            value,
        },
        receipt,
        access.loaded_betree_reads(),
        access.loaded_branch_reads(),
    ));

    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);

    journal_pre.inv_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        access.reads(),
        access.writes(),
    );
    journal_pre.journal_interpretation_unchanged_by_same_projection(
        journal_post,
    );
    UnifiedCacheBranchBetreeRefinement::query_refines(
        branch_pre,
        branch_post,
        pre_state.branch.betree.memtable.seq_end,
        key,
        value,
        receipt,
        access,
    );

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Execute{
            req,
            reply,
        };

    assert(src.progress.requests.contains(req));
    assert(!src.progress.replies.contains(reply)) by {
        if src.progress.replies.contains(reply) {
            assert(pre.replies.contains(reply));
            assert(req.id != reply.id);
        }
    }
    assert(dst.progress.requests
        == src.progress.requests.remove(req));
    assert(dst.progress.replies
        == src.progress.replies.insert(reply));
    assert(src.journal.ephemeral is Known);
    assert(src.journal.ephemeral->v.journal.status is Some);
    assert(src.journal_lsn() == src.branch_lsn());
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::query(dst.branch),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(CrashAwareCachingDiskBetreeSystem::State::query);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    program_execute_progress_invs(
        pre,
        post,
        lbl,
        new_program,
    );
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_execute_put_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_journal: AtomicJournalState::State,
    new_branch: AtomicBranchBetreeState::State,
)
    requires
        SystemModel::State::program_execute(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        lbl is ProgramUIOp,
        lbl->op is Execute,
        lbl->op->req.input is PutInput,
        UnifiedCacheBetreeSystem::State::execute_put(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Execute {
                req: lbl->op->req,
                reply: lbl->op->reply,
            },
            new_journal,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::program_execute);
    reveal(UnifiedCacheBetreeSystem::State::execute_put);

    let req = lbl->op->req;
    let reply = lbl->op->reply;
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let key = req.input.arrow_PutInput_key();
    let value = req.input.arrow_PutInput_value();
    let keyed_message = KeyedMessage {
        key,
        message: Message::Define{value},
    };
    let records = MsgHistory::singleton_at(
        pre_state.branch.betree.memtable.seq_end,
        keyed_message,
    );
    AtomicBranchBetreeState::State::put_effect(
        pre_state.branch,
        post_state.branch,
        records,
    );

    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);

    UnifiedCacheJournalRefinement::put_preserves_projection_aus(
        journal_pre,
        journal_post,
        records,
    );
    crate::implementation::CachingDiskAdapterRefinement_v::
        caching_disk_i_equal_by_aus_ext(
            journal_post.cache,
            journal_post.disk,
            journal_post.journal_projection_aus(),
            journal_pre.journal_projection_aus(),
        );
    assert(journal_post.journal_caching_disk_i()
        == journal_pre.journal_caching_disk_i());
    UnifiedCacheJournalRefinement::put_refines(
        journal_pre,
        journal_post,
        records,
    );
    UnifiedCacheBranchBetreeRefinement::put_refines(
        branch_pre,
        branch_post,
        records,
    );

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Execute{
            req,
            reply,
        };

    assert(src.progress.requests.contains(req));
    assert(!src.progress.replies.contains(reply)) by {
        if src.progress.replies.contains(reply) {
            assert(pre.replies.contains(reply));
            assert(req.id != reply.id);
        }
    }
    assert(dst.progress.requests
        == src.progress.requests.remove(req));
    assert(dst.progress.replies
        == src.progress.replies.insert(reply));
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::put(
            dst.journal,
            dst.branch,
        ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(CrashAwareCachingDiskBetreeSystem::State::put);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    program_execute_progress_invs(
        pre,
        post,
        lbl,
        new_program,
    );
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post)) by {
        if post_state.client_ready() {
            assert(pre_state.client_ready());
            pre_state.branch.betree.memtable.apply_puts_end(records);
            assert(post_state.journal.journal.seq_end()
                == records.seq_end);
            assert(post_state.branch.betree.memtable.seq_end
                == records.seq_end);
        }
    }
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_execute_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_execute(new_program),
        ),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    let req = lbl->op->req;
    let reply = lbl->op->reply;
    let source_lbl = UnifiedCacheBetreeSystem::Label::Execute {
        req,
        reply,
    };
    assert(UnifiedCacheBetreeProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::UserIO{op: lbl->op},
    ));
    assert(UnifiedCacheBetreeSystem::State::next(
        pre.program.state,
        post.program.state,
        source_lbl,
    ));
    reveal(UnifiedCacheBetreeSystem::State::next);
    reveal(UnifiedCacheBetreeSystem::State::next_by);
    let unified_step = choose |step: UnifiedCacheBetreeSystem::Step|
        UnifiedCacheBetreeSystem::State::next_by(
            pre.program.state,
            post.program.state,
            source_lbl,
            step,
        );
    match req.input {
        Input::NoopInput => {
            match unified_step {
                UnifiedCacheBetreeSystem::Step::execute_noop() => {
                    program_execute_noop_refines(
                        pre,
                        post,
                        lbl,
                        new_program,
                    );
                }
                _ => {
                    assert(false);
                }
            }
        }
        Input::PutInput{..} => {
            match unified_step {
                UnifiedCacheBetreeSystem::Step::execute_put(
                    new_journal,
                    new_branch,
                ) => {
                    program_execute_put_refines(
                        pre,
                        post,
                        lbl,
                        new_program,
                        new_journal,
                        new_branch,
                    );
                }
                _ => {
                    assert(false);
                }
            }
        }
        Input::QueryInput{..} => {
            match unified_step {
                UnifiedCacheBetreeSystem::Step::execute_query(
                    new_cache,
                    receipt,
                    access,
                ) => {
                    program_execute_query_refines(
                        pre,
                        post,
                        lbl,
                        new_program,
                        new_cache,
                        receipt,
                        access,
                    );
                }
                _ => {
                    assert(false);
                }
            }
        }
    }
}

pub proof fn program_accept_sync_request_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    sync_req_id: crate::spec::MapSpec_t::SyncReqId,
)
    requires
        SystemModel::State::program_accept_sync_request(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        lbl is ProgramUIOp,
        lbl->op == (ProgramUserOp::AcceptSyncRequest{
            sync_req_id: sync_req_id,
        }),
        UnifiedCacheBetreeSystem::State::accept_sync_request(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::AcceptSyncRequest {
                sync_req_id,
            },
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_accept_sync_request);
    reveal(UnifiedCacheBetreeSystem::State::accept_sync_request);
    let state = pre.program.state;
    let journal_src = unified_cache_betree_journal_source(pre);
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::ReqSync{
            sync_req_id,
        };

    UnifiedCacheJournalRefinement::query_end_lsn_self_refines(
        journal_src,
        state.branch.betree.memtable.seq_end,
    );
    assert(src.components_loaded());
    assert(src.branch_lsn()
        == state.branch.betree.memtable.seq_end);
    assert(dst.sync_reqs == src.sync_reqs.insert(
        sync_req_id,
        src.branch_lsn(),
    ));
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::req_sync(),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(CrashAwareCachingDiskBetreeSystem::State::req_sync);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_deliver_sync_reply_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    sync_req_id: crate::spec::MapSpec_t::SyncReqId,
)
    requires
        SystemModel::State::program_deliver_sync_reply(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        lbl is ProgramUIOp,
        lbl->op == (ProgramUserOp::DeliverSyncReply{
            sync_req_id: sync_req_id,
        }),
        UnifiedCacheBetreeSystem::State::deliver_sync_reply(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::DeliverSyncReply {
                sync_req_id,
            },
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_deliver_sync_reply);
    reveal(UnifiedCacheBetreeSystem::State::deliver_sync_reply);
    let state = pre.program.state;
    let sync_lsn = state.sync_req_map[sync_req_id];
    let journal_src = unified_cache_betree_journal_source(pre);
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::ReplySync{
            sync_req_id,
        };

    assert(sync_lsn
        <= unified_cache_betree_system_i(pre)
            .journal.persistent.metadata().seq_end);
    UnifiedCacheJournalRefinement::
        query_lsn_persistence_self_refines(
            journal_src,
            sync_lsn,
        );
    assert(src.components_loaded());
    assert(dst.sync_reqs == src.sync_reqs.remove(sync_req_id));
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::reply_sync(),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(CrashAwareCachingDiskBetreeSystem::State::reply_sync);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

proof fn program_internal_interpreted_noop_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        unified_cache_betree_system_i(post)
            == unified_cache_betree_system_i(pre),
        unified_cache_betree_component_inv(post),
        unified_cache_betree_ready_inv(post),
        unified_cache_betree_recovery_state_inv(post),
        unified_cache_betree_shared_cache_disk_inv(post),
        unified_cache_betree_cache_response_inv(post),
        unified_cache_betree_outstanding_io_inv(post),
        unified_cache_betree_cache_request_inv(post),
        unified_cache_betree_superblock_cache_id_inv(post),
        unified_cache_betree_sync_state_inv(post),
        unified_cache_betree_disk_request_inv(post),
        unified_cache_betree_superblock_image_inv(post),
        unified_cache_betree_unready_cache_clean_inv(post),
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        ),
        unified_cache_betree_wip_persistent_disjoint_inv(post),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    interpreted_noop_refines(pre, post, lbl);
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_internal_cache_internal_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_cache: Cache::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::cache_internal(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            new_cache,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::cache_internal);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;

    assert(journal_pre.same_except_cache_and_disk(
        journal_post,
    ));
    journal_pre.cache_internal_refines(journal_post);
    branch_pre.cache_internal_refines(branch_post);
    assert(unified_cache_betree_component_inv(post));

    cache_internal_preserves_shared_cache_disk_inv(
        pre,
        post,
    );
    cache_internal_preserves_protocol_invs(pre, post);
    cache_internal_preserves_unready_cache_clean_inv(
        pre,
        post,
    );
    cache_internal_preserves_persistent_branch_cache_clean_inv(
        pre,
        post,
    );
    assert(unified_cache_betree_ready_inv(post));
    if pre_state.recovery_state is Begin
        || pre_state.recovery_state is AwaitingSuperblock
    {
        let journal_aus =
            journal_pre.journal_projection_aus();
        cache_internal_preserves_empty_projection(
            pre_state.cache,
            post_state.cache,
            journal_aus,
        );
        assert(journal_post.journal_projection_aus()
            =~= journal_aus);
        assert(journal_post.journal_caching_disk_i().cache
            == Map::<Address, RawPage>::empty());
        assert(journal_post.journal_caching_disk_i().status
            == Map::<Address, PageStatus>::empty());
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post));

    if !journal_pre.superblock_loaded() {
        assert(journal_post.i() == journal_pre.i());
        assert(dst.journal == src.journal);
        if branch_pre.control.loading {
            let branch_lbl =
                CrashAwareCachingDiskBranchBetree::Label::
                    RecoverMetadata {
                        recovery_op:
                            BetreeMetadataRecoveryLabel::
                                DiskInternal,
                    };
            assert(crate::implementation::
                CrashAwareCachingDiskBetreeSystem_v::
                    branch_internal_label(branch_lbl)) by {
                reveal(crate::implementation::
                    CrashAwareCachingDiskBetreeSystem_v::
                        branch_internal_label);
            }
            assert(
                CrashAwareCachingDiskBetreeSystem::State::
                    next_by(
                        src,
                        dst,
                        target_lbl,
                        CrashAwareCachingDiskBetreeSystem::Step::
                            branch_internal(
                                dst.branch,
                                branch_lbl,
                            ),
                    )
            ) by {
                reveal(
                    CrashAwareCachingDiskBetreeSystem::State::
                        next_by,
                );
                reveal(
                    CrashAwareCachingDiskBetreeSystem::State::
                        branch_internal,
                );
            }
        } else if branch_pre.control.metadata_loaded {
            let branch_lbl =
                CrashAwareCachingDiskBranchBetree::Label::
                    Ephemeral {
                        op:
                            CachingDiskBranchBetree::Label::
                                Internal,
                        deallocs: Set::empty(),
                    };
            assert(crate::implementation::
                CrashAwareCachingDiskBetreeSystem_v::
                    branch_internal_label(branch_lbl)) by {
                reveal(crate::implementation::
                    CrashAwareCachingDiskBetreeSystem_v::
                        branch_internal_label);
            }
            assert(
                CrashAwareCachingDiskBetreeSystem::State::
                    next_by(
                        src,
                        dst,
                        target_lbl,
                        CrashAwareCachingDiskBetreeSystem::Step::
                            branch_internal(
                                dst.branch,
                                branch_lbl,
                            ),
                    )
            ) by {
                reveal(
                    CrashAwareCachingDiskBetreeSystem::State::
                        next_by,
                );
                reveal(
                    CrashAwareCachingDiskBetreeSystem::State::
                        branch_internal,
                );
            }
        } else {
            assert(!branch_pre.control.loading);
            assert(!branch_pre.control.metadata_loaded);
            assert(branch_post.i() == branch_pre.i());
            assert(dst == src) by {
                assert(dst.journal == src.journal);
                assert(dst.branch == src.branch);
                assert(dst.progress == src.progress);
                assert(dst.sync_reqs == src.sync_reqs);
                assert(dst.free_aus == src.free_aus);
                assert(dst.superblockstore
                    == src.superblockstore);
            }
            assert(
                CrashAwareCachingDiskBetreeSystem::State::
                    next_by(
                        src,
                        dst,
                        target_lbl,
                        CrashAwareCachingDiskBetreeSystem::Step::
                            noop(),
                    )
            ) by {
                reveal(
                    CrashAwareCachingDiskBetreeSystem::State::
                        next_by,
                );
                reveal(
                    CrashAwareCachingDiskBetreeSystem::State::
                        noop,
                );
            }
        }
    } else if branch_pre.control.loading {
        let branch_lbl =
            CrashAwareCachingDiskBranchBetree::Label::
                RecoverMetadata {
                    recovery_op:
                        BetreeMetadataRecoveryLabel::DiskInternal,
                };
        assert(crate::implementation::
            CrashAwareCachingDiskBetreeSystem_v::
                branch_internal_label(branch_lbl)) by {
            reveal(crate::implementation::
                CrashAwareCachingDiskBetreeSystem_v::
                    branch_internal_label);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            next_by(
                src,
                dst,
                target_lbl,
                CrashAwareCachingDiskBetreeSystem::Step::
                    component_internals(
                        dst.journal,
                        dst.branch,
                        branch_lbl,
                    ),
            )) by {
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    next_by,
            );
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    component_internals,
            );
        }
    } else if branch_pre.control.metadata_loaded {
        let branch_lbl =
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op:
                        CachingDiskBranchBetree::Label::Internal,
                    deallocs: Set::empty(),
                };
        assert(crate::implementation::
            CrashAwareCachingDiskBetreeSystem_v::
                branch_internal_label(branch_lbl)) by {
            reveal(crate::implementation::
                CrashAwareCachingDiskBetreeSystem_v::
                    branch_internal_label);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            next_by(
                src,
                dst,
                target_lbl,
                CrashAwareCachingDiskBetreeSystem::Step::
                    component_internals(
                        dst.journal,
                        dst.branch,
                        branch_lbl,
                    ),
            )) by {
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    next_by,
            );
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    component_internals,
            );
        }
    } else {
        assert(!branch_pre.control.loading);
        assert(!branch_pre.control.metadata_loaded);
        assert(branch_post.i() == branch_pre.i());
        assert(dst.branch == src.branch);
        assert(CrashAwareCachingDiskBetreeSystem::State::
            next_by(
                src,
                dst,
                target_lbl,
                CrashAwareCachingDiskBetreeSystem::Step::
                    journal_internal(dst.journal),
            )) by {
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    next_by,
            );
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    journal_internal,
            );
        }
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    program_internal_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_betree_noop_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_internal(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            post.program.state.branch,
        ),
        AtomicBranchBetreeState::State::next_by(
            pre.program.state.branch,
            post.program.state.branch,
            AtomicBranchBetreeState::Label::Internal,
            AtomicBranchBetreeState::Step::internal_noop(),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::branch_internal);
    reveal(AtomicBranchBetreeState::State::next_by);
    reveal(AtomicBranchBetreeState::State::internal_noop);
    assert(post.program.state == pre.program.state);
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre));
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    program_internal_interpreted_noop_refines(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_sync_journal_prepare_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            execute_sync_journal_prepare(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Internal,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        execute_sync_journal_prepare);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let image = pre_state.sync_phase.image().unwrap();
    let branch_ready = pre_state.sync_phase.branch_ready();

    assert(post_state == UnifiedCacheBetreeSystem::State {
        sync_phase: AtomicBetreeSyncPhase::Preparing {
            image,
            journal_ready: true,
            branch_ready,
        },
        ..pre_state
    });
    assert(unified_cache_betree_sync_state_inv(pre));
    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    assert(AtomicJournalState::State::next_by(
        pre_state.journal,
        pre_state.journal,
        AtomicJournalState::Label::CommitPrepared,
        AtomicJournalState::Step::commit_prepared(),
    ));
    assert(AtomicJournalState::State::commit_prepared(
        pre_state.journal,
        pre_state.journal,
        AtomicJournalState::Label::CommitPrepared,
    ));
    reveal(AtomicJournalState::State::commit_prepared);
    assert(pre_state.journal.journal.status is Some);
    assert(pre_state.journal.in_flight.unwrap().snapshot
        .freshest_rec() is Some ==> {
        pre_state.journal.in_flight.unwrap().seq_end
            <= pre_state.journal.journal.clean_watermark()
    });
    assert(unified_cache_betree_sync_state_inv(post));

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    assert(journal_post == journal_pre);
    assert(branch_post.prepared_branch_image_i()
        == branch_pre.prepared_branch_image_i()) by {
        reveal(UnifiedCacheBranchBetreeRefinement::
            UnifiedCacheBranchBetreeSource::
                prepared_branch_image_i);
    }
    assert(branch_post.i() == branch_pre.i());
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre));

    assert(unified_cache_betree_component_inv(post)) by {
        reveal(unified_cache_betree_component_inv);
        reveal(UnifiedCacheBranchBetreeRefinement::
            UnifiedCacheBranchBetreeSource::inv);
    }
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_response_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_superblock_cache_id_inv(post));
    assert(unified_cache_betree_disk_request_inv(post));
    assert(unified_cache_betree_superblock_image_inv(post));
    assert(unified_cache_betree_unready_cache_clean_inv(post));
    assert(unified_cache_betree_persistent_branch_cache_clean_inv(
        post,
    ));
    assert(unified_cache_betree_wip_persistent_disjoint_inv(
        post,
    ));
    assert(unified_cache_betree_allocation_inv(post));
    program_internal_interpreted_noop_refines(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_sync_branch_prepare_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_cache: Cache::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            execute_sync_branch_prepare(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Internal,
                new_cache,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        execute_sync_branch_prepare);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let image = pre_state.sync_phase.image().unwrap();
    let journal_ready =
        pre_state.sync_phase.journal_ready();
    let frozen = pre_state.branch.control.frozen.unwrap();
    let cache_lbl = Cache::Label::EvictableCheck {
        aus: frozen.aus,
    };

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(
        pre_state.cache,
        post_state.cache,
        cache_lbl,
        Cache::Step::evictable(),
    ));
    reveal(Cache::State::evictable);
    assert(post_state.cache == pre_state.cache);
    assert(post_state == UnifiedCacheBetreeSystem::State {
        sync_phase: AtomicBetreeSyncPhase::Preparing {
            image,
            journal_ready,
            branch_ready: true,
        },
        ..pre_state
    });
    assert(unified_cache_betree_sync_state_inv(pre));
    assert(unified_cache_betree_sync_state_inv(post));

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    assert(journal_post == journal_pre);
    assert(branch_post.prepared_branch_image_i()
        == branch_pre.prepared_branch_image_i()) by {
        reveal(UnifiedCacheBranchBetreeRefinement::
            UnifiedCacheBranchBetreeSource::
                prepared_branch_image_i);
    }
    assert(branch_post.i() == branch_pre.i());
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre));
    assert(unified_cache_betree_component_inv(post)) by {
        reveal(unified_cache_betree_component_inv);
        reveal(UnifiedCacheBranchBetreeRefinement::
            UnifiedCacheBranchBetreeSource::inv);
    }

    assert(unified_cache_betree_persistent_branch_cache_clean_inv(
        post,
    )) by {
        pre_state.cache.build_lookup_map_ensures();
        assert forall |slot: Slot|
            #[trigger] post_state.cache.entries.contains_key(slot)
            && post_state.cache.entries[slot] is Filled
            && unified_cache_betree_branch_clean_aus(
                post_state,
            ).contains(
                post_state.cache.entries[slot].get_addr().au,
            )
            implies post_state.cache.status_map[slot] is Clean
        by {
            let addr =
                post_state.cache.entries[slot].get_addr();
            if pre_state.branch.control.persistent_aus
                .contains(addr.au)
            {
                assert(unified_cache_betree_branch_clean_aus(
                    pre_state,
                ).contains(addr.au));
                assert(unified_cache_betree_persistent_branch_cache_clean_inv(
                    pre,
                ));
            } else {
                assert(frozen.aus.contains(addr.au));
                assert(pre_state.cache.lookup_map
                    .contains_key(addr));
                assert(pre_state.cache.lookup_map[addr]
                    == slot);
            }
        }
    }
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_response_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_superblock_cache_id_inv(post));
    assert(unified_cache_betree_disk_request_inv(post));
    assert(unified_cache_betree_superblock_image_inv(post));
    assert(unified_cache_betree_unready_cache_clean_inv(post));
    assert(unified_cache_betree_wip_persistent_disjoint_inv(
        post,
    ));
    assert(unified_cache_betree_allocation_inv(post));
    program_internal_interpreted_noop_refines(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_metadata_load_complete_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::metadata_load_complete(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        metadata_load_complete);
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre));
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    program_internal_interpreted_noop_refines(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_recovery_complete_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::recovery_complete(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::recovery_complete);
    let state = pre.program.state;
    let end_lsn = state.branch.betree.memtable.seq_end;
    let atomic_lbl =
        AtomicJournalState::Label::QueryEndLsn{end_lsn};

    reveal(AtomicJournalState::State::next);
    reveal(AtomicJournalState::State::next_by);
    let atomic_step = choose |step: AtomicJournalState::Step|
        AtomicJournalState::State::next_by(
            state.journal,
            state.journal,
            atomic_lbl,
            step,
        );
    match atomic_step {
        AtomicJournalState::Step::query_end_lsn() => {
            reveal(AtomicJournalState::State::query_end_lsn);
            reveal(
                crate::implementation::CachedJournal_v::
                    CachedJournal::State::next,
            );
            reveal(
                crate::implementation::CachedJournal_v::
                    CachedJournal::State::next_by,
            );
            let cached_step = choose |step:
                crate::implementation::CachedJournal_v::
                    CachedJournal::Step|
                crate::implementation::CachedJournal_v::
                    CachedJournal::State::next_by(
                        state.journal.journal,
                        state.journal.journal,
                        crate::implementation::CachedJournal_v::
                            CachedJournal::Label::QueryEndLsn{
                                end_lsn,
                            },
                        step,
                    );
            match cached_step {
                crate::implementation::CachedJournal_v::
                    CachedJournal::Step::query_end_lsn() => {
                    reveal(
                        crate::implementation::CachedJournal_v::
                            CachedJournal::State::query_end_lsn,
                    );
                }
                _ => {
                    assert(false);
                }
            }
        }
        _ => {
            assert(false);
        }
    }
    assert(state.journal.journal.seq_end() == end_lsn);
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre));
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    program_internal_interpreted_noop_refines(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_branch_recovery_begin_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_internal(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            post.program.state.branch,
        ),
        AtomicBranchBetreeState::State::next_by(
            pre.program.state.branch,
            post.program.state.branch,
            AtomicBranchBetreeState::Label::Internal,
            AtomicBranchBetreeState::Step::recovery_begin(),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::branch_internal);
    reveal(AtomicBranchBetreeState::State::next_by);
    reveal(AtomicBranchBetreeState::State::recovery_begin);

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheBranchBetreeRefinement::load_ephemeral_refines(
        branch_pre,
        branch_post,
    );

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            branch_load_ephemeral(dst.branch),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                branch_load_ephemeral,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_internal_branch_internal_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_branch: AtomicBranchBetreeState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_internal(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::branch_internal);
    assert(post.program.state.branch == new_branch);
    assert(AtomicBranchBetreeState::State::next(
        pre.program.state.branch,
        post.program.state.branch,
        AtomicBranchBetreeState::Label::Internal,
    ));
    reveal(AtomicBranchBetreeState::State::next);
    let step = choose |step: AtomicBranchBetreeState::Step|
        AtomicBranchBetreeState::State::next_by(
            pre.program.state.branch,
            post.program.state.branch,
            AtomicBranchBetreeState::Label::Internal,
            step,
        );
    match step {
        AtomicBranchBetreeState::Step::recovery_begin() => {
            program_internal_branch_recovery_begin_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        },
        AtomicBranchBetreeState::Step::internal_noop() => {
            program_internal_betree_noop_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        },
        _ => {
            reveal(AtomicBranchBetreeState::State::next_by);
            assert(false);
        },
    }
}

pub proof fn program_internal_branch_recover_betree_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    addr: crate::disk::GenericDisk_v::Address,
    reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    new_cache: Cache::State,
    new_branch: AtomicBranchBetreeState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_internal_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            AtomicBranchBetreeState::Label::Recover {
                recovery_op:
                    BetreeMetadataRecoveryLabel::ReadBetree{
                        addr,
                        reads,
                    },
            },
            reads,
            Map::empty(),
            new_cache,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_access);
    reveal(AtomicBranchBetreeState::State::
        internal_access_next);
    reveal(AtomicBranchBetreeState::State::recover);
    let recovery_op =
        BetreeMetadataRecoveryLabel::ReadBetree{addr, reads};
    let cache_lbl = Cache::Label::Access {
        reads,
        writes: Map::empty(),
    };
    Cache::State::inv_next(
        pre.program.state.cache,
        post.program.state.cache,
        cache_lbl,
    );
    Cache::State::access_read_only_is_noop(
        pre.program.state.cache,
        post.program.state.cache,
        reads,
    );

    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    journal_pre.inv_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        reads,
        Map::empty(),
    );
    journal_pre.journal_interpretation_unchanged_by_same_projection(
        journal_post,
    );

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheBranchBetreeRefinement::recover_metadata_refines(
        branch_pre,
        branch_post,
        recovery_op,
    );

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            branch_recover_metadata(dst.branch, recovery_op),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                branch_recover_metadata,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_internal_branch_recover_root_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    root: crate::disk::GenericDisk_v::Address,
    reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    new_cache: Cache::State,
    new_branch: AtomicBranchBetreeState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_internal_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            AtomicBranchBetreeState::Label::Recover {
                recovery_op:
                    BetreeMetadataRecoveryLabel::ReadBranchRoot{
                        root,
                        reads,
                    },
            },
            reads,
            Map::empty(),
            new_cache,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_access);
    reveal(AtomicBranchBetreeState::State::
        internal_access_next);
    reveal(AtomicBranchBetreeState::State::recover);
    let recovery_op =
        BetreeMetadataRecoveryLabel::ReadBranchRoot{root, reads};
    let cache_lbl = Cache::Label::Access {
        reads,
        writes: Map::empty(),
    };
    Cache::State::inv_next(
        pre.program.state.cache,
        post.program.state.cache,
        cache_lbl,
    );
    Cache::State::access_read_only_is_noop(
        pre.program.state.cache,
        post.program.state.cache,
        reads,
    );

    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    journal_pre.inv_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        reads,
        Map::empty(),
    );
    journal_pre.journal_interpretation_unchanged_by_same_projection(
        journal_post,
    );

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheBranchBetreeRefinement::recover_metadata_refines(
        branch_pre,
        branch_post,
        recovery_op,
    );

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            branch_recover_metadata(dst.branch, recovery_op),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                branch_recover_metadata,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_internal_branch_recover_aux_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    root: crate::disk::GenericDisk_v::Address,
    reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    new_cache: Cache::State,
    new_branch: AtomicBranchBetreeState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_internal_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            AtomicBranchBetreeState::Label::Recover {
                recovery_op:
                    BetreeMetadataRecoveryLabel::ReadBranchAux{
                        root,
                        reads,
                    },
            },
            reads,
            Map::empty(),
            new_cache,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_access);
    reveal(AtomicBranchBetreeState::State::
        internal_access_next);
    reveal(AtomicBranchBetreeState::State::recover);
    let recovery_op =
        BetreeMetadataRecoveryLabel::ReadBranchAux{root, reads};
    let cache_lbl = Cache::Label::Access {
        reads,
        writes: Map::empty(),
    };
    Cache::State::inv_next(
        pre.program.state.cache,
        post.program.state.cache,
        cache_lbl,
    );
    Cache::State::access_read_only_is_noop(
        pre.program.state.cache,
        post.program.state.cache,
        reads,
    );

    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    journal_pre.inv_preserved_by_cache_access_outside_journal_projection(
        journal_post,
        reads,
        Map::empty(),
    );
    journal_pre.journal_interpretation_unchanged_by_same_projection(
        journal_post,
    );

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheBranchBetreeRefinement::recover_metadata_refines(
        branch_pre,
        branch_post,
        recovery_op,
    );

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            branch_recover_metadata(dst.branch, recovery_op),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                branch_recover_metadata,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_internal_branch_recovery_complete_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_recovery_complete(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_recovery_complete);
    reveal(AtomicBranchBetreeState::State::recovery_complete);

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheBranchBetreeRefinement::load_metadata_refines(
        branch_pre,
        branch_post,
    );

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let discovered_aus =
        post.program.state.branch.control.persistent_aus;
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(discovered_aus
        == dst.branch.ephemeral->persistent_aus);
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            branch_load_metadata(dst.branch, discovered_aus),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                branch_load_metadata,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_internal_journal_load_index_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    cache_reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    journal_reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    discovered_aus: Set<crate::disk::GenericDisk_v::AU>,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::journal_load_index(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            cache_reads,
            journal_reads,
            discovered_aus,
            new_cache,
            new_journal,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::journal_load_index);
    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    UnifiedCacheJournalRefinement::load_index_refines(
        journal_pre,
        journal_post,
        cache_reads,
        journal_reads,
        discovered_aus,
    );

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access {
                reads: cache_reads,
                writes: Map::empty(),
            },
            step,
        );
    match cache_step {
        Cache::Step::access() => {
            reveal(Cache::State::access);
            assert(post.program.state.cache
                == pre.program.state.cache);
        }
        _ => {
            assert(false);
        }
    }
    assert(branch_post == branch_pre);

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            journal_load_index(dst.journal, discovered_aus),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                journal_load_index,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_internal_read_for_recovery_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    addr: crate::disk::GenericDisk_v::Address,
    journal_reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::read_for_recovery(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            addr,
            journal_reads,
            new_cache,
            new_journal,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::read_for_recovery);
    reveal(AtomicBranchBetreeState::State::put);
    let full_msgs =
        crate::implementation::JournalTypes_v::
            to_journal_records(journal_reads)[addr].message_seq;
    let journal_records = full_msgs.maybe_discard_old(
        pre.program.state.journal.journal.snapshot.boundary_lsn,
    );
    let branch_records = full_msgs.maybe_discard_old(
        pre.program.state.branch.betree.memtable.seq_end,
    );

    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    UnifiedCacheJournalRefinement::read_for_recovery_refines(
        journal_pre,
        journal_post,
        addr,
        journal_reads,
        journal_reads,
        Map::empty(),
    );

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_step = choose |step: Cache::Step|
        Cache::State::next_by(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access {
                reads: journal_reads,
                writes: Map::empty(),
            },
            step,
        );
    match cache_step {
        Cache::Step::access() => {
            reveal(Cache::State::access);
            assert(post.program.state.cache
                == pre.program.state.cache);
        }
        _ => {
            assert(false);
        }
    }
    UnifiedCacheBranchBetreeRefinement::put_refines(
        branch_pre,
        branch_post,
        branch_records,
    );

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(src.branch_lsn()
        == pre.program.state.branch.betree.memtable.seq_end);
    assert(pre.program.state.journal.journal.snapshot.boundary_lsn
        <= src.branch_lsn()) by {
        assert(branch_pre.control.metadata.seq_end
            <= branch_pre.branch.memtable.seq_end);
        assert(branch_pre.control.metadata
            == branch_pre.persistent_metadata_i());
        assert(branch_pre.persistent_superblock_image_i()
            == journal_pre.persistent_superblock_image_i());
        assert(branch_pre.persistent_metadata_i().seq_end
            == journal_pre.persistent_superblock_image_i()
                .journal_snapshot.boundary_lsn);
    }
    assert(branch_records
        == journal_records.maybe_discard_old(src.branch_lsn())) by {
        let boundary =
            pre.program.state.journal.journal.snapshot.boundary_lsn;
        let branch_lsn = src.branch_lsn();
        reveal(MsgHistory::maybe_discard_old);
        if full_msgs.seq_start <= boundary {
            assert(journal_records == full_msgs.discard_old(boundary));
            assert(journal_records.seq_start == boundary);
            assert(journal_records.seq_end == full_msgs.seq_end);
            assert(journal_records.seq_start <= branch_lsn);
            assert(full_msgs.seq_start <= branch_lsn);
            assert(branch_records == full_msgs.discard_old(branch_lsn));
            assert(journal_records.maybe_discard_old(branch_lsn)
                == journal_records.discard_old(branch_lsn));
            let left = journal_records.discard_old(branch_lsn);
            let right = full_msgs.discard_old(branch_lsn);
            assert(left.seq_start == right.seq_start);
            assert(left.seq_end == right.seq_end);
            assert(left.msgs == right.msgs) by {
                assert_maps_equal!(left.msgs, right.msgs, lsn => {});
            }
            assert(left == right);
        } else {
            assert(journal_records == full_msgs);
        }
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::recover(
            dst.journal,
            dst.branch,
            journal_records,
            branch_records,
        ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(CrashAwareCachingDiskBetreeSystem::State::recover);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(unified_cache_betree_component_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);
    assert(refinement_inv(post));
}

pub proof fn program_internal_journal_marshall_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    addr: crate::disk::GenericDisk_v::Address,
    raw_page: crate::spec::AsyncDisk_t::RawPage,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::journal_internal_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            AtomicJournalState::Label::JournalMarshal {
                addr,
                writes: to_journal_records(
                    Map::<
                        crate::disk::GenericDisk_v::Address,
                        crate::spec::AsyncDisk_t::RawPage,
                    >::empty().insert(addr, raw_page),
                ),
            },
            Map::empty(),
            Map::<
                crate::disk::GenericDisk_v::Address,
                crate::spec::AsyncDisk_t::RawPage,
            >::empty().insert(addr, raw_page),
            new_cache,
            new_journal,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        journal_internal_access);
    reveal(AtomicJournalState::State::internal_access_next);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let writes = Map::<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >::empty().insert(addr, raw_page);

    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    assert(AtomicJournalState::State::next(
        pre_state.journal,
        post_state.journal,
        AtomicJournalState::Label::JournalMarshal{
            addr,
            writes: to_journal_records(writes),
        },
    )) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre_state.journal,
            post_state.journal,
            AtomicJournalState::Label::JournalMarshal{
                addr,
                writes: to_journal_records(writes),
            },
            AtomicJournalState::Step::journal_marshal(
                post_state.journal.journal,
            ),
        ));
    }
    UnifiedCacheJournalRefinement::journal_marshal_refines(
        journal_pre,
        journal_post,
        addr,
        raw_page,
    );

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    assert(writes.dom() <= addresses_in_aus(
        journal_pre.journal_projection_aus(),
    )) by {
        assert forall |write_addr:
            crate::disk::GenericDisk_v::Address|
            #[trigger] writes.contains_key(write_addr)
            implies addresses_in_aus(
                journal_pre.journal_projection_aus(),
            ).contains(write_addr)
        by {
            assert(write_addr == addr);
        }
    }
    assert(writes.dom().disjoint(addresses_in_aus(
        branch_pre.branch_projection_aus(),
    ))) by {
        assert forall |write_addr:
            crate::disk::GenericDisk_v::Address|
            #[trigger] writes.contains_key(write_addr)
            implies !addresses_in_aus(
                branch_pre.branch_projection_aus(),
            ).contains(write_addr)
        by {
            assert(journal_pre.journal_projection_aus()
                .contains(write_addr.au));
            if addresses_in_aus(
                branch_pre.branch_projection_aus(),
            ).contains(write_addr) {
                assert(branch_pre.branch_projection_aus()
                    .contains(write_addr.au));
                assert(false);
            }
        }
    }
    branch_pre
        .unchanged_by_cache_access_outside_branch_projection(
            branch_post,
            Map::empty(),
            writes,
        );
    assert(unified_cache_betree_component_inv(post));

    assert(writes.dom() <= Set::new(
        |write_addr: crate::disk::GenericDisk_v::Address|
            write_addr.wf(),
    )) by {
        assert forall |write_addr:
            crate::disk::GenericDisk_v::Address|
            #[trigger] writes.contains_key(write_addr)
            implies write_addr.wf()
        by {
            assert(write_addr == addr);
        }
    }
    cache_access_preserves_shared_cache_disk_inv(
        pre,
        post,
        Map::empty(),
        writes,
    );
    cache_access_preserves_protocol_invs(
        pre,
        post,
        Map::empty(),
        writes,
    );
    assert(writes.dom().disjoint(addresses_in_aus(
        unified_cache_betree_branch_clean_aus(pre_state),
    ))) by {
        assert(unified_cache_betree_branch_clean_aus(pre_state)
            <= branch_pre.branch_projection_aus());
    }
    cache_access_preserves_persistent_branch_cache_clean_inv(
        pre,
        post,
        Map::empty(),
        writes,
    );
    assert(unified_cache_betree_shared_cache_disk_inv(post));

    assert(unified_cache_betree_ready_inv(post)) by {
        assert(pre_state.client_ready());
        assert(post_state.client_ready());
        assert(post_state.branch == pre_state.branch);
        assert(post_state.journal.journal.seq_end()
            == pre_state.journal.journal.seq_end());
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
        assert(branch_post.branch_projection_aus()
            == branch_pre.branch_projection_aus());
        assert(post_state.free_aus == pre_state.free_aus);
    }

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(dst.branch == src.branch);
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            journal_internal(dst.journal),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                journal_internal,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    program_internal_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_observe_clean_journal_aus_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    aus: Set<crate::disk::GenericDisk_v::AU>,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            observe_clean_journal_aus(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Internal,
                aus,
                new_cache,
                new_journal,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        observe_clean_journal_aus);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    UnifiedCacheJournalRefinement::observe_clean_aus_refines(
        journal_pre,
        journal_post,
        aus,
    );

    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    assert(branch_post == branch_pre);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
    }
    assert(unified_cache_betree_ready_inv(post)) by {
        assert(pre_state.client_ready());
        assert(post_state.client_ready());
        assert(post_state.branch == pre_state.branch);
        assert(post_state.journal.journal.seq_end()
            == pre_state.journal.journal.seq_end());
    }
    assert(unified_cache_betree_recovery_state_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(dst.branch == src.branch);
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            journal_observe_clean_aus(dst.journal, aus),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                journal_observe_clean_aus,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    program_internal_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_journal_fill_aus_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    aus: Set<crate::disk::GenericDisk_v::AU>,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::journal_fill_aus(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            aus,
            new_journal,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::journal_fill_aus);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let journal_pre = unified_cache_betree_journal_source(pre);
    let journal_post = unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);

    assert(pre_state.journal.ready());
    assert(pre_state.branch.control.metadata_loaded);
    assert(aus.disjoint(
        journal_pre.journal_projection_aus(),
    )) by {
        assert(pre_state.free_aus.disjoint(
            journal_pre.journal_projection_aus(),
        ));
    }
    journal_fill_shared_projection_inv(pre, aus);
    UnifiedCacheJournalRefinement::fill_aus_refines(
        journal_pre,
        journal_post,
        aus,
    );
    assert(branch_post == branch_pre);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));

    assert(unified_cache_betree_ready_inv(post)) by {
        assert(post_state.client_ready()
            == pre_state.client_ready());
        assert(post_state.branch == pre_state.branch);
        assert(post_state.journal.journal
            == pre_state.journal.journal);
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        let old_journal_aus =
            journal_pre.journal_projection_aus();
        let new_journal_aus =
            journal_post.journal_projection_aus();
        let branch_aus = branch_pre.branch_projection_aus();
        let reserved =
            UnifiedCacheBetreeSystem::State::reserved_aus();
        assert(new_journal_aus
            =~= old_journal_aus + aus);
        assert(aus.disjoint(reserved)) by {
            assert(pre_state.free_aus.disjoint(reserved));
        }
        assert(aus.disjoint(branch_aus)) by {
            assert(pre_state.free_aus.disjoint(branch_aus));
        }
        assert(new_journal_aus.disjoint(branch_aus));
        assert(reserved.disjoint(new_journal_aus));
        assert((pre_state.free_aus - aus)
            .disjoint(new_journal_aus)) by {
            assert forall |au:
                crate::disk::GenericDisk_v::AU|
                #[trigger] (pre_state.free_aus - aus)
                    .contains(au)
                implies !new_journal_aus.contains(au)
            by {
                if new_journal_aus.contains(au) {
                    if old_journal_aus.contains(au) {
                        assert(pre_state.free_aus.disjoint(
                            old_journal_aus,
                        ));
                    } else {
                        assert(aus.contains(au));
                    }
                }
            }
        }
    }

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(src.allocation_ready());
    assert(dst.branch == src.branch);
    assert(dst.free_aus
        == (src.free_aus - aus) + Set::empty()) by {
        assert_sets_equal!(
            (src.free_aus - aus) + Set::empty(),
            src.free_aus - aus,
            au => {}
        );
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            journal_internal_alloc(
                dst.journal,
                aus,
                Set::empty(),
                Set::empty(),
            ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                journal_internal_alloc,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    program_internal_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
    );
}

pub proof fn program_internal_betree_branch_begin_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    access: PageAccess,
    new_cache: Cache::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            branch_internal_alloc_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            access.reads(),
            access.writes(),
            new_cache,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
        ),
        access == PageAccess::empty(),
        AtomicBranchBetreeState::State::branch_begin(
            pre.program.state.branch,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::
                    InternalAlloc{allocs, deallocs},
            },
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_alloc_access);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    assert(access.reads()
        == Map::<Address, RawPage>::empty()) by {
        reveal(PageAccess::reads);
    }
    assert(access.writes()
        == Map::<Address, RawPage>::empty()) by {
        reveal(PageAccess::writes);
    }
    assert(Cache::State::next(
        pre_state.cache,
        post_state.cache,
        Cache::Label::Access {
            reads: Map::empty(),
            writes: Map::empty(),
        },
    ));
    Cache::State::access_read_only_is_noop(
        pre_state.cache,
        post_state.cache,
        Map::empty(),
    );
    UnifiedCacheBranchBetreeRefinement::
        branch_begin_refines(
            branch_pre,
            branch_post,
            allocs,
            deallocs,
        );
    assert(journal_post == journal_pre);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_ready_inv(post)) by {
        assert(pre_state.client_ready());
        assert(post_state.client_ready());
        reveal(CachedBranchBetree::State::branch_begin);
        assert(post_state.branch.betree.memtable
            == pre_state.branch.betree.memtable);
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_branch_alloc_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
    );
}

pub proof fn program_internal_betree_branch_fill_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    idx: int,
    post_branch:
        crate::implementation::CachedBranchBetree_v::
            CachedAllocationBranch,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::betree_branch_fill(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            idx,
            post_branch,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        betree_branch_fill);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    branch_alloc_clean_cache_disk_coupling(pre, allocs);
    UnifiedCacheBranchBetreeRefinement::
        branch_fill_refines(
            branch_pre,
            branch_post,
            allocs,
            deallocs,
            idx,
            post_branch,
        );
    assert(journal_post == journal_pre);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_ready_inv(post)) by {
        assert(pre_state.client_ready());
        assert(post_state.client_ready());
        reveal(CachedBranchBetree::State::branch_build);
        assert(post_state.branch.betree.memtable
            == pre_state.branch.betree.memtable);
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_branch_alloc_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
    );
}

pub proof fn program_internal_betree_branch_abort_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    idx: int,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::betree_branch_abort(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            idx,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        betree_branch_abort);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    UnifiedCacheBranchBetreeRefinement::
        branch_abort_refines(
            branch_pre,
            branch_post,
            allocs,
            deallocs,
            idx,
        );
    assert(journal_post == journal_pre);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_ready_inv(post)) by {
        assert(pre_state.client_ready());
        assert(post_state.client_ready());
        reveal(CachedBranchBetree::State::branch_abort);
        assert(post_state.branch.betree.memtable
            == pre_state.branch.betree.memtable);
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_branch_alloc_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
    );
}

pub proof fn program_internal_betree_compact_abort_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    input_idx: int,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::betree_compact_abort(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            input_idx,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        betree_compact_abort);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    UnifiedCacheBranchBetreeRefinement::
        compact_abort_refines(
            branch_pre,
            branch_post,
            allocs,
            deallocs,
            input_idx,
        );
    assert(journal_post == journal_pre);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_ready_inv(post)) by {
        assert(pre_state.client_ready());
        assert(post_state.client_ready());
        reveal(CachedBranchBetree::State::compact_abort);
        assert(post_state.branch.betree.memtable
            == pre_state.branch.betree.memtable);
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_branch_alloc_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
    );
}

pub proof fn program_internal_betree_compact_begin_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    path:
        crate::implementation::CachedBranchBetree_v::
            LoadedBetreePath,
    start: nat,
    end: nat,
    access: PageAccess,
    new_cache: Cache::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_internal_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::Internal,
            },
            access.reads(),
            access.writes(),
            new_cache,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
        ),
        access.only_betree(),
        access.read_only(),
        AtomicBranchBetreeState::State::compact_begin(
            pre.program.state.branch,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::Internal,
            },
            new_branch,
            path,
            start,
            end,
            access.loaded_betree_reads(),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_access);
    reveal(AtomicBranchBetreeState::State::
        internal_access_next);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_lbl =
        CrashAwareCachingDiskBranchBetree::Label::
            Ephemeral {
                op: CachingDiskBranchBetree::Label::Internal,
                deallocs: Set::empty(),
            };

    assert(access.writes()
        == Map::<
            crate::disk::GenericDisk_v::Address,
            crate::spec::AsyncDisk_t::RawPage,
        >::empty()) by {
        reveal(PageAccess::read_only);
        reveal(PageAccess::writes);
        assert_maps_equal!(
            access.writes(),
            Map::<
                crate::disk::GenericDisk_v::Address,
                crate::spec::AsyncDisk_t::RawPage,
            >::empty(),
            addr => {}
        );
    }
    assert(Cache::State::next(
        pre_state.cache,
        post_state.cache,
        Cache::Label::Access {
            reads: access.reads(),
            writes: Map::empty(),
        },
    ));
    Cache::State::access_read_only_is_noop(
        pre_state.cache,
        post_state.cache,
        access.reads(),
    );
    assert(post_state.cache == pre_state.cache);
    UnifiedCacheBranchBetreeRefinement::
        compact_begin_refines(
            branch_pre,
            branch_post,
            path,
            start,
            end,
            access,
        );

    assert(journal_post == journal_pre);
    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_ready_inv(post)) by {
        if post_state.client_ready() {
            assert(pre_state.client_ready());
            reveal(CachedBranchBetree::State::compact_begin);
            assert(post_state.branch.betree.memtable
                == pre_state.branch.betree.memtable);
        }
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(branch_post.branch_projection_aus()
            == branch_pre.branch_projection_aus());
    }

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl = CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(crate::implementation::
        CrashAwareCachingDiskBetreeSystem_v::
            branch_internal_label(branch_lbl)) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBetreeSystem_v::
                branch_internal_label);
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            branch_internal(dst.branch, branch_lbl),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::next_by);
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                branch_internal,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    program_internal_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
    );
}

proof fn program_internal_betree_write_finish_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    op: CachingDiskBranchBetree::Label,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    reclaimed: Set<crate::disk::GenericDisk_v::AU>,
    access: PageAccess,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        pre.program.state.client_ready(),
        post.program.state.client_ready(),
        allocs <= pre.program.state.free_aus,
        op is InternalAlloc,
        crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs(op) == allocs,
        CrashAwareCachingDiskBranchBetree::State::next(
            unified_cache_betree_system_i(pre).branch,
            unified_cache_betree_system_i(post).branch,
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op,
                    deallocs: reclaimed,
                },
        ),
        UnifiedCacheBranchBetreeRefinement::inv(
            UnifiedCacheBranchBetreeRefinement::
                unified_cache_branch_betree_source(post),
        ),
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post)
                .branch_projection_aus()
            == (
                UnifiedCacheBranchBetreeRefinement::
                    unified_cache_branch_betree_source(pre)
                        .branch_projection_aus()
                + allocs
            ) - reclaimed,
        reclaimed <=
            UnifiedCacheBranchBetreeRefinement::
                unified_cache_branch_betree_source(pre)
                    .branch_projection_aus(),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access {
                reads: access.reads(),
                writes: access.writes(),
            },
        ),
        access.writes().dom()
            <= addresses_in_aus(
                UnifiedCacheBranchBetreeRefinement::
                    unified_cache_branch_betree_source(pre)
                        .branch_projection_aus()
                + allocs,
            ),
        access.writes().dom()
            <= Set::new(
                |addr: crate::disk::GenericDisk_v::Address| addr.wf(),
            ),
        access.writes().dom().disjoint(addresses_in_aus(
            unified_cache_betree_branch_clean_aus(
                pre.program.state,
            ),
        )),
        post.program.state.journal
            == pre.program.state.journal,
        post.program.state.persistent_image
            == pre.program.state.persistent_image,
        post.program.state.sync_phase
            == pre.program.state.sync_phase,
        post.program.state.sync_req_map
            == pre.program.state.sync_req_map,
        post.program.state.outstanding_cache_reqs
            == pre.program.state.outstanding_cache_reqs,
        post.program.state.branch.control
            == pre.program.state.branch.control,
        post.program.state.branch.betree.memtable.seq_end
            == pre.program.state.branch.betree.memtable.seq_end,
        post.program.state.free_aus
            == (pre.program.state.free_aus - allocs)
                + reclaimed,
        cached_branch_alloc_aus(
            post.program.state.branch.betree.wip_branches,
        ) <= cached_branch_alloc_aus(
            pre.program.state.branch.betree.wip_branches,
        ) + allocs,
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);

    assert(access.writes().dom().disjoint(
        addresses_in_aus(
            journal_pre.journal_projection_aus(),
        ),
    )) by {
        assert forall |addr:
            crate::disk::GenericDisk_v::Address|
            #[trigger] access.writes().contains_key(addr)
            implies !addresses_in_aus(
                journal_pre.journal_projection_aus(),
            ).contains(addr)
        by {
            assert((
                branch_pre.branch_projection_aus() + allocs
            ).contains(addr.au));
            if branch_pre.branch_projection_aus()
                .contains(addr.au)
            {
                assert(branch_pre.branch_projection_aus()
                    .disjoint(
                        journal_pre.journal_projection_aus(),
                    ));
            } else {
                assert(allocs.contains(addr.au));
                assert(pre_state.free_aus.contains(addr.au));
                assert(pre_state.free_aus.disjoint(
                    journal_pre.journal_projection_aus(),
                ));
            }
        }
    }
    journal_pre
        .inv_preserved_by_cache_access_outside_journal_projection(
            journal_post,
            access.reads(),
            access.writes(),
        );
    assert(unified_cache_betree_component_inv(post));

    cache_access_preserves_shared_cache_disk_inv(
        pre,
        post,
        access.reads(),
        access.writes(),
    );
    cache_access_preserves_protocol_invs(
        pre,
        post,
        access.reads(),
        access.writes(),
    );
    cache_access_preserves_persistent_branch_cache_clean_inv(
        pre,
        post,
        access.reads(),
        access.writes(),
    );
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    program_internal_branch_alloc_finish_refinement(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
    );
}

pub proof fn program_internal_betree_branch_build_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    idx: int,
    post_branch:
        crate::implementation::CachedBranchBetree_v::
            CachedAllocationBranch,
    event:
        crate::implementation::CachingDiskBranchBetree_v::
            BranchBuildEvent,
    access: PageAccess,
    new_cache: Cache::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            branch_internal_alloc_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            access.reads(),
            access.writes(),
            new_cache,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
        ),
        access.only_branch(),
        AtomicBranchBetreeState::State::branch_build(
            pre.program.state.branch,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::
                    InternalAlloc{allocs, deallocs},
            },
            new_branch,
            idx,
            post_branch,
            event.cached_event(access),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_alloc_access);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    branch_alloc_clean_cache_disk_coupling(pre, allocs);
    UnifiedCacheBranchBetreeRefinement::
        branch_build_refines(
            branch_pre,
            branch_post,
            allocs,
            deallocs,
            idx,
            post_branch,
            event,
            access,
        );
    reveal(CachedBranchBetree::State::branch_build);
    assert(post_state.branch.betree.memtable
        == pre_state.branch.betree.memtable);
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    let wip_aus =
        pre_state.branch.betree.wip_branches[idx]
            .mini_allocator.all_aus();
    let wip_au_sets = Seq::new(
        pre_state.branch.betree.wip_branches.len(),
        |i: int| pre_state.branch.betree.wip_branches[i]
            .mini_allocator.all_aus(),
    );
    crate::betree::Utils_v::lemma_subset_union_seq_of_sets(
        wip_au_sets,
        idx,
    );
    assert(wip_aus <= cached_branch_alloc_aus(
        pre_state.branch.betree.wip_branches,
    )) by {
        reveal(cached_branch_alloc_aus);
    }
    assert(wip_aus.disjoint(
        unified_cache_betree_branch_clean_aus(pre_state),
    )) by {
        assert(cached_branch_alloc_aus(
            pre_state.branch.betree.wip_branches,
        ).disjoint(pre_state.branch.control.persistent_aus));
        if pre_state.sync_phase.branch_ready()
            && pre_state.branch.control.frozen is Some
        {
            assert(branch_pre.i().refinement_inv());
            assert(cached_branch_alloc_aus(
                pre_state.branch.betree.wip_branches,
            ).disjoint(
                pre_state.branch.control.frozen.unwrap().aus,
            ));
        }
    }
    assert(access.writes().dom().disjoint(addresses_in_aus(
        unified_cache_betree_branch_clean_aus(pre_state),
    ))) by {
        assert forall |addr: Address|
            #[trigger] access.writes().contains_key(addr)
            implies !addresses_in_aus(
                unified_cache_betree_branch_clean_aus(pre_state),
            ).contains(addr)
        by {
            assert(wip_aus.contains(addr.au));
        }
    }
    program_internal_betree_write_finish_refines(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
        access,
    );
}

pub proof fn program_internal_betree_flush_memtable_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    branch_idx: int,
    new_root_addr: Address,
    access: PageAccess,
    new_cache: Cache::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            branch_internal_alloc_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            access.reads(),
            access.writes(),
            new_cache,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
        ),
        access.wf(),
        access.branch_writes.is_empty(),
        AtomicBranchBetreeState::State::flush_memtable(
            pre.program.state.branch,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::
                    InternalAlloc{allocs, deallocs},
            },
            new_branch,
            branch_idx,
            new_root_addr,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
            access.loaded_branch_reads(),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_alloc_access);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    branch_alloc_clean_cache_disk_coupling(pre, allocs);
    UnifiedCacheBranchBetreeRefinement::
        flush_memtable_refines(
            branch_pre,
            branch_post,
            allocs,
            deallocs,
            branch_idx,
            new_root_addr,
            access,
        );
    reveal(CachedBranchBetree::State::flush_memtable);
    assert(post_state.branch.betree.memtable.seq_end
        == pre_state.branch.betree.memtable.seq_end);
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_betree_write_finish_refines(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
        access,
    );
}

pub proof fn program_internal_betree_grow_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    new_root_addr: Address,
    access: PageAccess,
    new_cache: Cache::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            branch_internal_alloc_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            access.reads(),
            access.writes(),
            new_cache,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
        ),
        access.only_betree(),
        AtomicBranchBetreeState::State::grow(
            pre.program.state.branch,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::
                    InternalAlloc{allocs, deallocs},
            },
            new_branch,
            new_root_addr,
            access.loaded_betree_writes(),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_alloc_access);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    branch_alloc_clean_cache_disk_coupling(pre, allocs);
    UnifiedCacheBranchBetreeRefinement::grow_refines(
        branch_pre,
        branch_post,
        allocs,
        deallocs,
        new_root_addr,
        access,
    );
    reveal(CachedBranchBetree::State::grow);
    assert(post_state.branch.betree.memtable
        == pre_state.branch.betree.memtable);
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_betree_write_finish_refines(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
        access,
    );
}

pub proof fn program_internal_betree_split_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    path: LoadedBetreePath,
    request: SplitRequest,
    new_addrs: SplitAddrs,
    path_addrs: PathAddrs,
    access: PageAccess,
    new_cache: Cache::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            branch_internal_alloc_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            access.reads(),
            access.writes(),
            new_cache,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
        ),
        access.only_betree(),
        AtomicBranchBetreeState::State::split(
            pre.program.state.branch,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::
                    InternalAlloc{allocs, deallocs},
            },
            new_branch,
            path,
            request,
            new_addrs,
            path_addrs,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_alloc_access);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    branch_alloc_clean_cache_disk_coupling(pre, allocs);
    UnifiedCacheBranchBetreeRefinement::split_refines(
        branch_pre,
        branch_post,
        allocs,
        deallocs,
        path,
        request,
        new_addrs,
        path_addrs,
        access,
    );
    reveal(CachedBranchBetree::State::split);
    assert(post_state.branch.betree.memtable
        == pre_state.branch.betree.memtable);
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_betree_write_finish_refines(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
        access,
    );
}

pub proof fn program_internal_betree_flush_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    path: LoadedBetreePath,
    child_idx: nat,
    buffer_gc: nat,
    new_addrs: TwoAddrs,
    path_addrs: PathAddrs,
    access: PageAccess,
    new_cache: Cache::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            branch_internal_alloc_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            access.reads(),
            access.writes(),
            new_cache,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
        ),
        access.only_betree(),
        AtomicBranchBetreeState::State::flush(
            pre.program.state.branch,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::
                    InternalAlloc{allocs, deallocs},
            },
            new_branch,
            path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_alloc_access);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    branch_alloc_clean_cache_disk_coupling(pre, allocs);
    UnifiedCacheBranchBetreeRefinement::flush_refines(
        branch_pre,
        branch_post,
        allocs,
        deallocs,
        path,
        child_idx,
        buffer_gc,
        new_addrs,
        path_addrs,
        access,
    );
    reveal(CachedBranchBetree::State::flush);
    assert(post_state.branch.betree.memtable
        == pre_state.branch.betree.memtable);
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_betree_write_finish_refines(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
        access,
    );
}

pub proof fn program_internal_betree_compact_complete_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    input_idx: int,
    branch_idx: int,
    path: LoadedBetreePath,
    start: nat,
    end: nat,
    new_node_addr: Address,
    path_addrs: PathAddrs,
    access: PageAccess,
    new_cache: Cache::State,
    new_branch: CachedBranchBetree::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            branch_internal_alloc_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            allocs,
            deallocs,
            access.reads(),
            access.writes(),
            new_cache,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
        ),
        access.wf(),
        access.branch_writes.is_empty(),
        AtomicBranchBetreeState::State::compact_complete(
            pre.program.state.branch,
            AtomicBranchBetreeState::State {
                betree: new_branch,
                ..pre.program.state.branch
            },
            AtomicBranchBetreeState::Label::Betree {
                cached_op: CachedBranchBetree::Label::
                    InternalAlloc{allocs, deallocs},
            },
            new_branch,
            input_idx,
            branch_idx,
            path,
            start,
            end,
            new_node_addr,
            path_addrs,
            access.loaded_betree_reads(),
            access.loaded_betree_writes(),
            access.loaded_branch_reads(),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::program_internal);
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_alloc_access);
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let reclaimed =
        pre_state.branch.control.reclaimable(deallocs);
    let op =
        CachingDiskBranchBetree::Label::InternalAlloc {
            allocs,
            deallocs,
            guard_aus:
                pre_state.branch.control.protected_aus(),
        };

    branch_alloc_clean_cache_disk_coupling(pre, allocs);
    UnifiedCacheBranchBetreeRefinement::
        compact_complete_refines(
            branch_pre,
            branch_post,
            allocs,
            deallocs,
            input_idx,
            branch_idx,
            path,
            start,
            end,
            new_node_addr,
            path_addrs,
            access,
        );
    reveal(CachedBranchBetree::State::compact_complete);
    assert(post_state.branch.betree.memtable
        == pre_state.branch.betree.memtable);
    assert(crate::implementation::
        CrashAwareCachingDiskBranchBetree_v::
            logical_allocs(op) == allocs) by {
        reveal(crate::implementation::
            CrashAwareCachingDiskBranchBetree_v::
                logical_allocs);
    }
    program_internal_betree_write_finish_refines(
        pre,
        post,
        lbl,
        new_program,
        op,
        allocs,
        reclaimed,
        access,
    );
}

pub proof fn
program_internal_branch_internal_alloc_access_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    allocs: Set<crate::disk::GenericDisk_v::AU>,
    deallocs: Set<crate::disk::GenericDisk_v::AU>,
    reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    writes: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    new_cache: Cache::State,
    new_branch: AtomicBranchBetreeState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::
            branch_internal_alloc_access(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Internal,
                allocs,
                deallocs,
                reads,
                writes,
                new_cache,
                new_branch,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_alloc_access);
    reveal(AtomicBranchBetreeState::State::
        internal_alloc_access_next);
    let (step, access) = choose |
        step: AtomicBranchBetreeState::Step,
        access: PageAccess,
    | AtomicBranchBetreeState::State::
        internal_alloc_access_next_by(
            pre.program.state.branch,
            new_branch,
            allocs,
            deallocs,
            reads,
            writes,
            step,
            access,
        );
    reveal(AtomicBranchBetreeState::State::
        internal_alloc_access_next_by);
    reveal(AtomicBranchBetreeState::State::next_by);

    match step {
        AtomicBranchBetreeState::Step::branch_begin(
            new_betree,
        ) => {
            assert(AtomicBranchBetreeState::State::branch_begin(
                pre.program.state.branch,
                new_branch,
                AtomicBranchBetreeState::Label::Betree {
                    cached_op: CachedBranchBetree::Label::
                        InternalAlloc{allocs, deallocs},
                },
                new_betree,
            ));
            reveal(AtomicBranchBetreeState::State::branch_begin);
            assert(new_branch == AtomicBranchBetreeState::State {
                betree: new_betree,
                ..pre.program.state.branch
            });
            program_internal_betree_branch_begin_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                access,
                new_cache,
                new_betree,
            );
        },
        AtomicBranchBetreeState::Step::branch_build(
            new_betree,
            idx,
            post_branch,
            cached_event,
        ) => {
            let event = choose |event:
                crate::implementation::
                    CachingDiskBranchBetree_v::BranchBuildEvent|
                event.cached_event(access) == cached_event;
            assert(AtomicBranchBetreeState::State::branch_build(
                pre.program.state.branch,
                new_branch,
                AtomicBranchBetreeState::Label::Betree {
                    cached_op: CachedBranchBetree::Label::
                        InternalAlloc{allocs, deallocs},
                },
                new_betree,
                idx,
                post_branch,
                event.cached_event(access),
            ));
            reveal(AtomicBranchBetreeState::State::branch_build);
            assert(new_branch == AtomicBranchBetreeState::State {
                betree: new_betree,
                ..pre.program.state.branch
            });
            program_internal_betree_branch_build_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                idx,
                post_branch,
                event,
                access,
                new_cache,
                new_betree,
            );
        },
        AtomicBranchBetreeState::Step::flush_memtable(
            new_betree,
            branch_idx,
            new_root_addr,
            betree_reads,
            betree_writes,
            branch_reads,
        ) => {
            assert(AtomicBranchBetreeState::State::
                flush_memtable(
                    pre.program.state.branch,
                    new_branch,
                    AtomicBranchBetreeState::Label::Betree {
                        cached_op: CachedBranchBetree::Label::
                            InternalAlloc{allocs, deallocs},
                    },
                    new_betree,
                    branch_idx,
                    new_root_addr,
                    betree_reads,
                    betree_writes,
                    branch_reads,
                ));
            reveal(AtomicBranchBetreeState::State::
                flush_memtable);
            assert(new_branch == AtomicBranchBetreeState::State {
                betree: new_betree,
                ..pre.program.state.branch
            });
            program_internal_betree_flush_memtable_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                branch_idx,
                new_root_addr,
                access,
                new_cache,
                new_betree,
            );
        },
        AtomicBranchBetreeState::Step::grow(
            new_betree,
            new_root_addr,
            betree_writes,
        ) => {
            assert(AtomicBranchBetreeState::State::grow(
                pre.program.state.branch,
                new_branch,
                AtomicBranchBetreeState::Label::Betree {
                    cached_op: CachedBranchBetree::Label::
                        InternalAlloc{allocs, deallocs},
                },
                new_betree,
                new_root_addr,
                betree_writes,
            ));
            reveal(AtomicBranchBetreeState::State::grow);
            assert(new_branch == AtomicBranchBetreeState::State {
                betree: new_betree,
                ..pre.program.state.branch
            });
            program_internal_betree_grow_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                new_root_addr,
                access,
                new_cache,
                new_betree,
            );
        },
        AtomicBranchBetreeState::Step::split(
            new_betree,
            path,
            request,
            new_addrs,
            path_addrs,
            betree_reads,
            betree_writes,
        ) => {
            assert(AtomicBranchBetreeState::State::split(
                pre.program.state.branch,
                new_branch,
                AtomicBranchBetreeState::Label::Betree {
                    cached_op: CachedBranchBetree::Label::
                        InternalAlloc{allocs, deallocs},
                },
                new_betree,
                path,
                request,
                new_addrs,
                path_addrs,
                betree_reads,
                betree_writes,
            ));
            reveal(AtomicBranchBetreeState::State::split);
            assert(new_branch == AtomicBranchBetreeState::State {
                betree: new_betree,
                ..pre.program.state.branch
            });
            program_internal_betree_split_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                path,
                request,
                new_addrs,
                path_addrs,
                access,
                new_cache,
                new_betree,
            );
        },
        AtomicBranchBetreeState::Step::flush(
            new_betree,
            path,
            child_idx,
            buffer_gc,
            new_addrs,
            path_addrs,
            betree_reads,
            betree_writes,
        ) => {
            assert(AtomicBranchBetreeState::State::flush(
                pre.program.state.branch,
                new_branch,
                AtomicBranchBetreeState::Label::Betree {
                    cached_op: CachedBranchBetree::Label::
                        InternalAlloc{allocs, deallocs},
                },
                new_betree,
                path,
                child_idx,
                buffer_gc,
                new_addrs,
                path_addrs,
                betree_reads,
                betree_writes,
            ));
            reveal(AtomicBranchBetreeState::State::flush);
            assert(new_branch == AtomicBranchBetreeState::State {
                betree: new_betree,
                ..pre.program.state.branch
            });
            program_internal_betree_flush_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                path,
                child_idx,
                buffer_gc,
                new_addrs,
                path_addrs,
                access,
                new_cache,
                new_betree,
            );
        },
        AtomicBranchBetreeState::Step::compact_complete(
            new_betree,
            input_idx,
            branch_idx,
            path,
            start,
            end,
            new_node_addr,
            path_addrs,
            betree_reads,
            betree_writes,
            branch_reads,
        ) => {
            assert(AtomicBranchBetreeState::State::
                compact_complete(
                    pre.program.state.branch,
                    new_branch,
                    AtomicBranchBetreeState::Label::Betree {
                        cached_op: CachedBranchBetree::Label::
                            InternalAlloc{allocs, deallocs},
                    },
                    new_betree,
                    input_idx,
                    branch_idx,
                    path,
                    start,
                    end,
                    new_node_addr,
                    path_addrs,
                    betree_reads,
                    betree_writes,
                    branch_reads,
                ));
            reveal(AtomicBranchBetreeState::State::
                compact_complete);
            assert(new_branch == AtomicBranchBetreeState::State {
                betree: new_betree,
                ..pre.program.state.branch
            });
            program_internal_betree_compact_complete_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                input_idx,
                branch_idx,
                path,
                start,
                end,
                new_node_addr,
                path_addrs,
                access,
                new_cache,
                new_betree,
            );
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn program_internal_branch_internal_access_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    branch_lbl: AtomicBranchBetreeState::Label,
    reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    writes: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    new_cache: Cache::State,
    new_branch: AtomicBranchBetreeState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::branch_internal_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            branch_lbl,
            reads,
            writes,
            new_cache,
            new_branch,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(UnifiedCacheBetreeSystem::State::
        branch_internal_access);
    reveal(AtomicBranchBetreeState::State::
        internal_access_next);
    match branch_lbl {
        AtomicBranchBetreeState::Label::Recover{
            recovery_op,
        } => {
            assert(writes
                == Map::<
                    crate::disk::GenericDisk_v::Address,
                    crate::spec::AsyncDisk_t::RawPage,
                >::empty());
            match recovery_op {
                BetreeMetadataRecoveryLabel::ReadBetree{
                    addr,
                    reads: recovery_reads,
                } => {
                    assert(recovery_reads == reads);
                    program_internal_branch_recover_betree_refines(
                        pre,
                        post,
                        lbl,
                        new_program,
                        addr,
                        reads,
                        new_cache,
                        new_branch,
                    );
                },
                BetreeMetadataRecoveryLabel::ReadBranchRoot{
                    root,
                    reads: recovery_reads,
                } => {
                    assert(recovery_reads == reads);
                    program_internal_branch_recover_root_refines(
                        pre,
                        post,
                        lbl,
                        new_program,
                        root,
                        reads,
                        new_cache,
                        new_branch,
                    );
                },
                BetreeMetadataRecoveryLabel::ReadBranchAux{
                    root,
                    reads: recovery_reads,
                } => {
                    assert(recovery_reads == reads);
                    program_internal_branch_recover_aux_refines(
                        pre,
                        post,
                        lbl,
                        new_program,
                        root,
                        reads,
                        new_cache,
                        new_branch,
                    );
                },
                BetreeMetadataRecoveryLabel::DiskInternal => {
                    assert(false);
                },
            }
        },
        AtomicBranchBetreeState::Label::Betree{
            cached_op,
        } => {
            assert(cached_op is Internal);
            assert(writes
                == Map::<
                    crate::disk::GenericDisk_v::Address,
                    crate::spec::AsyncDisk_t::RawPage,
                >::empty());
            let (path, start, end) = choose |
                path:
                    crate::implementation::CachedBranchBetree_v::
                        LoadedBetreePath,
                start: nat,
                end: nat,
            |
                AtomicBranchBetreeState::State::compact_begin(
                    pre.program.state.branch,
                    new_branch,
                    branch_lbl,
                    new_branch.betree,
                    path,
                    start,
                    end,
                    crate::implementation::
                        CachingDiskBranchBetree_v::
                            to_betree_nodes(reads),
                );
            let access = PageAccess {
                betree_reads: reads,
                branch_reads: Map::empty(),
                betree_writes: Map::empty(),
                branch_writes: Map::empty(),
            };
            assert(access.reads() == reads) by {
                reveal(PageAccess::reads);
            }
            assert(access.writes() == writes) by {
                reveal(PageAccess::writes);
            }
            assert(access.only_betree()) by {
                reveal(PageAccess::only_betree);
            }
            assert(access.read_only()) by {
                reveal(PageAccess::read_only);
            }
            assert(access.loaded_betree_reads()
                == crate::implementation::
                    CachingDiskBranchBetree_v::
                        to_betree_nodes(reads)) by {
                reveal(PageAccess::loaded_betree_reads);
            }
            reveal(AtomicBranchBetreeState::State::compact_begin);
            assert(new_branch == AtomicBranchBetreeState::State {
                betree: new_branch.betree,
                ..pre.program.state.branch
            });
            program_internal_betree_compact_begin_refines(
                pre,
                post,
                lbl,
                new_program,
                path,
                start,
                end,
                access,
                new_cache,
                new_branch.betree,
            );
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn program_internal_journal_internal_access_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    journal_lbl: AtomicJournalState::Label,
    reads: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    writes: Map<
        crate::disk::GenericDisk_v::Address,
        crate::spec::AsyncDisk_t::RawPage,
    >,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
)
    requires
        SystemModel::State::program_internal(
            pre,
            post,
            lbl,
            new_program,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeSystem::State::journal_internal_access(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            journal_lbl,
            reads,
            writes,
            new_cache,
            new_journal,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(UnifiedCacheBetreeSystem::State::
        journal_internal_access);
    reveal(AtomicJournalState::State::internal_access_next);
    match journal_lbl {
        AtomicJournalState::Label::JournalMarshal{
            addr,
            writes: journal_writes,
        } => {
            assert(reads
                == Map::<
                    crate::disk::GenericDisk_v::Address,
                    crate::spec::AsyncDisk_t::RawPage,
                >::empty());
            let raw_page = writes[addr];
            let singleton_writes = Map::<
                crate::disk::GenericDisk_v::Address,
                crate::spec::AsyncDisk_t::RawPage,
            >::empty().insert(addr, raw_page);
            assert(writes.dom() == set![addr]);
            assert(singleton_writes.dom() == set![addr]);
            assert(writes == singleton_writes) by {
                assert_maps_equal!(writes, singleton_writes, write_addr => {
                    if writes.contains_key(write_addr) {
                        assert(writes.dom().contains(write_addr));
                        assert(set![addr].contains(write_addr));
                        assert(write_addr == addr);
                    }
                });
            }
            assert(to_journal_records(singleton_writes)
                == journal_writes);
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
        _ => {
            assert(false);
        },
    }
}

pub proof fn program_internal_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_internal(new_program),
        ),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::program_internal(
        pre,
        post,
        lbl,
        new_program,
    ));
    reveal(SystemModel::State::program_internal);
    assert(UnifiedCacheBetreeProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::Internal{},
    ));
    assert(UnifiedCacheBetreeSystem::State::next(
        pre.program.state,
        post.program.state,
        UnifiedCacheBetreeSystem::Label::Internal,
    ));
    reveal(UnifiedCacheBetreeSystem::State::next);
    reveal(UnifiedCacheBetreeSystem::State::next_by);
    let step = choose |step: UnifiedCacheBetreeSystem::Step|
        UnifiedCacheBetreeSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Internal,
            step,
        );
    match step {
        UnifiedCacheBetreeSystem::Step::branch_internal(
            new_branch,
        ) => {
            program_internal_branch_internal_refines(
                pre,
                post,
                lbl,
                new_program,
                new_branch,
            );
        }
        UnifiedCacheBetreeSystem::Step::branch_internal_access(
            branch_lbl,
            reads,
            writes,
            new_cache,
            new_branch,
        ) => {
            program_internal_branch_internal_access_refines(
                pre,
                post,
                lbl,
                new_program,
                branch_lbl,
                reads,
                writes,
                new_cache,
                new_branch,
            );
        }
        UnifiedCacheBetreeSystem::Step::
            branch_recovery_complete() => {
            program_internal_branch_recovery_complete_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        }
        UnifiedCacheBetreeSystem::Step::cache_internal(
            new_cache,
        ) => {
            program_internal_cache_internal_refines(
                pre,
                post,
                lbl,
                new_program,
                new_cache,
            );
        }
        UnifiedCacheBetreeSystem::Step::journal_load_index(
            cache_reads,
            journal_reads,
            discovered_aus,
            new_cache,
            new_journal,
        ) => {
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
        }
        UnifiedCacheBetreeSystem::Step::
            metadata_load_complete() => {
            program_internal_metadata_load_complete_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        }
        UnifiedCacheBetreeSystem::Step::read_for_recovery(
            addr,
            journal_reads,
            new_cache,
            new_journal,
            new_branch,
        ) => {
            program_internal_read_for_recovery_refines(
                pre,
                post,
                lbl,
                new_program,
                addr,
                journal_reads,
                new_cache,
                new_journal,
                new_branch,
            );
        }
        UnifiedCacheBetreeSystem::Step::recovery_complete() => {
            program_internal_recovery_complete_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        }
        UnifiedCacheBetreeSystem::Step::journal_internal_access(
            journal_lbl,
            reads,
            writes,
            new_cache,
            new_journal,
        ) => {
            program_internal_journal_internal_access_refines(
                pre,
                post,
                lbl,
                new_program,
                journal_lbl,
                reads,
                writes,
                new_cache,
                new_journal,
            );
        }
        UnifiedCacheBetreeSystem::Step::
            observe_clean_journal_aus(
                aus,
                new_cache,
                new_journal,
            ) => {
            program_internal_observe_clean_journal_aus_refines(
                pre,
                post,
                lbl,
                new_program,
                aus,
                new_cache,
                new_journal,
            );
        }
        UnifiedCacheBetreeSystem::Step::journal_fill_aus(
            aus,
            new_journal,
        ) => {
            program_internal_journal_fill_aus_refines(
                pre,
                post,
                lbl,
                new_program,
                aus,
                new_journal,
            );
        }
        UnifiedCacheBetreeSystem::Step::betree_branch_fill(
            allocs,
            deallocs,
            idx,
            post_branch,
            new_branch,
        ) => {
            program_internal_betree_branch_fill_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                idx,
                post_branch,
                new_branch,
            );
        }
        UnifiedCacheBetreeSystem::Step::
            branch_internal_alloc_access(
            allocs,
            deallocs,
            reads,
            writes,
            new_cache,
            new_branch,
        ) => {
            program_internal_branch_internal_alloc_access_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                reads,
                writes,
                new_cache,
                new_branch,
            );
        }
        UnifiedCacheBetreeSystem::Step::betree_branch_abort(
            allocs,
            deallocs,
            idx,
            new_branch,
        ) => {
            program_internal_betree_branch_abort_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                idx,
                new_branch,
            );
        }
        UnifiedCacheBetreeSystem::Step::betree_compact_abort(
            allocs,
            deallocs,
            input_idx,
            new_branch,
        ) => {
            program_internal_betree_compact_abort_refines(
                pre,
                post,
                lbl,
                new_program,
                allocs,
                deallocs,
                input_idx,
                new_branch,
            );
        }
        UnifiedCacheBetreeSystem::Step::
            execute_sync_journal_prepare() => {
            program_internal_sync_journal_prepare_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        }
        UnifiedCacheBetreeSystem::Step::
            execute_sync_branch_prepare(new_cache) => {
            program_internal_sync_branch_prepare_refines(
                pre,
                post,
                lbl,
                new_program,
                new_cache,
            );
        }
        _ => {
            assert(false);
        }
    }
}

pub proof fn program_disk_initiate_recovery_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    req_id: ID,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::initiate_recovery(
                req_id,
                reqs,
                resps,
            ),
            lbl->info,
        ),
        UnifiedCacheBetreeSystem::State::initiate_recovery(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Disk,
            req_id,
            reqs,
            resps,
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let read_req = DiskRequest::ReadReq{
        from: spec_superblock_addr(),
    };
    let req_map = Map::empty().insert(req_id, read_req);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs == Multiset::empty().insert((
        req_id,
        read_req,
    )));
    assert(resps.is_empty());
    multiset_map_singleton_ensures(req_id, read_req);
    assert(multiset_to_map(reqs) == req_map);
    assert(multiset_to_map(resps)
        == Map::<ID, DiskResponse>::empty()) by {
        assert_maps_equal!(
            multiset_to_map(resps),
            Map::<ID, DiskResponse>::empty(),
            id => {
                if multiset_to_map(resps).contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] resps.contains(pair)
                            && pair.0 == id;
                    assert(resps.contains(pair));
                    assert(false);
                }
            }
        );
    }
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(post.disk.content == pre.disk.content);
    assert(post.disk.responses == pre.disk.responses);
    assert(post.disk.requests
        == pre.disk.requests.union_prefer_right(req_map));
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    reveal(UnifiedCacheBetreeSystem::State::
        initiate_recovery);
    assert(post_state == UnifiedCacheBetreeSystem::State{
        recovery_state: RecoveryState::AwaitingSuperblock,
        ..pre_state
    });

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);

    assert(journal_pre.same_except_cache_and_disk(
        journal_post,
    ));
    journal_pre.unchanged_by_same_cache_and_disk_content(
        journal_post,
    );
    branch_pre.unchanged_by_same_cache_and_disk_content(
        branch_post,
    );
    assert(unified_cache_betree_component_inv(post));

    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre)) by {
        assert(unified_cache_betree_journal_source(post).i()
            == unified_cache_betree_journal_source(pre).i());
        assert(branch_post.i() == branch_pre.i());
        assert(unified_cache_betree_superblockstore_i(post)
            == unified_cache_betree_superblockstore_i(pre)) by {
            assert(post_state.sync_phase
                == pre_state.sync_phase);
            assert(unified_cache_betree_superblock_landed(
                post_state,
                post.disk,
            ) == unified_cache_betree_superblock_landed(
                pre_state,
                pre.disk,
            ));
            let sync_req_id = pre_state.sync_phase.req_id();
            if sync_req_id is Some {
                let id = sync_req_id.unwrap();
                if req_map.contains_key(id) {
                    assert(post.disk.requests[id]
                        == req_map[id]);
                    assert(post.disk.requests[id] is ReadReq);
                    assert(!unified_cache_betree_superblock_write_pending(
                        post,
                    ));
                } else if pre.disk.requests
                    .contains_key(id)
                {
                    assert(post.disk.requests[id]
                        == pre.disk.requests[id]);
                }
            }
        }
    }
    interpreted_noop_refines(pre, post, lbl);

    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post)) by {
        assert(disk_has_pending_id(post.disk, req_id));
        assert forall |left: ID, right: ID| {
            &&& #[trigger] disk_has_pending_id(
                post.disk,
                left,
            )
            &&& #[trigger] disk_has_pending_id(
                post.disk,
                right,
            )
        } implies left == right by {
            if post.disk.requests.contains_key(left) {
                assert(req_map.contains_key(left));
                assert(left == req_id);
            } else {
                assert(post.disk.responses.contains_key(left));
                assert(pre.disk.responses.contains_key(left));
                assert(false);
            }
            if post.disk.requests.contains_key(right) {
                assert(req_map.contains_key(right));
                assert(right == req_id);
            } else {
                assert(post.disk.responses.contains_key(right));
                assert(pre.disk.responses.contains_key(right));
                assert(false);
            }
        }
    }
    assert(unified_cache_betree_disk_request_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_allocation_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_superblock_recovery_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    req_id: ID,
    raw_page: RawPage,
    image: AbstractSuperblockImage,
    new_journal: AtomicJournalState::State,
    new_branch: AtomicBranchBetreeState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::
                superblock_recovery(
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
        UnifiedCacheBetreeSystem::State::
            superblock_recovery(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                req_id,
                raw_page,
                image,
                new_journal,
                new_branch,
                reqs,
                resps,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let read_resp = DiskResponse::ReadResp{data: raw_page};
    let resp_map = Map::empty().insert(req_id, read_resp);
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(resps == Multiset::empty().insert((
        req_id,
        read_resp,
    )));
    assert(multiset_to_map(reqs)
        == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            multiset_to_map(reqs),
            Map::<ID, DiskRequest>::empty(),
            id => {
                if multiset_to_map(reqs).contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] reqs.contains(pair)
                            && pair.0 == id;
                    assert(reqs.contains(pair));
                    assert(false);
                }
            }
        );
    }
    multiset_map_singleton_ensures(req_id, read_resp);
    assert(multiset_to_map(resps) == resp_map);
    assert(disk_lbl->requests
        == Map::<ID, DiskRequest>::empty());
    assert(disk_lbl->responses == resp_map);
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(post.disk.content == pre.disk.content);
    assert(post.disk.requests == pre.disk.requests);
    assert(post.disk.responses
        == pre.disk.responses.remove(req_id));
    assert(resp_map <= pre.disk.responses) by {
        reveal(AsyncDisk::State::disk_ops);
    }
    assert(resp_map.contains_key(req_id));
    assert(pre.disk.responses.contains_key(req_id));
    assert(pre.disk.responses[req_id] == read_resp);
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    assert(unified_cache_betree_recovery_state_inv(pre));
    assert(pre_state.recovery_state
        is AwaitingSuperblock);
    assert(pre.disk.responses[req_id] is ReadResp);
    assert(pre.disk.responses[req_id]->data
        == pre.disk.content[spec_superblock_addr()]);
    assert(raw_page
        == pre.disk.content[spec_superblock_addr()]);
    assert(superblock_matches(raw_page, image));
    superblock_matches_image_wf(raw_page, image);
    assert(betree_superblock_image_wf(image));

    reveal(UnifiedCacheBetreeSystem::State::
        superblock_recovery);
    let metadata = betree_metadata_from_superblock(image);
    assert(post_state == UnifiedCacheBetreeSystem::State{
        recovery_state: RecoveryState::SuperblockAvailable,
        journal: new_journal,
        branch: new_branch,
        persistent_image: Some(image),
        sync_phase: AtomicBetreeSyncPhase::None,
        sync_req_map: Map::empty(),
        ..pre_state
    });

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);

    assert(journal_pre.persistent_superblock_image_i()
        == image) by {
        assert(!journal_pre.superblock_loaded());
        assert(UnifiedCacheJournalRefinement::
            async_disk_superblock_raw_i(
                pre.disk.content,
            ) == raw_page);
    }
    assert(journal_post.journal_projection_aus()
        =~= journal_pre.journal_projection_aus()) by {
        assert(!journal_post.journal.ready());
        assert(!journal_pre.journal.ready());
        assert(journal_post.persistent_superblock_image_i()
            == image);
    }
    assert(journal_post.cache == journal_pre.cache);
    assert(journal_post.journal_caching_disk_i().cache
        == journal_pre.journal_caching_disk_i().cache) by {
        assert_maps_equal!(
            journal_post.journal_caching_disk_i().cache,
            journal_pre.journal_caching_disk_i().cache,
            addr => {}
        );
    }
    assert(journal_post.journal_caching_disk_i().status
        == journal_pre.journal_caching_disk_i().status) by {
        assert_maps_equal!(
            journal_post.journal_caching_disk_i().status,
            journal_pre.journal_caching_disk_i().status,
            addr => {}
        );
    }
    assert(journal_post.journal_caching_disk_i().cache
        == Map::<Address, RawPage>::empty()) by {
        assert(journal_pre.journal_caching_disk_i().cache
            == Map::<Address, RawPage>::empty());
    }
    assert(journal_post.journal_caching_disk_i().status
        == Map::<Address, PageStatus>::empty()) by {
        assert(journal_pre.journal_caching_disk_i().status
            == Map::<Address, PageStatus>::empty());
    }
    UnifiedCacheJournalRefinement::load_ephemeral_refines(
        journal_pre,
        journal_post,
        image,
    );

    branch_pre.install_from_superblock_refines(
        branch_post,
        image,
    );
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::LoadEphemeral,
    ));
    assert(dst.branch == src.branch);
    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    assert(dst.superblockstore == src.superblockstore) by {
        assert(pre_state.sync_phase is None);
        assert(post_state.sync_phase is None);
        assert(post.disk.content == pre.disk.content);
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::
        journal_load_ephemeral(
            src,
            dst,
            CrashAwareCachingDiskBetreeSystem::Label::Noop,
            dst.journal,
        )
    ) by {
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::
                journal_load_ephemeral,
        );
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        CrashAwareCachingDiskBetreeSystem::Label::Noop,
        CrashAwareCachingDiskBetreeSystem::Step::
            journal_load_ephemeral(dst.journal),
    )) by {
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::next_by,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(
            src,
            dst,
            CrashAwareCachingDiskBetreeSystem::Label::Noop,
        );

    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_disk_request_inv(post)) by {
        assert(pre.disk.responses.contains_key(req_id));
        assert(disk_has_pending_id(pre.disk, req_id));
        assert forall |pending_id: ID|
            #[trigger] pre.disk.requests
                .contains_key(pending_id)
            implies false
        by {
            assert(disk_has_pending_id(
                pre.disk,
                pending_id,
            ));
            assert(pending_id == req_id);
            assert(pre.disk.requests.dom().disjoint(
                pre.disk.responses.dom(),
            ));
        }
        assert(post.disk.requests
            == Map::<ID, DiskRequest>::empty());
    }
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
        assert(branch_post.branch_projection_aus()
            == branch_pre.branch_projection_aus());
    }
    assert(refinement_inv(post));
}

pub proof fn program_disk_cache_io_begin_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    req_map: Map<ID, DiskRequest>,
    new_cache: Cache::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::cache_io_begin(
                req_map,
                new_cache,
                reqs,
                resps,
            ),
            lbl->info,
        ),
        UnifiedCacheBetreeSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Disk,
            UnifiedCacheBetreeSystem::Step::cache_io_begin(
                req_map,
                new_cache,
                reqs,
                resps,
            ),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheBetreeSystem::State::next_by);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(multiset_to_map(reqs) == req_map);
    assert(disk_lbl->requests == req_map);
    assert(disk_lbl->responses
        == Map::<ID, DiskResponse>::empty()) by {
        assert(resps.is_empty());
        assert_maps_equal!(
            disk_lbl->responses,
            Map::<ID, DiskResponse>::empty(),
            id => {
                if disk_lbl->responses.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] resps.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(post.disk.requests
        == pre.disk.requests.union_prefer_right(req_map));
    assert(post.disk.responses == pre.disk.responses);
    assert(post.disk.content == pre.disk.content);
    assert(req_map.dom().disjoint(pre.disk.requests.dom()));
    assert(req_map.dom().disjoint(pre.disk.responses.dom()));
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    reveal(UnifiedCacheBetreeSystem::State::cache_io_begin);
    let updated = Map::new(
        |id| req_map.contains_key(id),
        |id| req_map[id].addr(),
    );
    assert(post_state == UnifiedCacheBetreeSystem::State{
        cache: new_cache,
        outstanding_cache_reqs:
            pre_state.outstanding_cache_reqs
                .union_prefer_right(updated),
        ..pre_state
    });
    let cache_lbl = Cache::Label::DiskOps{
        requests: req_map.values(),
        responses: Map::empty(),
    };
    assert(Cache::State::next(
        pre_state.cache,
        post_state.cache,
        cache_lbl,
    ));
    cache_disk_ops_begin_preserves_unready_cache_clean_inv(
        pre,
        post,
        req_map.values(),
    );
    cache_disk_ops_begin_preserves_persistent_branch_cache_clean_inv(
        pre,
        post,
        req_map.values(),
    );

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    assert(journal_pre.same_except_cache_and_disk(
        journal_post,
    ));
    assert(journal_pre.superblock_loaded()) by {
        assert(!(pre_state.recovery_state is Begin));
        assert(!(pre_state.recovery_state
            is AwaitingSuperblock));
        assert(pre_state.persistent_image is Some);
    }
    journal_pre.cache_disk_ops_begin_refines(
        journal_post,
        req_map.values(),
    );
    branch_pre.cache_disk_ops_begin_refines(
        branch_post,
        req_map.values(),
    );
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::Internal,
    ));
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        let sync_req_id = pre_state.sync_phase.req_id();
        if sync_req_id is Some {
            let id = sync_req_id.unwrap();
            if req_map.contains_key(id) {
                assert(post.disk.requests[id] == req_map[id]);
                assert(updated.contains_key(id));
                assert(updated[id]
                    != spec_superblock_addr());
                if unified_cache_betree_superblock_write_pending(
                    post,
                ) {
                    assert(post.disk.requests[id].addr()
                        == spec_superblock_addr());
                    assert(false);
                }
            } else if pre.disk.requests.contains_key(id) {
                assert(post.disk.requests[id]
                    == pre.disk.requests[id]);
            }
        }
    }
    if branch_pre.control.loading {
        let branch_lbl =
            CrashAwareCachingDiskBranchBetree::Label::
                RecoverMetadata {
                    recovery_op:
                        BetreeMetadataRecoveryLabel::
                            DiskInternal,
                };
        assert(crate::implementation::
            CrashAwareCachingDiskBetreeSystem_v::
                branch_internal_label(branch_lbl)) by {
            reveal(crate::implementation::
                CrashAwareCachingDiskBetreeSystem_v::
                    branch_internal_label);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            component_internals(
                src,
                dst,
                target_lbl,
                dst.journal,
                dst.branch,
                branch_lbl,
            )
        ) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                component_internals);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBetreeSystem::Step::
                component_internals(
                    dst.journal,
                    dst.branch,
                    branch_lbl,
                ),
        )) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                next_by);
        }
    } else if branch_pre.control.metadata_loaded {
        let branch_lbl =
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::Internal,
                    deallocs: Set::empty(),
                };
        assert(crate::implementation::
            CrashAwareCachingDiskBetreeSystem_v::
                branch_internal_label(branch_lbl)) by {
            reveal(crate::implementation::
                CrashAwareCachingDiskBetreeSystem_v::
                    branch_internal_label);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            component_internals(
                src,
                dst,
                target_lbl,
                dst.journal,
                dst.branch,
                branch_lbl,
            )
        ) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                component_internals);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBetreeSystem::Step::
                component_internals(
                    dst.journal,
                    dst.branch,
                    branch_lbl,
                ),
        )) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                next_by);
        }
    } else {
        assert(dst.branch == src.branch);
        assert(CrashAwareCachingDiskBetreeSystem::State::
            journal_internal(
                src,
                dst,
                target_lbl,
                dst.journal,
            )
        ) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                journal_internal);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBetreeSystem::Step::
                journal_internal(dst.journal),
        )) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                next_by);
        }
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);

    assert(dst.progress == src.progress);
    assert(dst.sync_reqs == src.sync_reqs);
    assert(dst.free_aus == src.free_aus);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    cache_io_begin_preserves_shared_cache_disk_inv(
        pre,
        post,
        req_map,
    );
    cache_io_begin_preserves_protocol_invs(
        pre,
        post,
        req_map,
    );
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    )) by {
        let phase_req_id = pre_state.sync_phase.req_id();
        if phase_req_id is Some {
            let id = phase_req_id.unwrap();
            assert(unified_cache_betree_superblock_cache_id_inv(
                pre,
            ));
            assert(disk_has_pending_id(pre.disk, id));
            assert(!req_map.contains_key(id)) by {
                if req_map.contains_key(id) {
                    if pre.disk.requests.contains_key(id) {
                        assert(req_map.dom().disjoint(
                            pre.disk.requests.dom(),
                        ));
                    } else {
                        assert(pre.disk.responses.contains_key(id));
                        assert(req_map.dom().disjoint(
                            pre.disk.responses.dom(),
                        ));
                    }
                    assert(false);
                }
            }
            assert(!updated.contains_key(id));
            assert(!post_state.outstanding_cache_reqs
                .contains_key(id));
            if pre.disk.requests.contains_key(id) {
                assert(post.disk.requests.contains_key(id));
            } else {
                assert(post.disk.responses.contains_key(id));
            }
        }
    }
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
        assert(branch_post.branch_projection_aus()
            == branch_pre.branch_projection_aus());
    }
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_cache_io_end_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    resp_map: Map<ID, DiskResponse>,
    new_cache: Cache::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::cache_io_end(
                resp_map,
                new_cache,
                reqs,
                resps,
            ),
            lbl->info,
        ),
        UnifiedCacheBetreeSystem::State::next_by(
            pre.program.state,
            post.program.state,
            UnifiedCacheBetreeSystem::Label::Disk,
            UnifiedCacheBetreeSystem::Step::cache_io_end(
                resp_map,
                new_cache,
                reqs,
                resps,
            ),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let disk_lbl = DiskLabel::DiskOps{
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheBetreeSystem::State::next_by);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(multiset_to_map(resps) == resp_map);
    assert(disk_lbl->responses == resp_map);
    assert(disk_lbl->requests
        == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            disk_lbl->requests,
            Map::<ID, DiskRequest>::empty(),
            id => {
                if disk_lbl->requests.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] reqs.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(post.disk.requests == pre.disk.requests);
    assert(post.disk.responses
        == pre.disk.responses.remove_keys(resp_map.dom()));
    assert(post.disk.content == pre.disk.content);
    assert(resp_map <= pre.disk.responses);
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    reveal(UnifiedCacheBetreeSystem::State::cache_io_end);
    let finished =
        pre_state.outstanding_cache_reqs
            .restrict(resp_map.dom())
            .invert();
    let cache_resps = Map::new(
        |addr| finished.contains_key(addr),
        |addr| resp_map[finished[addr]],
    );
    assert(post_state == UnifiedCacheBetreeSystem::State{
        cache: new_cache,
        outstanding_cache_reqs:
            pre_state.outstanding_cache_reqs
                .remove_keys(resp_map.dom()),
        ..pre_state
    });
    let cache_lbl = Cache::Label::DiskOps{
        requests: Set::empty(),
        responses: cache_resps,
    };
    assert(Cache::State::next(
        pre_state.cache,
        post_state.cache,
        cache_lbl,
    ));
    cache_responses_coherent(pre, resp_map, cache_resps);
    assert(!cache_resps
        .contains_key(spec_superblock_addr())) by {
        if cache_resps.contains_key(
            spec_superblock_addr(),
        ) {
            assert(finished.contains_key(
                spec_superblock_addr(),
            ));
            Cache::State::invert_contains_pair(
                pre_state.outstanding_cache_reqs
                    .restrict(resp_map.dom()),
                spec_superblock_addr(),
            );
            let id = finished[spec_superblock_addr()];
            assert(pre_state.outstanding_cache_reqs[id]
                == spec_superblock_addr());
            assert(unified_cache_betree_cache_request_inv(pre));
            assert(false);
        }
    }

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    assert(journal_pre.same_except_cache_and_disk(
        journal_post,
    ));
    assert(journal_pre.superblock_loaded()) by {
        assert(!(pre_state.recovery_state is Begin));
        assert(!(pre_state.recovery_state
            is AwaitingSuperblock));
        assert(pre_state.persistent_image is Some);
    }
    journal_pre.cache_disk_ops_end_refines(
        journal_post,
        cache_resps,
    );
    branch_pre.cache_disk_ops_end_refines(
        branch_post,
        cache_resps,
    );
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::Internal,
    ));
    assert(dst.superblockstore == src.superblockstore) by {
        assert(post_state.sync_phase == pre_state.sync_phase);
        let phase_req_id = pre_state.sync_phase.req_id();
        if phase_req_id is Some {
            let id = phase_req_id.unwrap();
            assert(unified_cache_betree_superblock_cache_id_inv(
                pre,
            ));
            assert(!pre_state.outstanding_cache_reqs
                .contains_key(id));
            assert(!resp_map.contains_key(id));
            assert(post.disk.responses.contains_key(id)
                == pre.disk.responses.contains_key(id));
        }
    }
    if branch_pre.control.loading {
        let branch_lbl =
            CrashAwareCachingDiskBranchBetree::Label::
                RecoverMetadata {
                    recovery_op:
                        BetreeMetadataRecoveryLabel::
                            DiskInternal,
                };
        assert(crate::implementation::
            CrashAwareCachingDiskBetreeSystem_v::
                branch_internal_label(branch_lbl)) by {
            reveal(crate::implementation::
                CrashAwareCachingDiskBetreeSystem_v::
                    branch_internal_label);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            component_internals(
                src,
                dst,
                target_lbl,
                dst.journal,
                dst.branch,
                branch_lbl,
            )
        ) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                component_internals);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBetreeSystem::Step::
                component_internals(
                    dst.journal,
                    dst.branch,
                    branch_lbl,
                ),
        )) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                next_by);
        }
    } else if branch_pre.control.metadata_loaded {
        let branch_lbl =
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op: CachingDiskBranchBetree::Label::Internal,
                    deallocs: Set::empty(),
                };
        assert(crate::implementation::
            CrashAwareCachingDiskBetreeSystem_v::
                branch_internal_label(branch_lbl)) by {
            reveal(crate::implementation::
                CrashAwareCachingDiskBetreeSystem_v::
                    branch_internal_label);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            component_internals(
                src,
                dst,
                target_lbl,
                dst.journal,
                dst.branch,
                branch_lbl,
            )
        ) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                component_internals);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBetreeSystem::Step::
                component_internals(
                    dst.journal,
                    dst.branch,
                    branch_lbl,
                ),
        )) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                next_by);
        }
    } else {
        assert(dst.branch == src.branch);
        assert(CrashAwareCachingDiskBetreeSystem::State::
            journal_internal(
                src,
                dst,
                target_lbl,
                dst.journal,
            )
        ) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                journal_internal);
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
            src,
            dst,
            target_lbl,
            CrashAwareCachingDiskBetreeSystem::Step::
                journal_internal(dst.journal),
        )) by {
            reveal(CrashAwareCachingDiskBetreeSystem::State::
                next_by);
        }
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    cache_io_end_preserves_shared_cache_disk_inv(
        pre,
        post,
        cache_resps,
    );
    cache_io_end_preserves_protocol_invs(
        pre,
        post,
        resp_map,
        cache_resps,
    );
    cache_disk_ops_end_preserves_unready_cache_clean_inv(
        pre,
        post,
        cache_resps,
    );
    cache_disk_ops_end_preserves_persistent_branch_cache_clean_inv(
        pre,
        post,
        cache_resps,
    );
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    )) by {
        let phase_req_id = pre_state.sync_phase.req_id();
        if phase_req_id is Some {
            let id = phase_req_id.unwrap();
            assert(unified_cache_betree_superblock_cache_id_inv(
                pre,
            ));
            assert(!resp_map.contains_key(id));
            assert(!post_state.outstanding_cache_reqs
                .contains_key(id));
            if pre.disk.requests.contains_key(id) {
                assert(post.disk.requests.contains_key(id));
            } else {
                assert(pre.disk.responses.contains_key(id));
                assert(post.disk.responses.contains_key(id));
            }
        }
    }
    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
        assert(branch_post.branch_projection_aus()
            == branch_pre.branch_projection_aus());
    }
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_execute_journal_sync_begin_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    image: AbstractSuperblockImage,
    journal_reads: Map<Address, RawPage>,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::
                execute_journal_sync_begin(
                    image,
                    journal_reads,
                    new_cache,
                    new_journal,
                    reqs,
                    resps,
                ),
            lbl->info,
        ),
        UnifiedCacheBetreeSystem::State::
            execute_journal_sync_begin(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                image,
                journal_reads,
                new_cache,
                new_journal,
                reqs,
                resps,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let disk_lbl = DiskLabel::DiskOps {
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheBetreeSystem::State::
        execute_journal_sync_begin);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(resps.is_empty());
    assert(disk_lbl->requests
        == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            disk_lbl->requests,
            Map::<ID, DiskRequest>::empty(),
            id => {
                if disk_lbl->requests.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] reqs.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(disk_lbl->responses
        == Map::<ID, DiskResponse>::empty()) by {
        assert_maps_equal!(
            disk_lbl->responses,
            Map::<ID, DiskResponse>::empty(),
            id => {
                if disk_lbl->responses.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] resps.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(post.disk.requests == pre.disk.requests) by {
        assert_maps_equal!(
            post.disk.requests,
            pre.disk.requests,
            id => {}
        );
    }
    assert(post.disk.responses == pre.disk.responses) by {
        assert_maps_equal!(
            post.disk.responses,
            pre.disk.responses,
            id => {}
        );
    }
    assert(post.disk.content == pre.disk.content);
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    assert(post_state == UnifiedCacheBetreeSystem::State {
        cache: new_cache,
        journal: new_journal,
        sync_phase:
            AtomicBetreeSyncPhase::Preparing{
                image,
                journal_ready: false,
                branch_ready: true,
            },
        ..pre_state
    });
    let atomic_journal_lbl =
        AtomicJournalState::Label::CommitStart {
            snapshot: image.journal_snapshot,
            seq_end: image.journal_seq_end,
            reads:
                crate::implementation::JournalTypes_v::
                    to_journal_records(journal_reads),
        };
    AtomicJournalState::State::commit_start_effect(
        pre_state.journal,
        post_state.journal,
        atomic_journal_lbl,
    );
    Cache::State::access_read_only_is_noop(
        pre_state.cache,
        post_state.cache,
        journal_reads,
    );
    assert(post_state.cache == pre_state.cache);

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheJournalRefinement::commit_start_refines(
        journal_pre,
        journal_post,
        image.journal_snapshot,
        image.journal_seq_end,
        journal_reads,
    );
    assert(branch_post.i() == branch_pre.i());
    assert(branch_post.inv()) by {
        reveal(UnifiedCacheBranchBetreeRefinement::
            UnifiedCacheBranchBetreeSource::inv);
    }
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(src.branch.ephemeral is Known);
    assert(betree_superblock_image_wf(image));
    assert(betree_metadata_from_superblock(image)
        == src.branch.persistent.metadata);
    assert(dst.branch == src.branch);
    assert(dst.superblockstore == src.superblockstore);
    assert(CrashAwareCachingDiskBetreeSystem::State::
        journal_commit_start(
            src,
            dst,
            target_lbl,
            dst.journal,
            image,
        )
    ) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            journal_commit_start);
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            journal_commit_start(
                dst.journal,
                image,
            ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_response_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    ));
    assert(unified_cache_betree_sync_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(post_state.journal.journal
            == pre_state.journal.journal);
        assert(post_state.journal.mini_allocator
            == pre_state.journal.mini_allocator);
        assert(post_state.journal.ready());
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
        assert(branch_post.branch_projection_aus()
            == branch_pre.branch_projection_aus());
    }
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_execute_journal_superblock_write_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    req_id: ID,
    req: DiskRequest,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::
                execute_sync_superblock_write(
                    req_id,
                    req,
                    reqs,
                    resps,
                ),
            lbl->info,
        ),
        pre.program.state.branch.control.frozen is None,
        UnifiedCacheBetreeSystem::State::
            execute_sync_superblock_write(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                req_id,
                req,
                reqs,
                resps,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let req_map =
        Map::<ID, DiskRequest>::empty().insert(req_id, req);
    let disk_lbl = DiskLabel::DiskOps {
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };
    let image = pre_state.sync_phase.image().unwrap();

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheBetreeSystem::State::
        execute_sync_superblock_write);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs == Multiset::singleton((req_id, req)));
    assert(reqs == crate::implementation::
        MultisetMapRelation_v::multiset_map_singleton(
            req_id,
            req,
        ));
    multiset_map_singleton_ensures(req_id, req);
    assert(disk_lbl->requests == req_map);
    assert(disk_lbl->responses
        == Map::<ID, DiskResponse>::empty()) by {
        assert_maps_equal!(
            disk_lbl->responses,
            Map::<ID, DiskResponse>::empty(),
            id => {
                if disk_lbl->responses.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] resps.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(post.disk.content == pre.disk.content);
    assert(post.disk.responses == pre.disk.responses) by {
        assert_maps_equal!(
            post.disk.responses,
            pre.disk.responses,
            id => {}
        );
    }
    assert(post.disk.requests
        == pre.disk.requests.union_prefer_right(req_map));
    assert(req_map.dom().disjoint(
        pre.disk.requests.dom(),
    ));
    assert(req_map.dom().disjoint(
        pre.disk.responses.dom(),
    ));
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    assert(post_state == UnifiedCacheBetreeSystem::State {
        sync_phase:
            AtomicBetreeSyncPhase::
                SuperblockWriteIssued {
                    req_id,
                    image,
                },
        ..pre_state
    });
    assert(!pre_state.outstanding_cache_reqs
        .contains_key(req_id)) by {
        if pre_state.outstanding_cache_reqs
            .contains_key(req_id)
        {
            assert(disk_has_pending_id(pre.disk, req_id));
            if pre.disk.requests.contains_key(req_id) {
                assert(req_map.dom().disjoint(
                    pre.disk.requests.dom(),
                ));
            } else {
                assert(pre.disk.responses.contains_key(req_id));
                assert(req_map.dom().disjoint(
                    pre.disk.responses.dom(),
                ));
            }
            assert(false);
        }
    }
    assert(unified_cache_betree_sync_state_inv(pre));

    assert(AtomicJournalState::State::commit_prepared(
        pre_state.journal,
        pre_state.journal,
        AtomicJournalState::Label::CommitPrepared,
    )) by {
        assert(unified_cache_betree_sync_state_inv(pre));
        reveal(AtomicJournalState::State::commit_prepared);
    }
    assert(AtomicJournalState::State::next(
        pre_state.journal,
        pre_state.journal,
        AtomicJournalState::Label::CommitPrepared,
    )) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre_state.journal,
            pre_state.journal,
            AtomicJournalState::Label::CommitPrepared,
            AtomicJournalState::Step::commit_prepared(),
        ));
    }
    assert(post_state.journal == pre_state.journal);

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheJournalRefinement::commit_prepared_refines(
        journal_pre,
        journal_post,
    );
    assert(branch_post.i() == branch_pre.i());
    assert(branch_post.inv()) by {
        reveal(UnifiedCacheBranchBetreeRefinement::
            UnifiedCacheBranchBetreeSource::inv);
    }
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;
    let raw_page = req->data;
    assert(src.branch.frozen is None);
    assert(dst.branch == src.branch);
    assert(src.superblockstore.in_flight is None);
    assert(!src.superblockstore.landed);
    assert(dst.superblockstore.in_flight == Some(raw_page));
    assert(!dst.superblockstore.landed);
    assert(dst.superblockstore.persistent
        == src.superblockstore.persistent);
    assert(SuperblockStore::State::next_by(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Write{raw: raw_page},
        SuperblockStore::Step::write(),
    )) by {
        reveal(SuperblockStore::State::next_by);
        reveal(SuperblockStore::State::write);
    }
    reveal(SuperblockStore::State::next);
    assert(CrashAwareCachingDiskBetreeSystem::State::
        journal_commit_prepared(
            src,
            dst,
            target_lbl,
            dst.journal,
            dst.superblockstore,
            raw_page,
            image,
        )
    ) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            journal_commit_prepared);
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            journal_commit_prepared(
                dst.journal,
                dst.superblockstore,
                raw_page,
                image,
            ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_response_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    )) by {
        assert(disk_has_pending_id(post.disk, req_id));
    }
    assert(unified_cache_betree_sync_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
        assert(branch_post.branch_projection_aus()
            == branch_pre.branch_projection_aus());
    }
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_execute_journal_sync_end_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    journal_discarded_aus:
        Set<crate::disk::GenericDisk_v::AU>,
    new_journal: AtomicJournalState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::
                execute_journal_sync_end(
                    journal_discarded_aus,
                    new_journal,
                    reqs,
                    resps,
                ),
            lbl->info,
        ),
        UnifiedCacheBetreeSystem::State::
            execute_journal_sync_end(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                journal_discarded_aus,
                new_journal,
                reqs,
                resps,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let req_id = pre_state.sync_phase.req_id().unwrap();
    let image = pre_state.sync_phase.image().unwrap();
    let write_resp = DiskResponse::WriteResp{};
    let resp_map =
        Map::<ID, DiskResponse>::empty().insert(
            req_id,
            write_resp,
        );
    let disk_lbl = DiskLabel::DiskOps {
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheBetreeSystem::State::
        execute_journal_sync_end);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(resps
        == Multiset::singleton((req_id, write_resp)));
    assert(resps == multiset_map_singleton(
        req_id,
        write_resp,
    ));
    multiset_map_singleton_ensures(req_id, write_resp);
    assert(disk_lbl->requests
        == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            disk_lbl->requests,
            Map::<ID, DiskRequest>::empty(),
            id => {
                if disk_lbl->requests.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] reqs.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(disk_lbl->responses == resp_map);
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(resp_map <= pre.disk.responses);
    assert(resp_map.contains_key(req_id));
    assert(resp_map[req_id] == write_resp);
    assert(post.disk.requests == pre.disk.requests);
    assert(post.disk.responses
        == pre.disk.responses.remove_keys(resp_map.dom()));
    assert(post.disk.content == pre.disk.content);
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    assert(unified_cache_betree_sync_state_inv(pre));
    assert(post_state == UnifiedCacheBetreeSystem::State {
        free_aus:
            pre_state.free_aus + journal_discarded_aus,
        journal: new_journal,
        persistent_image: Some(image),
        sync_phase: AtomicBetreeSyncPhase::None,
        ..pre_state
    });
    let atomic_journal_lbl =
        AtomicJournalState::Label::CommitComplete {
            require_end:
                pre_state.journal.journal.seq_end(),
            discarded_aus: journal_discarded_aus,
        };
    AtomicJournalState::State::commit_complete_effect(
        pre_state.journal,
        post_state.journal,
        atomic_journal_lbl,
    );

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheJournalRefinement::commit_complete_refines(
        journal_pre,
        journal_post,
        pre_state.journal.journal.seq_end(),
        journal_discarded_aus,
    );

    assert(branch_post.persistent_metadata_i()
        == branch_pre.persistent_metadata_i()) by {
        assert(betree_metadata_from_superblock(image)
            == pre_state.branch.control.metadata);
        assert(branch_pre.control.metadata
            == branch_pre.persistent_metadata_i());
    }
    assert(branch_post.persistent_tight_betree_i()
        == branch_pre.persistent_tight_betree_i());
    assert(branch_post.persistent_branch_roots_i()
        == branch_pre.persistent_branch_roots_i());
    assert(branch_post.persistent_branch_summary_i()
        == branch_pre.persistent_branch_summary_i());
    assert(branch_post.persistent_branch_image_i()
        == branch_pre.persistent_branch_image_i());
    assert(branch_post.branch_projection_aus()
        == branch_pre.branch_projection_aus());
    assert(branch_post.branch_caching_disk_i()
        == branch_pre.branch_caching_disk_i());
    assert(branch_post.i() == branch_pre.i());
    assert(branch_post.inv()) by {
        reveal(UnifiedCacheBranchBetreeRefinement::
            UnifiedCacheBranchBetreeSource::inv);
    }
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(pre.disk.responses.contains_key(req_id));
    assert(pre.disk.responses[req_id] == write_resp);
    assert(!pre.disk.requests.contains_key(req_id)) by {
        assert(pre.disk.requests.dom().disjoint(
            pre.disk.responses.dom(),
        ));
    }
    reveal(unified_cache_betree_superblock_write_pending);
    reveal(unified_cache_betree_superblock_landed);
    assert(src.branch.frozen is None);
    assert(dst.branch == src.branch);
    assert(src.superblockstore.in_flight is None);
    assert(src.superblockstore.landed);
    assert(dst.superblockstore.in_flight is None);
    assert(!dst.superblockstore.landed);
    assert(dst.superblockstore.persistent
        == src.superblockstore.persistent);
    assert(SuperblockStore::State::next_by(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Complete,
        SuperblockStore::Step::complete(),
    )) by {
        reveal(SuperblockStore::State::next_by);
        reveal(SuperblockStore::State::complete);
    }
    reveal(SuperblockStore::State::next);
    assert(CrashAwareCachingDiskBetreeSystem::State::
        journal_commit_complete(
            src,
            dst,
            target_lbl,
            dst.journal,
            dst.superblockstore,
            journal_discarded_aus,
        )
    ) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            journal_commit_complete);
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            journal_commit_complete(
                dst.journal,
                dst.superblockstore,
                journal_discarded_aus,
            ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post)) by {
        assert(!pre_state.outstanding_cache_reqs
            .contains_key(req_id));
    }
    assert(unified_cache_betree_cache_response_inv(post)) by {
        assert(!pre_state.outstanding_cache_reqs
            .contains_key(req_id));
    }
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    ));
    assert(unified_cache_betree_sync_state_inv(post));
    assert(post_state.free_aus
        == pre_state.free_aus
            + journal_discarded_aus
            + Set::empty()) by {
        assert_sets_equal!(
            post_state.free_aus,
            pre_state.free_aus
                + journal_discarded_aus
                + Set::empty(),
            au => {}
        );
    }
    sync_discard_preserves_allocation_inv(
        pre,
        post,
        journal_discarded_aus,
        Set::empty(),
    );
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_execute_store_sync_begin_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    image: AbstractSuperblockImage,
    journal_reads: Map<Address, RawPage>,
    new_cache: Cache::State,
    new_journal: AtomicJournalState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::
                execute_store_sync_begin(
                    image,
                    journal_reads,
                    new_cache,
                    new_journal,
                    reqs,
                    resps,
                ),
            lbl->info,
        ),
        UnifiedCacheBetreeSystem::State::
            execute_store_sync_begin(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                image,
                journal_reads,
                new_cache,
                new_journal,
                reqs,
                resps,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let disk_lbl = DiskLabel::DiskOps {
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheBetreeSystem::State::
        execute_store_sync_begin);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(resps.is_empty());
    assert(disk_lbl->requests
        == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            disk_lbl->requests,
            Map::<ID, DiskRequest>::empty(),
            id => {
                if disk_lbl->requests.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] reqs.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(disk_lbl->responses
        == Map::<ID, DiskResponse>::empty()) by {
        assert_maps_equal!(
            disk_lbl->responses,
            Map::<ID, DiskResponse>::empty(),
            id => {
                if disk_lbl->responses.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] resps.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(post.disk.requests == pre.disk.requests) by {
        assert_maps_equal!(
            post.disk.requests,
            pre.disk.requests,
            id => {}
        );
    }
    assert(post.disk.responses == pre.disk.responses) by {
        assert_maps_equal!(
            post.disk.responses,
            pre.disk.responses,
            id => {}
        );
    }
    assert(post.disk.content == pre.disk.content);
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    Cache::State::access_read_only_is_noop(
        pre_state.cache,
        post_state.cache,
        journal_reads,
    );
    assert(post_state.cache == pre_state.cache);
    let atomic_journal_lbl =
        AtomicJournalState::Label::CommitStart {
            snapshot: image.journal_snapshot,
            seq_end: image.journal_seq_end,
            reads:
                crate::implementation::JournalTypes_v::
                    to_journal_records(journal_reads),
        };
    AtomicJournalState::State::commit_start_effect(
        pre_state.journal,
        post_state.journal,
        atomic_journal_lbl,
    );

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheJournalRefinement::commit_start_refines(
        journal_pre,
        journal_post,
        image.journal_snapshot,
        image.journal_seq_end,
        journal_reads,
    );
    UnifiedCacheBranchBetreeRefinement::
        store_commit_start_refines(
            branch_pre,
            branch_post,
            image,
            journal_reads,
        );
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(dst.superblockstore == src.superblockstore);
    assert(CrashAwareCachingDiskBetreeSystem::State::
        store_commit_start(
            src,
            dst,
            target_lbl,
            dst.journal,
            dst.branch,
            image,
        )
    ) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            store_commit_start);
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            store_commit_start(
                dst.journal,
                dst.branch,
                image,
            ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_response_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    ));
    assert(unified_cache_betree_sync_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
        assert(branch_post.branch_projection_aus()
            =~= branch_pre.branch_projection_aus());
    }
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_execute_store_superblock_write_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    req_id: ID,
    req: DiskRequest,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::
                execute_sync_superblock_write(
                    req_id,
                    req,
                    reqs,
                    resps,
                ),
            lbl->info,
        ),
        pre.program.state.branch.control.frozen is Some,
        UnifiedCacheBetreeSystem::State::
            execute_sync_superblock_write(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                req_id,
                req,
                reqs,
                resps,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let req_map =
        Map::<ID, DiskRequest>::empty().insert(req_id, req);
    let disk_lbl = DiskLabel::DiskOps {
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };
    let image = pre_state.sync_phase.image().unwrap();

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheBetreeSystem::State::
        execute_sync_superblock_write);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs == Multiset::singleton((req_id, req)));
    assert(reqs == multiset_map_singleton(req_id, req));
    multiset_map_singleton_ensures(req_id, req);
    assert(disk_lbl->requests == req_map);
    assert(disk_lbl->responses
        == Map::<ID, DiskResponse>::empty()) by {
        assert_maps_equal!(
            disk_lbl->responses,
            Map::<ID, DiskResponse>::empty(),
            id => {
                if disk_lbl->responses.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] resps.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(post.disk.content == pre.disk.content);
    assert(post.disk.responses == pre.disk.responses) by {
        assert_maps_equal!(
            post.disk.responses,
            pre.disk.responses,
            id => {}
        );
    }
    assert(post.disk.requests
        == pre.disk.requests.union_prefer_right(req_map));
    assert(req_map.dom().disjoint(
        pre.disk.requests.dom(),
    ));
    assert(req_map.dom().disjoint(
        pre.disk.responses.dom(),
    ));
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    assert(unified_cache_betree_sync_state_inv(pre));
    assert(!pre_state.outstanding_cache_reqs
        .contains_key(req_id)) by {
        if pre_state.outstanding_cache_reqs
            .contains_key(req_id)
        {
            assert(disk_has_pending_id(pre.disk, req_id));
            if pre.disk.requests.contains_key(req_id) {
                assert(req_map.dom().disjoint(
                    pre.disk.requests.dom(),
                ));
            } else {
                assert(pre.disk.responses.contains_key(req_id));
                assert(req_map.dom().disjoint(
                    pre.disk.responses.dom(),
                ));
            }
            assert(false);
        }
    }
    let frozen = pre_state.branch.control.frozen.unwrap();
    assert(post_state.cache == pre_state.cache);
    assert forall |slot: Slot|
        #[trigger] pre_state.cache.entries.contains_key(slot)
        && pre_state.cache.entries[slot] is Filled
        && frozen.aus.contains(
            pre_state.cache.entries[slot].get_addr().au,
        )
        implies pre_state.cache.status_map[slot] is Clean
    by {
        assert(unified_cache_betree_branch_clean_aus(
            pre_state,
        ).contains(
            pre_state.cache.entries[slot].get_addr().au,
        ));
        assert(unified_cache_betree_persistent_branch_cache_clean_inv(
            pre,
        ));
    }

    assert(AtomicJournalState::State::commit_prepared(
        pre_state.journal,
        pre_state.journal,
        AtomicJournalState::Label::CommitPrepared,
    )) by {
        assert(unified_cache_betree_sync_state_inv(pre));
        reveal(AtomicJournalState::State::commit_prepared);
    }
    assert(AtomicJournalState::State::next(
        pre_state.journal,
        pre_state.journal,
        AtomicJournalState::Label::CommitPrepared,
    )) by {
        reveal(AtomicJournalState::State::next);
        reveal(AtomicJournalState::State::next_by);
        assert(AtomicJournalState::State::next_by(
            pre_state.journal,
            pre_state.journal,
            AtomicJournalState::Label::CommitPrepared,
            AtomicJournalState::Step::commit_prepared(),
        ));
    }
    assert(post_state.journal == pre_state.journal);

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheJournalRefinement::commit_prepared_refines(
        journal_pre,
        journal_post,
    );
    UnifiedCacheBranchBetreeRefinement::
        store_commit_prepared_refines(
            branch_pre,
            branch_post,
        );
    assert(unified_cache_betree_persistent_branch_cache_clean_inv(
        post,
    )) by {
        assert forall |slot: Slot|
            #[trigger] post_state.cache.entries
                .contains_key(slot)
            && post_state.cache.entries[slot] is Filled
            && unified_cache_betree_branch_clean_aus(
                post_state,
            ).contains(
                post_state.cache.entries[slot].get_addr().au,
            )
            implies post_state.cache.status_map[slot]
                is Clean
        by {
            let au =
                post_state.cache.entries[slot].get_addr().au;
            if pre_state.branch.control.persistent_aus
                .contains(au)
            {
                assert(unified_cache_betree_branch_clean_aus(
                    pre_state,
                ).contains(au));
                assert(pre_state.cache.status_map[slot]
                    is Clean);
            } else {
                assert(frozen.aus.contains(au));
            }
        }
    }
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;
    let raw_page = req->data;
    assert(src.superblockstore.in_flight is None);
    assert(!src.superblockstore.landed);
    assert(dst.superblockstore.in_flight == Some(raw_page));
    assert(!dst.superblockstore.landed);
    assert(dst.superblockstore.persistent
        == src.superblockstore.persistent);
    assert(SuperblockStore::State::next_by(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Write{raw: raw_page},
        SuperblockStore::Step::write(),
    )) by {
        reveal(SuperblockStore::State::next_by);
        reveal(SuperblockStore::State::write);
    }
    reveal(SuperblockStore::State::next);
    assert(CrashAwareCachingDiskBetreeSystem::State::
        store_commit_prepared(
            src,
            dst,
            target_lbl,
            dst.journal,
            dst.branch,
            dst.superblockstore,
            raw_page,
            image,
        )
    ) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            store_commit_prepared);
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            store_commit_prepared(
                dst.journal,
                dst.branch,
                dst.superblockstore,
                raw_page,
                image,
            ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_response_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    )) by {
        assert(disk_has_pending_id(post.disk, req_id));
    }
    assert(unified_cache_betree_sync_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post)) by {
        assert(journal_post.journal_projection_aus()
            =~= journal_pre.journal_projection_aus());
        assert(branch_post.branch_projection_aus()
            =~= branch_pre.branch_projection_aus());
    }
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_execute_store_sync_end_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
    journal_discarded_aus:
        Set<crate::disk::GenericDisk_v::AU>,
    new_journal: AtomicJournalState::State,
    reqs: Multiset<(ID, DiskRequest)>,
    resps: Multiset<(ID, DiskResponse)>,
)
    requires
        SystemModel::State::program_disk(
            pre,
            post,
            lbl,
            new_program,
            new_disk,
        ),
        refinement_inv(pre),
        UnifiedCacheBetreeProgramModel::disk_step_matches_info(
            pre.program.state,
            UnifiedCacheBetreeSystem::Step::
                execute_store_sync_end(
                    journal_discarded_aus,
                    new_journal,
                    reqs,
                    resps,
                ),
            lbl->info,
        ),
        UnifiedCacheBetreeSystem::State::
            execute_store_sync_end(
                pre.program.state,
                post.program.state,
                UnifiedCacheBetreeSystem::Label::Disk,
                journal_discarded_aus,
                new_journal,
                reqs,
                resps,
            ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let req_id = pre_state.sync_phase.req_id().unwrap();
    let image = pre_state.sync_phase.image().unwrap();
    let frozen = pre_state.branch.control.frozen.unwrap();
    let branch_discarded_aus =
        pre_state.branch.control.persistent_aus
            - frozen.aus
            - pre_state.branch.betree.owned_aus();
    let write_resp = DiskResponse::WriteResp{};
    let resp_map =
        Map::<ID, DiskResponse>::empty().insert(
            req_id,
            write_resp,
        );
    let disk_lbl = DiskLabel::DiskOps {
        requests: multiset_to_map(lbl->info.reqs),
        responses: multiset_to_map(lbl->info.resps),
    };

    reveal(SystemModel::State::program_disk);
    reveal(UnifiedCacheBetreeSystem::State::
        execute_store_sync_end);
    assert(lbl is ProgramDiskOp);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(reqs == lbl->info.reqs);
    assert(resps == lbl->info.resps);
    assert(reqs.is_empty());
    assert(resps
        == Multiset::singleton((req_id, write_resp)));
    assert(resps == multiset_map_singleton(
        req_id,
        write_resp,
    ));
    multiset_map_singleton_ensures(req_id, write_resp);
    assert(disk_lbl->requests
        == Map::<ID, DiskRequest>::empty()) by {
        assert_maps_equal!(
            disk_lbl->requests,
            Map::<ID, DiskRequest>::empty(),
            id => {
                if disk_lbl->requests.contains_key(id) {
                    let pair = choose |pair|
                        #[trigger] reqs.contains(pair)
                            && pair.0 == id;
                    assert(false);
                }
            }
        );
    }
    assert(disk_lbl->responses == resp_map);
    assert(DiskModel::next(pre.disk, post.disk, disk_lbl));
    assert(AsyncDisk::State::disk_ops(
        pre.disk,
        post.disk,
        disk_lbl,
    )) by {
        reveal(AsyncDisk::State::next);
        reveal(AsyncDisk::State::next_by);
        let disk_step = choose |step: AsyncDisk::Step|
            AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                disk_lbl,
                step,
            );
        match disk_step {
            AsyncDisk::Step::disk_ops() => {}
            _ => {
                assert(false);
            }
        }
    }
    reveal(AsyncDisk::State::disk_ops);
    assert(resp_map <= pre.disk.responses);
    assert(resp_map.contains_key(req_id));
    assert(resp_map[req_id] == write_resp);
    assert(post.disk.requests == pre.disk.requests);
    assert(post.disk.responses
        == pre.disk.responses.remove_keys(resp_map.dom()));
    assert(post.disk.content == pre.disk.content);
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        disk_lbl,
    );
    assert(post.disk.inv());

    assert(unified_cache_betree_sync_state_inv(pre));
    assert(post_state == UnifiedCacheBetreeSystem::State {
        free_aus:
            pre_state.free_aus
                + journal_discarded_aus
                + branch_discarded_aus,
        journal: new_journal,
        branch: post_state.branch,
        persistent_image: Some(image),
        sync_phase: AtomicBetreeSyncPhase::None,
        ..pre_state
    });
    let atomic_journal_lbl =
        AtomicJournalState::Label::CommitComplete {
            require_end:
                pre_state.journal.journal.seq_end(),
            discarded_aus: journal_discarded_aus,
        };
    AtomicJournalState::State::commit_complete_effect(
        pre_state.journal,
        post_state.journal,
        atomic_journal_lbl,
    );

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    UnifiedCacheJournalRefinement::commit_complete_refines(
        journal_pre,
        journal_post,
        pre_state.journal.journal.seq_end(),
        journal_discarded_aus,
    );
    UnifiedCacheBranchBetreeRefinement::
        store_commit_complete_refines(
            branch_pre,
            branch_post,
            image,
        );
    assert(unified_cache_betree_persistent_branch_cache_clean_inv(
        post,
    )) by {
        assert forall |slot: Slot|
            #[trigger] post_state.cache.entries
                .contains_key(slot)
            && post_state.cache.entries[slot] is Filled
            && unified_cache_betree_branch_clean_aus(
                post_state,
            ).contains(
                post_state.cache.entries[slot].get_addr().au,
            )
            implies post_state.cache.status_map[slot]
                is Clean
        by {
            let au =
                post_state.cache.entries[slot].get_addr().au;
            assert(unified_cache_betree_branch_clean_aus(
                pre_state,
            ).contains(au));
            assert(pre_state.cache.status_map[slot] is Clean);
        }
    }
    assert(unified_cache_betree_component_inv(post));

    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        CrashAwareCachingDiskBetreeSystem::Label::Noop;
    assert(pre.disk.responses.contains_key(req_id));
    assert(pre.disk.responses[req_id] == write_resp);
    assert(!pre.disk.requests.contains_key(req_id)) by {
        assert(pre.disk.requests.dom().disjoint(
            pre.disk.responses.dom(),
        ));
    }
    reveal(unified_cache_betree_superblock_write_pending);
    reveal(unified_cache_betree_superblock_landed);
    assert(src.superblockstore.in_flight is None);
    assert(src.superblockstore.landed);
    assert(dst.superblockstore.in_flight is None);
    assert(!dst.superblockstore.landed);
    assert(dst.superblockstore.persistent
        == src.superblockstore.persistent);
    assert(SuperblockStore::State::next_by(
        src.superblockstore,
        dst.superblockstore,
        SuperblockStore::Label::Complete,
        SuperblockStore::Step::complete(),
    )) by {
        reveal(SuperblockStore::State::next_by);
        reveal(SuperblockStore::State::complete);
    }
    reveal(SuperblockStore::State::next);
    assert(CrashAwareCachingDiskBetreeSystem::State::
        store_commit_complete(
            src,
            dst,
            target_lbl,
            dst.journal,
            dst.branch,
            dst.superblockstore,
            journal_discarded_aus,
            branch_discarded_aus,
        )
    ) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            store_commit_complete);
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::
            store_commit_complete(
                dst.journal,
                dst.branch,
                dst.superblockstore,
                journal_discarded_aus,
                branch_discarded_aus,
            ),
    )) by {
        reveal(CrashAwareCachingDiskBetreeSystem::State::
            next_by);
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post)) by {
        assert(!pre_state.outstanding_cache_reqs
            .contains_key(req_id));
    }
    assert(unified_cache_betree_cache_response_inv(post)) by {
        assert(!pre_state.outstanding_cache_reqs
            .contains_key(req_id));
    }
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    ));
    assert(unified_cache_betree_sync_state_inv(post));
    sync_discard_preserves_allocation_inv(
        pre,
        post,
        journal_discarded_aus,
        branch_discarded_aus,
    );
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn program_disk_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_disk(
                new_program,
                new_disk,
            ),
        ),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::program_disk(
        pre,
        post,
        lbl,
        new_program,
        new_disk,
    ));
    reveal(SystemModel::State::program_disk);
    assert(lbl is ProgramDiskOp);
    assert(UnifiedCacheBetreeProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::DiskIO{info: lbl->info},
    ));
    assert(post.program == new_program);
    assert(UnifiedCacheBetreeProgramModel::
        valid_disk_transition(
            pre.program,
            post.program,
            lbl->info,
        ));
    let unified_step =
        choose |step: UnifiedCacheBetreeSystem::Step|
            #![auto] {
                &&& UnifiedCacheBetreeSystem::State::next_by(
                    pre.program.state,
                    post.program.state,
                    UnifiedCacheBetreeSystem::Label::Disk,
                    step,
                )
                &&& UnifiedCacheBetreeProgramModel::
                    disk_step_matches_info(
                        pre.program.state,
                        step,
                        lbl->info,
                    )
            };
    assert(UnifiedCacheBetreeSystem::State::next_by(
        pre.program.state,
        post.program.state,
        UnifiedCacheBetreeSystem::Label::Disk,
        unified_step,
    ));
    assert(UnifiedCacheBetreeProgramModel::
        disk_step_matches_info(
            pre.program.state,
            unified_step,
            lbl->info,
        ));
    reveal(UnifiedCacheBetreeSystem::State::next_by);
    match unified_step {
        UnifiedCacheBetreeSystem::Step::initiate_recovery(
            req_id,
            reqs,
            resps,
        ) => {
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
        UnifiedCacheBetreeSystem::Step::superblock_recovery(
            req_id,
            raw_page,
            image,
            new_journal,
            new_branch,
            reqs,
            resps,
        ) => {
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
        UnifiedCacheBetreeSystem::Step::
            execute_journal_sync_begin(
                image,
                journal_reads,
                new_cache,
                new_journal,
                reqs,
                resps,
            ) => {
            program_disk_execute_journal_sync_begin_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                image,
                journal_reads,
                new_cache,
                new_journal,
                reqs,
                resps,
            );
        },
        UnifiedCacheBetreeSystem::Step::
            execute_sync_superblock_write(
                req_id,
                req,
                reqs,
                resps,
            ) => {
            if pre.program.state.branch.control.frozen is Some {
                program_disk_execute_store_superblock_write_refines(
                    pre,
                    post,
                    lbl,
                    new_program,
                    new_disk,
                    req_id,
                    req,
                    reqs,
                    resps,
                );
            } else {
                program_disk_execute_journal_superblock_write_refines(
                    pre,
                    post,
                    lbl,
                    new_program,
                    new_disk,
                    req_id,
                    req,
                    reqs,
                    resps,
                );
            }
        },
        UnifiedCacheBetreeSystem::Step::
            execute_journal_sync_end(
                journal_discarded_aus,
                new_journal,
                reqs,
                resps,
            ) => {
            program_disk_execute_journal_sync_end_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                journal_discarded_aus,
                new_journal,
                reqs,
                resps,
            );
        },
        UnifiedCacheBetreeSystem::Step::
            execute_store_sync_begin(
                image,
                journal_reads,
                new_cache,
                new_journal,
                reqs,
                resps,
            ) => {
            program_disk_execute_store_sync_begin_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                image,
                journal_reads,
                new_cache,
                new_journal,
                reqs,
                resps,
            );
        },
        UnifiedCacheBetreeSystem::Step::
            execute_store_sync_end(
                journal_discarded_aus,
                new_journal,
                reqs,
                resps,
            ) => {
            program_disk_execute_store_sync_end_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
                journal_discarded_aus,
                new_journal,
                reqs,
                resps,
            );
        },
        UnifiedCacheBetreeSystem::Step::cache_io_begin(
            req_map,
            new_cache,
            reqs,
            resps,
        ) => {
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
        UnifiedCacheBetreeSystem::Step::cache_io_end(
            resp_map,
            new_cache,
            reqs,
            resps,
        ) => {
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

pub proof fn disk_internal_process_write_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_disk: DiskModel,
    id: ID,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::disk_internal(new_disk),
        ),
        refinement_inv(pre),
        AsyncDisk::State::next_by(
            pre.disk,
            new_disk,
            DiskLabel::Internal{},
            AsyncDisk::Step::process_write(id),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    reveal(SystemModel::State::disk_internal);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);

    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let req = pre.disk.requests[id];
    let addr = req->to;
    let write_resp = DiskResponse::WriteResp{};
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);

    assert(lbl is DiskInternal);
    assert(post.program == pre.program);
    assert(post_state == pre_state);
    assert(post.disk == new_disk);
    assert(pre.disk.requests.contains_key(id));
    assert(req is WriteReq);
    assert(addr.wf());
    assert(post.disk.requests
        == pre.disk.requests.remove(id));
    assert(post.disk.responses
        == pre.disk.responses.insert(id, write_resp));
    assert(post.disk.content
        == pre.disk.content.insert(addr, req->data));
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        DiskLabel::Internal{},
    );
    assert(post.disk.inv());
    assert(journal_pre.same_except_cache_and_disk(
        journal_post,
    ));
    assert(branch_post.branch == branch_pre.branch);
    assert(branch_post.control == branch_pre.control);
    assert(branch_post.cache == branch_pre.cache);
    assert(branch_post.persistent_image
        == branch_pre.persistent_image);
    assert(branch_post.sync_phase
        == branch_pre.sync_phase);

    if pre_state.outstanding_cache_reqs
        .contains_key(id)
    {
        let cache_addr =
            pre_state.outstanding_cache_reqs[id];
        assert(req.addr() == cache_addr);
        assert(cache_addr == addr);
        assert(addr != spec_superblock_addr()) by {
            if addr == spec_superblock_addr() {
                assert(pre_state.outstanding_cache_reqs
                    .contains_value(
                        spec_superblock_addr(),
                    ));
                assert(false);
            }
        }
        let slot = pre_state.cache.lookup_map[addr];
        assert(pre_state.cache.lookup_map
            .contains_key(addr));
        assert(pre_state.cache.entries[slot] is Filled);
        assert(pre_state.cache.entries[slot]->data
            == req->data);
        assert(pre_state.cache.status_map[slot]
            is Writeback);
        pre_state.cache.build_lookup_map_ensures();
        assert(cache_filled_addr(
            pre_state.cache,
            addr,
        ));
        assert(cache_filled_page(
            pre_state.cache,
            addr,
        ) == req->data);
        assert(filled_cache_status(pre_state.cache)
            .contains_key(addr));
        assert(filled_cache_status(pre_state.cache)[addr]
            == PageStatus::Writeback);

        assert(pre_state.journal.ready()) by {
            if !pre_state.journal.ready() {
                assert(unified_cache_betree_unready_cache_clean_inv(
                    pre,
                ));
                assert(pre_state.cache.status_map[slot]
                    is Clean);
                assert(false);
            }
        }
        assert(pre_state.branch.control.metadata_loaded)
        by {
            if !pre_state.branch.control.metadata_loaded {
                assert(unified_cache_betree_unready_cache_clean_inv(
                    pre,
                ));
                assert(pre_state.cache.status_map[slot]
                    is Clean);
                assert(false);
            }
        }
        assert(pre_state.persistent_image is Some) by {
            assert(unified_cache_betree_recovery_state_inv(
                pre,
            ));
            match pre_state.recovery_state {
                RecoveryState::Begin
                | RecoveryState::AwaitingSuperblock => {
                    assert(pre_state.branch
                        == AtomicBranchBetreeState::State::
                            empty());
                    assert(!pre_state.branch.control
                        .metadata_loaded);
                    assert(false);
                },
                _ => {}
            }
        }
        assert(journal_pre.superblock_loaded());
        assert(journal_post.superblock_loaded());
        assert(journal_post.persistent_superblock_image_i()
            == journal_pre.persistent_superblock_image_i());
        assert(branch_post.persistent_superblock_image_i()
            == branch_pre.persistent_superblock_image_i());
        assert(post.disk.content.contains_key(
            spec_superblock_addr(),
        ));
        assert(post.disk.content[spec_superblock_addr()]
            == pre.disk.content[spec_superblock_addr()]);
        assert(UnifiedCacheJournalRefinement::
            async_disk_superblock_page_wf(
                post.disk.content,
            ));
        assert(abstract_superblock_raw_wf(
            post.disk.content[spec_superblock_addr()],
        ));

        let branch_clean_aus =
            unified_cache_betree_branch_clean_aus(
                pre_state,
            );
        assert(!branch_clean_aus.contains(addr.au)) by {
            if branch_clean_aus.contains(addr.au) {
                assert(unified_cache_betree_persistent_branch_cache_clean_inv(
                    pre,
                ));
                assert(pre_state.cache.status_map[slot]
                    is Clean);
                assert(false);
            }
        }
        assert(!pre_state.branch.control
            .persistent_aus.contains(addr.au));
        if pre_state.sync_phase.branch_ready()
            && pre_state.branch.control.frozen is Some
        {
            assert(!pre_state.branch.control.frozen
                .unwrap().aus.contains(addr.au));
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
            assert(journal_post.journal_projection_aus()
                =~= journal_pre.journal_projection_aus());
        }
        assert(CachingDisk::State::next(
            branch_pre.branch_caching_disk_i(),
            branch_post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        )) by {
            assert(branch_post.branch_projection_aus()
                =~= branch_pre.branch_projection_aus());
        }

        assert(branch_post.persistent_branch_image_i()
            == branch_pre.persistent_branch_image_i()) by {
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    persistent_branch_image_i);
            assert_maps_equal!(
                branch_post.persistent_branch_image_i()
                    .persistent,
                branch_pre.persistent_branch_image_i()
                    .persistent,
                a => {
                    if branch_post.persistent_branch_image_i()
                        .persistent.contains_key(a)
                    {
                        assert(pre_state.branch.control
                            .persistent_aus.contains(a.au));
                        assert(a != addr);
                        assert(post.disk.content[a]
                            == pre.disk.content[a]);
                    }
                    if branch_pre.persistent_branch_image_i()
                        .persistent.contains_key(a)
                    {
                        assert(pre_state.branch.control
                            .persistent_aus.contains(a.au));
                        assert(a != addr);
                        assert(post.disk.content[a]
                            == pre.disk.content[a]);
                    }
                }
            );
        }
        assert(branch_post.prepared_branch_image_i()
            == branch_pre.prepared_branch_image_i()) by {
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    prepared_branch_image_i);
            if pre_state.sync_phase is SuperblockWriteIssued
                && pre_state.branch.control.frozen is Some
            {
                let frozen_aus =
                    pre_state.branch.control.frozen
                        .unwrap().aus;
                assert_maps_equal!(
                    branch_post.prepared_branch_image_i()
                        .unwrap().persistent,
                    branch_pre.prepared_branch_image_i()
                        .unwrap().persistent,
                    a => {
                        if branch_post.prepared_branch_image_i()
                            .unwrap().persistent
                            .contains_key(a)
                        {
                            assert(frozen_aus.contains(a.au));
                            assert(a != addr);
                            assert(post.disk.content[a]
                                == pre.disk.content[a]);
                        }
                        if branch_pre.prepared_branch_image_i()
                            .unwrap().persistent
                            .contains_key(a)
                        {
                            assert(frozen_aus.contains(a.au));
                            assert(a != addr);
                            assert(post.disk.content[a]
                                == pre.disk.content[a]);
                        }
                    }
                );
            }
        }

        journal_pre.
            loaded_caching_disk_internal_refines_journal_internal_preserves_inv(
                journal_post,
            );
        branch_pre.projected_loaded_disk_internal_refines(
            branch_post,
        );
        assert(unified_cache_betree_component_inv(post));

        let src = unified_cache_betree_system_i(pre);
        let dst = unified_cache_betree_system_i(post);
        let target_lbl =
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            );
        let branch_lbl =
            CrashAwareCachingDiskBranchBetree::Label::
                Ephemeral {
                    op:
                        CachingDiskBranchBetree::Label::
                            Internal,
                    deallocs: Set::empty(),
                };
        assert(target_lbl
            == CrashAwareCachingDiskBetreeSystem::Label::Noop)
        by {
            let phase_id = pre_state.sync_phase.req_id();
            if phase_id is Some {
                let sync_id = phase_id.unwrap();
                assert(sync_id != id) by {
                    if sync_id == id {
                        assert(!pre_state
                            .outstanding_cache_reqs
                            .contains_key(sync_id));
                        assert(false);
                    }
                }
                if pre.disk.requests
                    .contains_key(sync_id)
                {
                    assert(post.disk.requests
                        .contains_key(sync_id));
                }
                if pre.disk.responses
                    .contains_key(sync_id)
                {
                    assert(post.disk.responses
                        .contains_key(sync_id));
                }
                if post.disk.responses
                    .contains_key(sync_id)
                {
                    assert(pre.disk.responses
                        .contains_key(sync_id));
                }
            }
        }
        assert(dst.progress == src.progress);
        assert(dst.sync_reqs == src.sync_reqs);
        assert(dst.free_aus == src.free_aus);
        assert(dst.superblockstore
            == src.superblockstore) by {
            let phase_id = pre_state.sync_phase.req_id();
            if phase_id is Some {
                let sync_id = phase_id.unwrap();
                assert(sync_id != id);
                if pre.disk.requests
                    .contains_key(sync_id)
                {
                    assert(post.disk.requests
                        .contains_key(sync_id));
                    assert(post.disk.requests[sync_id]
                        == pre.disk.requests[sync_id]);
                }
                if pre.disk.responses
                    .contains_key(sync_id)
                {
                    assert(post.disk.responses
                        .contains_key(sync_id));
                }
                if post.disk.responses
                    .contains_key(sync_id)
                {
                    assert(pre.disk.responses
                        .contains_key(sync_id));
                }
            }
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            component_internals(
                src,
                dst,
                target_lbl,
                dst.journal,
                dst.branch,
                branch_lbl,
            )) by {
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    component_internals,
            );
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            next_by(
                src,
                dst,
                target_lbl,
                CrashAwareCachingDiskBetreeSystem::Step::
                    component_internals(
                        dst.journal,
                        dst.branch,
                        branch_lbl,
                    ),
            )) by {
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    next_by,
            );
        }
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::next,
        );
        CrashAwareCachingDiskBetreeSystemRefinement::
            next_refines_ctam(src, dst, target_lbl);
    } else {
        assert(unified_cache_betree_disk_request_inv(pre));
        assert(pre_state.sync_phase.req_id() is Some);
        assert(pre_state.sync_phase.req_id().unwrap() == id);
        assert(addr == spec_superblock_addr());
        assert(unified_cache_betree_superblock_write_pending(
            pre,
        ));
        assert(pre_state.client_ready()) by {
            match pre_state.sync_phase {
                AtomicBetreeSyncPhase::
                    SuperblockWriteIssued{..} => {}
                _ => {
                    assert(false);
                }
            }
        }
        assert(pre_state.persistent_image is Some);
        assert(pre_state.journal.ready());
        assert(pre_state.branch.control.metadata_loaded);
        assert(post.disk.content.contains_key(
            spec_superblock_addr(),
        ));
        assert(post.disk.content[spec_superblock_addr()]
            == req->data);
        assert(abstract_superblock_raw_wf(req->data)) by {
            assert(unified_cache_betree_sync_state_inv(pre));
            assert(superblock_matches(
                req->data,
                pre_state.sync_phase.image().unwrap(),
            ));
        }
        assert(journal_post.persistent_superblock_image_i()
            == journal_pre.persistent_superblock_image_i());
        assert(branch_post.persistent_superblock_image_i()
            == branch_pre.persistent_superblock_image_i());

        let journal_aus =
            journal_pre.journal_projection_aus();
        let branch_aus =
            branch_pre.branch_projection_aus();
        assert(!journal_aus.contains(addr.au)) by {
            assert(unified_cache_betree_allocation_inv(pre));
            assert(UnifiedCacheBetreeSystem::State::
                reserved_aus().contains(addr.au));
        }
        assert(!branch_aus.contains(addr.au)) by {
            assert(unified_cache_betree_allocation_inv(pre));
            assert(UnifiedCacheBetreeSystem::State::
                reserved_aus().contains(addr.au));
        }
        async_disk_process_write_refines_projected_internal(
            pre_state.cache,
            pre.disk,
            post.disk,
            journal_aus,
            id,
        );
        async_disk_process_write_refines_projected_internal(
            pre_state.cache,
            pre.disk,
            post.disk,
            branch_aus,
            id,
        );
        assert(CachingDisk::State::next(
            journal_pre.journal_caching_disk_i(),
            journal_post.journal_caching_disk_i(),
            CachingDisk::Label::Internal{},
        ));
        assert(CachingDisk::State::next(
            branch_pre.branch_caching_disk_i(),
            branch_post.branch_caching_disk_i(),
            CachingDisk::Label::Internal{},
        ));
        assert(journal_post.journal_caching_disk_i()
            == journal_pre.journal_caching_disk_i()) by {
            assert_maps_equal!(
                journal_post.journal_caching_disk_i()
                    .persistent,
                journal_pre.journal_caching_disk_i()
                    .persistent,
                a => {
                    if journal_post.journal_caching_disk_i()
                        .persistent.contains_key(a)
                    {
                        assert(journal_aus.contains(a.au));
                        assert(a != addr);
                        assert(post.disk.content[a]
                            == pre.disk.content[a]);
                    }
                    if journal_pre.journal_caching_disk_i()
                        .persistent.contains_key(a)
                    {
                        assert(journal_aus.contains(a.au));
                        assert(a != addr);
                        assert(post.disk.content[a]
                            == pre.disk.content[a]);
                    }
                }
            );
        }
        assert(branch_post.branch_caching_disk_i()
            == branch_pre.branch_caching_disk_i()) by {
            assert_maps_equal!(
                branch_post.branch_caching_disk_i()
                    .persistent,
                branch_pre.branch_caching_disk_i()
                    .persistent,
                a => {
                    if branch_post.branch_caching_disk_i()
                        .persistent.contains_key(a)
                    {
                        assert(branch_aus.contains(a.au));
                        assert(a != addr);
                        assert(post.disk.content[a]
                            == pre.disk.content[a]);
                    }
                    if branch_pre.branch_caching_disk_i()
                        .persistent.contains_key(a)
                    {
                        assert(branch_aus.contains(a.au));
                        assert(a != addr);
                        assert(post.disk.content[a]
                            == pre.disk.content[a]);
                    }
                }
            );
        }
        assert(branch_post.persistent_branch_image_i()
            == branch_pre.persistent_branch_image_i()) by {
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    persistent_branch_image_i);
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    branch_caching_disk_i);
        }
        assert(branch_post.prepared_branch_image_i()
            == branch_pre.prepared_branch_image_i()) by {
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    prepared_branch_image_i);
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    known_branch_i);
        }
        journal_pre.
            loaded_caching_disk_internal_refines_journal_internal_preserves_inv(
                journal_post,
            );
        branch_pre.projected_loaded_disk_internal_refines(
            branch_post,
        );
        assert(journal_post.i() == journal_pre.i()) by {
            journal_pre.
                journal_interpretation_unchanged_by_same_projection(
                    journal_post,
                );
        }
        assert(branch_post.i() == branch_pre.i()) by {
            assert(branch_post.branch_caching_disk_i()
                == branch_pre.branch_caching_disk_i());
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::i);
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    ephemeral_branch_i);
        }
        assert(unified_cache_betree_component_inv(post));

        let src = unified_cache_betree_system_i(pre);
        let dst = unified_cache_betree_system_i(post);
        let target_lbl =
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            );
        assert(target_lbl
            == CrashAwareCachingDiskBetreeSystem::Label::Sync);
        assert(src.journal == dst.journal);
        assert(src.branch == dst.branch);
        assert(src.progress == dst.progress);
        assert(src.sync_reqs == dst.sync_reqs);
        assert(src.free_aus == dst.free_aus);
        assert(src.superblockstore.in_flight
            == Option::Some(req->data));
        assert(!src.superblockstore.landed);
        assert(dst.superblockstore.persistent
            == req->data);
        assert(dst.superblockstore.in_flight is None);
        assert(dst.superblockstore.landed);
        assert(SuperblockStore::State::land(
            src.superblockstore,
            dst.superblockstore,
            SuperblockStore::Label::Land,
        )) by {
            reveal(SuperblockStore::State::land);
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
        assert(CrashAwareCachingDiskBetreeSystem::State::
            superblock_write_lands(
                src,
                dst,
                target_lbl,
                dst.superblockstore,
            )) by {
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    superblock_write_lands,
            );
        }
        assert(CrashAwareCachingDiskBetreeSystem::State::
            next_by(
                src,
                dst,
                target_lbl,
                CrashAwareCachingDiskBetreeSystem::Step::
                    superblock_write_lands(
                        dst.superblockstore,
                    ),
            )) by {
            reveal(
                CrashAwareCachingDiskBetreeSystem::State::
                    next_by,
            );
        }
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::next,
        );
        CrashAwareCachingDiskBetreeSystemRefinement::
            next_refines_ctam(src, dst, target_lbl);
    }

    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post)) by {
        if post_state.recovery_state is Begin
            || post_state.recovery_state
                is AwaitingSuperblock
        {
            assert(pre_state.outstanding_cache_reqs
                == Map::<ID, Address>::empty());
            assert(!pre_state.outstanding_cache_reqs
                .contains_key(id));
            assert(pre.disk.requests[id] is ReadReq);
            assert(pre.disk.requests[id] is WriteReq);
            assert(false);
        }
    }
    assert(unified_cache_betree_shared_cache_disk_inv(post))
    by {
        assert forall |content_addr: Address| {
            &&& #[trigger] post.disk.content
                .contains_key(content_addr)
            &&& content_addr != spec_superblock_addr()
        } implies content_addr.wf() by {
            if content_addr == addr {
                assert(addr.wf());
            } else {
                assert(pre.disk.content
                    .contains_key(content_addr));
            }
        }
        assert forall |clean_addr: Address| {
            &&& #[trigger] filled_cache_status(
                post_state.cache,
            ).contains_key(clean_addr)
            &&& filled_cache_status(post_state.cache)[clean_addr]
                == PageStatus::Clean
            &&& clean_addr != spec_superblock_addr()
            &&& post.disk.content.contains_key(clean_addr)
        } implies {
            post.disk.content[clean_addr]
                == cache_filled_page(
                    post_state.cache,
                    clean_addr,
                )
        } by {
            if clean_addr == addr {
                assert(pre_state.outstanding_cache_reqs
                    .contains_key(id)) by {
                    if !pre_state.outstanding_cache_reqs
                        .contains_key(id)
                    {
                        assert(addr
                            == spec_superblock_addr());
                        assert(false);
                    }
                }
                let clean_slot =
                    pre_state.cache.lookup_map[addr];
                assert(pre_state.cache.status_map[clean_slot]
                    is Writeback);
                assert(filled_cache_status(
                    pre_state.cache,
                )[addr] == PageStatus::Writeback);
                assert(false);
            } else {
                assert(pre.disk.content
                    .contains_key(clean_addr));
                assert(post.disk.content[clean_addr]
                    == pre.disk.content[clean_addr]);
            }
        }
    }
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post))
    by {
        assert forall |pending_id: ID|
            #[trigger] post_state.outstanding_cache_reqs
                .contains_key(pending_id)
            implies disk_has_pending_id(
                post.disk,
                pending_id,
            )
        by {
            if pending_id == id {
                assert(post.disk.responses
                    .contains_key(id));
            } else if pre.disk.requests
                .contains_key(pending_id)
            {
                assert(post.disk.requests
                    .contains_key(pending_id));
            } else {
                assert(pre.disk.responses
                    .contains_key(pending_id));
                assert(post.disk.responses
                    .contains_key(pending_id));
            }
        }
        assert forall |pending_id: ID| {
            &&& #[trigger] post_state.outstanding_cache_reqs
                .contains_key(pending_id)
            &&& post.disk.requests
                .contains_key(pending_id)
        } implies {
            let pending_addr =
                post_state.outstanding_cache_reqs[
                    pending_id
                ];
            let pending_req =
                post.disk.requests[pending_id];
            &&& pending_req.addr() == pending_addr
            &&& pending_req is WriteReq ==> {
                &&& post_state.cache.lookup_map
                    .contains_key(pending_addr)
                &&& post_state.cache.entries[
                    post_state.cache.lookup_map[
                        pending_addr
                    ]
                ] is Filled
                &&& post_state.cache.entries[
                    post_state.cache.lookup_map[
                        pending_addr
                    ]
                ]->data == pending_req->data
                &&& post_state.cache.status_map[
                    post_state.cache.lookup_map[
                        pending_addr
                    ]
                ] is Writeback
            }
        } by {
            assert(pending_id != id);
            assert(pre.disk.requests
                .contains_key(pending_id));
            assert(post.disk.requests[pending_id]
                == pre.disk.requests[pending_id]);
        }
    }
    assert(unified_cache_betree_cache_response_inv(post))
    by {
        assert forall |resp_id: ID| {
            &&& #[trigger] post.disk.responses
                .contains_key(resp_id)
            &&& post_state.outstanding_cache_reqs
                .contains_key(resp_id)
        } implies {
            let response_addr =
                post_state.outstanding_cache_reqs[
                    resp_id
                ];
            let response = post.disk.responses[resp_id];
            &&& response_addr.wf()
            &&& response is ReadResp ==> {
                response->data
                    == post.disk.content[response_addr]
            }
            &&& response is WriteResp ==> {
                &&& post.disk.content
                    .contains_key(response_addr)
                &&& cache_filled_addr(
                    post_state.cache,
                    response_addr,
                )
                &&& post.disk.content[response_addr]
                    == cache_filled_page(
                        post_state.cache,
                        response_addr,
                    )
            }
        } by {
            let response_addr =
                post_state.outstanding_cache_reqs[resp_id];
            if resp_id == id {
                assert(pre_state.outstanding_cache_reqs
                    .contains_key(id));
                assert(response_addr == addr);
                assert(cache_filled_addr(
                    post_state.cache,
                    addr,
                ));
                assert(cache_filled_page(
                    post_state.cache,
                    addr,
                ) == req->data);
            } else {
                assert(pre.disk.responses
                    .contains_key(resp_id));
                if response_addr == addr {
                    assert(pre_state.outstanding_cache_reqs
                        .is_injective());
                    assert(resp_id == id);
                    assert(false);
                }
                assert(post.disk.content[response_addr]
                    == pre.disk.content[response_addr]);
            }
        }
    }
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    ));
    assert(unified_cache_betree_sync_state_inv(post));
    assert(unified_cache_betree_disk_request_inv(post))
    by {
        assert forall |write_id: ID|
            #[trigger] post.disk.requests
                .contains_key(write_id)
            && !post_state.outstanding_cache_reqs
                .contains_key(write_id)
            implies {
                ||| {
                    &&& post_state.recovery_state
                        is AwaitingSuperblock
                    &&& post.disk.requests[write_id]
                        is ReadReq
                    &&& post.disk.requests[write_id]->from
                        == spec_superblock_addr()
                }
                ||| {
                    &&& post_state.sync_phase.req_id()
                        is Some
                    &&& post_state.sync_phase.req_id()
                        .unwrap() == write_id
                    &&& post.disk.requests[write_id]
                        is WriteReq
                    &&& post.disk.requests[write_id]->to
                        == spec_superblock_addr()
                    &&& post_state.sync_phase.image()
                        is Some
                    &&& superblock_matches(
                        post.disk.requests[write_id]->data,
                        post_state.sync_phase.image()
                            .unwrap(),
                    )
                }
            }
        by {
            assert(write_id != id);
            assert(pre.disk.requests
                .contains_key(write_id));
            assert(post.disk.requests[write_id]
                == pre.disk.requests[write_id]);
        }
    }
    assert(unified_cache_betree_unready_cache_clean_inv(
        post,
    ));
    assert(
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        )
    );
    assert(unified_cache_betree_wip_persistent_disjoint_inv(
        post,
    ));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn disk_internal_process_read_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_disk: DiskModel,
    id: ID,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::disk_internal(new_disk),
        ),
        refinement_inv(pre),
        AsyncDisk::State::next_by(
            pre.disk,
            new_disk,
            DiskLabel::Internal{},
            AsyncDisk::Step::process_read(id),
        ),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    reveal(SystemModel::State::disk_internal);
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);

    let state = pre.program.state;
    let req = pre.disk.requests[id];
    let addr = req->from;
    let read_resp = DiskResponse::ReadResp {
        data: pre.disk.content[addr],
    };
    assert(lbl is DiskInternal);
    assert(post.program == pre.program);
    assert(post.disk == new_disk);
    assert(pre.disk.requests.contains_key(id));
    assert(req is ReadReq);
    assert(post.disk.requests
        == pre.disk.requests.remove(id));
    assert(post.disk.responses
        == pre.disk.responses.insert(id, read_resp));
    assert(post.disk.content == pre.disk.content);
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        DiskLabel::Internal{},
    );
    assert(post.disk.inv());

    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    journal_pre.unchanged_by_same_cache_and_disk_content(
        journal_post,
    );
    branch_pre.unchanged_by_same_cache_and_disk_content(
        branch_post,
    );
    assert(unified_cache_betree_component_inv(post));

    let phase_req_id = state.sync_phase.req_id();
    if phase_req_id is Some {
        let superblock_id = phase_req_id.unwrap();
        assert(superblock_id != id) by {
            if superblock_id == id {
                assert(pre.disk.requests[superblock_id]
                    is WriteReq);
                assert(pre.disk.requests[id] is ReadReq);
                assert(false);
            }
        }
    }
    assert(unified_cache_betree_system_i(post)
        == unified_cache_betree_system_i(pre)) by {
        assert(journal_post.i() == journal_pre.i());
        assert(branch_post.i() == branch_pre.i());
        reveal(unified_cache_betree_superblock_write_pending);
        reveal(unified_cache_betree_superblock_landed);
        if phase_req_id is Some {
            let superblock_id = phase_req_id.unwrap();
            assert(superblock_id != id);
            if pre.disk.requests.contains_key(
                superblock_id,
            ) {
                assert(post.disk.requests.contains_key(
                    superblock_id,
                ));
                assert(post.disk.requests[superblock_id]
                    == pre.disk.requests[superblock_id]);
            } else {
                assert(pre.disk.responses.contains_key(
                    superblock_id,
                ));
                assert(post.disk.responses.contains_key(
                    superblock_id,
                ));
                assert(post.disk.responses[superblock_id]
                    == pre.disk.responses[superblock_id]);
            }
        }
    }
    interpreted_noop_refines(pre, post, lbl);

    assert(unified_cache_betree_ready_inv(post));
    assert(unified_cache_betree_recovery_state_inv(post)) by {
        if state.recovery_state is Begin
            || state.recovery_state is AwaitingSuperblock
        {
            assert(state.outstanding_cache_reqs
                == Map::<ID, Address>::empty());
            assert(req->from == spec_superblock_addr());
            assert(post.disk.responses[id] == read_resp);
            assert(disk_has_pending_id(post.disk, id));
            assert forall |left: ID, right: ID| {
                &&& #[trigger] disk_has_pending_id(
                    post.disk,
                    left,
                )
                &&& #[trigger] disk_has_pending_id(
                    post.disk,
                    right,
                )
            } implies left == right by {
                assert(disk_has_pending_id(
                    pre.disk,
                    id,
                ));
                if post.disk.requests.contains_key(left) {
                    assert(pre.disk.requests.contains_key(
                        left,
                    ));
                    assert(left != id);
                    assert(disk_has_pending_id(
                        pre.disk,
                        left,
                    ));
                    assert(left == id);
                    assert(false);
                } else if left != id {
                    assert(pre.disk.responses.contains_key(
                        left,
                    ));
                    assert(disk_has_pending_id(
                        pre.disk,
                        left,
                    ));
                    assert(left == id);
                }
                if post.disk.requests.contains_key(right) {
                    assert(pre.disk.requests.contains_key(
                        right,
                    ));
                    assert(right != id);
                    assert(disk_has_pending_id(
                        pre.disk,
                        right,
                    ));
                    assert(right == id);
                    assert(false);
                } else if right != id {
                    assert(pre.disk.responses.contains_key(
                        right,
                    ));
                    assert(disk_has_pending_id(
                        pre.disk,
                        right,
                    ));
                    assert(right == id);
                }
            }
        }
    }
    assert(unified_cache_betree_shared_cache_disk_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post)) by {
        assert forall |pending_id: ID|
            #[trigger] state.outstanding_cache_reqs
                .contains_key(pending_id)
            implies disk_has_pending_id(
                post.disk,
                pending_id,
            )
        by {
            if pending_id == id {
                assert(post.disk.responses.contains_key(id));
            } else if pre.disk.requests.contains_key(
                pending_id,
            ) {
                assert(post.disk.requests.contains_key(
                    pending_id,
                ));
            } else {
                assert(pre.disk.responses.contains_key(
                    pending_id,
                ));
                assert(post.disk.responses.contains_key(
                    pending_id,
                ));
            }
        }
        assert forall |pending_id: ID| {
            &&& #[trigger] state.outstanding_cache_reqs
                .contains_key(pending_id)
            &&& post.disk.requests
                .contains_key(pending_id)
        } implies {
            let pending_addr =
                state.outstanding_cache_reqs[pending_id];
            let pending_req =
                post.disk.requests[pending_id];
            &&& pending_req.addr() == pending_addr
            &&& pending_req is WriteReq ==> {
                &&& state.cache.lookup_map
                    .contains_key(pending_addr)
                &&& state.cache.entries[
                    state.cache.lookup_map[pending_addr]
                ] is Filled
                &&& state.cache.entries[
                    state.cache.lookup_map[pending_addr]
                ]->data == pending_req->data
                &&& state.cache.status_map[
                    state.cache.lookup_map[pending_addr]
                ] is Writeback
            }
        } by {
            assert(pending_id != id);
            assert(pre.disk.requests.contains_key(
                pending_id,
            ));
            assert(post.disk.requests[pending_id]
                == pre.disk.requests[pending_id]);
        }
    }
    assert(unified_cache_betree_cache_response_inv(post)) by {
        assert forall |resp_id: ID| {
            &&& #[trigger] post.disk.responses
                .contains_key(resp_id)
            &&& state.outstanding_cache_reqs
                .contains_key(resp_id)
        } implies {
            let response_addr =
                state.outstanding_cache_reqs[resp_id];
            let response = post.disk.responses[resp_id];
            &&& response_addr.wf()
            &&& response is ReadResp ==> {
                response->data
                    == post.disk.content[response_addr]
            }
            &&& response is WriteResp ==> {
                &&& post.disk.content
                    .contains_key(response_addr)
                &&& cache_filled_addr(
                    state.cache,
                    response_addr,
                )
                &&& post.disk.content[response_addr]
                    == cache_filled_page(
                        state.cache,
                        response_addr,
                    )
            }
        } by {
            let response_addr =
                state.outstanding_cache_reqs[resp_id];
            if resp_id == id {
                assert(pre.disk.requests[id].addr()
                    == response_addr);
                assert(addr == response_addr);
                assert(response_addr.wf());
            } else {
                assert(pre.disk.responses
                    .contains_key(resp_id));
                assert(post.disk.responses[resp_id]
                    == pre.disk.responses[resp_id]);
                assert(unified_cache_betree_cache_response_inv(
                    pre,
                ));
            }
        }
    }
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    )) by {
        if phase_req_id is Some {
            let superblock_id = phase_req_id.unwrap();
            assert(superblock_id != id);
            if pre.disk.requests.contains_key(
                superblock_id,
            ) {
                assert(post.disk.requests.contains_key(
                    superblock_id,
                ));
            } else {
                assert(pre.disk.responses.contains_key(
                    superblock_id,
                ));
                assert(post.disk.responses.contains_key(
                    superblock_id,
                ));
            }
        }
    }
    assert(unified_cache_betree_sync_state_inv(post));
    assert(unified_cache_betree_allocation_inv(post));
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

pub proof fn disk_internal_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_disk: DiskModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::disk_internal(new_disk),
        ),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::disk_internal(
        pre,
        post,
        lbl,
        new_disk,
    ));
    assert(lbl is DiskInternal);
    assert(post.program == pre.program);
    assert(post.disk == new_disk);
    assert(DiskModel::next(
        pre.disk,
        new_disk,
        DiskLabel::Internal{},
    ));

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |step: AsyncDisk::Step|
        AsyncDisk::State::next_by(
            pre.disk,
            new_disk,
            DiskLabel::Internal{},
            step,
        );
    match disk_step {
        AsyncDisk::Step::process_read(id) => {
            disk_internal_process_read_refines(
                pre,
                post,
                lbl,
                new_disk,
                id,
            );
        },
        AsyncDisk::Step::process_write(id) => {
            disk_internal_process_write_refines(
                pre,
                post,
                lbl,
                new_disk,
                id,
            );
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn crash_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
    new_disk: DiskModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::crash(
                new_program,
                new_disk,
            ),
        ),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(
                pre,
                post,
                lbl,
            ),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::crash(
        pre,
        post,
        lbl,
        new_program,
        new_disk,
    ));
    reveal(SystemModel::State::crash);
    assert(lbl is Crash);
    assert(post.program == new_program);
    assert(post.disk == new_disk);
    assert(post.requests == Multiset::<Request>::empty());
    assert(post.replies == Multiset::<Reply>::empty());
    assert(UnifiedCacheBetreeProgramModel::init(
        post.program,
    ));
    assert(UnifiedCacheBetreeSystem::State::init(
        post.program.state,
    ));
    assert(DiskModel::next(
        pre.disk,
        post.disk,
        DiskLabel::Crash{},
    ));

    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let disk_step = choose |step: AsyncDisk::Step|
        AsyncDisk::State::next_by(
            pre.disk,
            post.disk,
            DiskLabel::Crash{},
            step,
        );
    match disk_step {
        AsyncDisk::Step::crash() => {
            reveal(AsyncDisk::State::crash);
        },
        _ => {
            assert(false);
        },
    }
    assert(post.disk.content == pre.disk.content);
    assert(post.disk.requests
        == Map::<ID, DiskRequest>::empty());
    assert(post.disk.responses
        == Map::<ID, DiskResponse>::empty());
    crate::spec::AsyncDisk_t::inv_next(
        pre.disk,
        post.disk,
        DiskLabel::Crash{},
    );

    reveal(UnifiedCacheBetreeSystem::State::init);
    reveal(UnifiedCacheBetreeSystem::State::init_by);
    let config =
        choose |config: UnifiedCacheBetreeSystem::Config|
            UnifiedCacheBetreeSystem::State::init_by(
                post.program.state,
                config,
            );
    match config {
        UnifiedCacheBetreeSystem::Config::initialize(
            cache_slots,
            free_aus,
        ) => {
            assert(UnifiedCacheBetreeSystem::State::
                initialize(
                    post.program.state,
                    cache_slots,
                    free_aus,
                ));
            assert(Cache::State::initialize(
                post.program.state.cache,
                cache_slots,
            )) by {
                reveal(UnifiedCacheBetreeSystem::State::
                    initialize);
                reveal(Cache::State::initialize);
            }
            Cache::State::initialize_inductive(
                post.program.state.cache,
                cache_slots,
            );
        },
        UnifiedCacheBetreeSystem::Config::
            dummy_to_use_type_params(_) => {
            assert(false);
        },
    }

    let pre_state = pre.program.state;
    let post_state = post.program.state;
    let src = unified_cache_betree_system_i(pre);
    let dst = unified_cache_betree_system_i(post);
    let target_lbl =
        unified_cache_betree_system_i_lbl(
            pre,
            post,
            lbl,
        );
    let keep_in_flight = src.superblockstore.landed;
    let branch_keep_in_flight =
        keep_in_flight && src.branch.prepared is Some;
    let journal_pre =
        unified_cache_betree_journal_source(pre);
    let journal_post =
        unified_cache_betree_journal_source(post);
    let branch_pre =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(pre);
    let branch_post =
        UnifiedCacheBranchBetreeRefinement::
            unified_cache_branch_betree_source(post);
    let journal_crash_image =
        if keep_in_flight {
            CachingDiskJournalImage::
                materialized_from_loaded_index(
                    src.journal.ephemeral->v,
                    src.journal.frozen.unwrap(),
                )
        } else if src.journal.ephemeral is Unknown {
            src.journal.persistent->image
        } else {
            CachingDiskJournalImage::
                materialized_from_loaded_index(
                    src.journal.ephemeral->v,
                    src.journal.persistent.metadata(),
                )
        };
    let branch_crash_image =
        if branch_keep_in_flight {
            src.branch.prepared.unwrap()
        } else {
            src.branch.persistent
        };

    assert(target_lbl
        == CrashAwareCachingDiskBetreeSystem::Label::Crash);
    assert(CrashAwareCachingDiskBetreeSystemRefinement::
        refinement_inv(src));
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
            reveal(SuperblockStore::State::crash);
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

    assert(journal_post.persistent_image is None);
    assert(journal_post.journal
        == AtomicJournalState::State::empty());
    assert(journal_post.disk.content
        == journal_pre.disk.content);
    assert(dst.journal.persistent
        == PersistentCachingDiskJournal::Image {
            image: journal_crash_image,
        }) by {
        if keep_in_flight {
            let image =
                pre_state.sync_phase.image().unwrap();
            assert(unified_cache_betree_sync_state_inv(
                pre,
            ));
            assert(pre_state.sync_phase.req_id() is Some);
            let req_id =
                pre_state.sync_phase.req_id().unwrap();
            assert(pre.disk.responses.contains_key(req_id));
            assert(superblock_matches(
                pre.disk.content[spec_superblock_addr()],
                image,
            ));
            assert(journal_post
                .persistent_superblock_image_i() == image);
            assert(src.journal.frozen is Some);
            assert(journal_pre.journal.ready());
            journal_pre.
                post_crash_persistent_image_matches_materialized(
                    journal_post,
                    image,
                    src.journal.frozen.unwrap(),
                );
            assert(journal_post.journal_projection_aus()
                <= journal_pre.journal_projection_aus());
        } else if src.journal.ephemeral is Unknown {
            assert(!journal_pre.superblock_loaded());
            assert(journal_post
                .persistent_superblock_image_i()
                == journal_pre
                    .persistent_superblock_image_i());
            assert(journal_post.persistent_journal_image_i()
                == journal_pre.persistent_journal_image_i())
            by {
                assert_maps_equal!(
                    journal_post
                        .persistent_journal_image_i()
                        .persistent,
                    journal_pre
                        .persistent_journal_image_i()
                        .persistent,
                    a => {}
                );
            }
        } else {
            let image =
                journal_pre.persistent_superblock_image_i();
            assert(journal_pre.superblock_loaded());
            assert(unified_cache_betree_superblock_image_inv(
                pre,
            ));
            assert(journal_post
                .persistent_superblock_image_i() == image);
            if journal_pre.journal.ready() {
                journal_pre.
                    post_crash_persistent_image_matches_materialized(
                        journal_post,
                        image,
                        src.journal.persistent.metadata(),
                    );
                assert(journal_post.journal_projection_aus()
                    <= journal_pre.journal_projection_aus());
            } else {
                journal_pre.
                    unloaded_post_crash_persistent_image_matches_materialized(
                        journal_post,
                        image,
                        src.journal.persistent.metadata(),
                    );
                assert(journal_post.journal_projection_aus()
                    <= journal_pre.journal_projection_aus());
            }
        }
    }
    assert(CrashAwareCachingDiskJournal::State::next(
        src.journal,
        dst.journal,
        CrashAwareCachingDiskJournal::Label::Crash {
            keep_in_flight,
        },
    )) by {
        assert(CrashAwareCachingDiskJournal::State::crash(
            src.journal,
            dst.journal,
            CrashAwareCachingDiskJournal::Label::Crash {
                keep_in_flight,
            },
        )) by {
            reveal(
                CrashAwareCachingDiskJournal::State::crash,
            );
        }
        assert(CrashAwareCachingDiskJournal::State::next_by(
            src.journal,
            dst.journal,
            CrashAwareCachingDiskJournal::Label::Crash {
                keep_in_flight,
            },
            CrashAwareCachingDiskJournal::Step::crash(),
        )) by {
            reveal(
                CrashAwareCachingDiskJournal::State::next_by,
            );
        }
        reveal(CrashAwareCachingDiskJournal::State::next);
    }
    src.journal.next_refines(
        dst.journal,
        CrashAwareCachingDiskJournal::Label::Crash {
            keep_in_flight,
        },
    );
    assert(UnifiedCacheJournalRefinement::inv(
        journal_post,
    )) by {
        assert(journal_post.journal.wf());
        assert(UnifiedCacheJournalRefinement::
            async_disk_superblock_page_wf(
                journal_post.disk.content,
            ));
        assert(journal_post
            .persistent_superblock_image_i().wf());
        assert(journal_post.cache.inv());
        assert(journal_post.disk.inv());
        let persistent_only = CachingDisk::State {
            cache: Map::<Address, RawPage>::empty(),
            persistent: journal_post
                .persistent_journal_image_i().persistent,
            status: Map::<Address, PageStatus>::empty(),
        };
        CachingDisk::State::persistent_only_inv(
            journal_post
                .persistent_journal_image_i().persistent,
        );
        assert(journal_post.journal_caching_disk_i()
            == persistent_only) by {
            assert_maps_equal!(
                journal_post.journal_caching_disk_i()
                    .cache,
                persistent_only.cache,
                a => {}
            );
            assert_maps_equal!(
                journal_post.journal_caching_disk_i()
                    .persistent,
                persistent_only.persistent,
                a => {}
            );
            assert_maps_equal!(
                journal_post.journal_caching_disk_i()
                    .status,
                persistent_only.status,
                a => {}
            );
        }
        assert(journal_post.journal_caching_disk_i()
            .inv());
        reveal(UnifiedCacheJournalRefinement::
            UnifiedCacheJournalSource::inv);
        reveal(UnifiedCacheJournalRefinement::
            UnifiedCacheJournalSource::semantic_inv);
        assert(journal_post.i().refinement_inv());
    }

    assert(branch_post.persistent_image is None);
    assert(branch_post.branch
        == crate::implementation::
            AtomicBranchBetreeState_v::
                empty_cached_betree());
    assert(branch_post.control
        == crate::implementation::
            AtomicBranchBetreeState_v::
                AtomicBranchBetreeControl::empty());
    assert(branch_post.disk.content
        == branch_pre.disk.content);
    assert(branch_crash_image.valid()) by {
        if branch_keep_in_flight {
            assert(src.branch.prepared is Some);
        } else {
            assert(src.branch.persistent.valid());
        }
    }
    assert(branch_crash_image.metadata
        == branch_post.persistent_metadata_i()) by {
        if keep_in_flight {
            let image =
                pre_state.sync_phase.image().unwrap();
            let req_id =
                pre_state.sync_phase.req_id().unwrap();
            assert(pre.disk.responses.contains_key(req_id));
            assert(unified_cache_betree_sync_state_inv(
                pre,
            ));
            assert(superblock_matches(
                pre.disk.content[spec_superblock_addr()],
                image,
            ));
            assert(branch_post
                .persistent_superblock_image_i() == image);
            if branch_keep_in_flight {
                assert(src.branch.prepared is Some);
                assert(src.branch.frozen is Some);
                assert(branch_crash_image
                    == src.branch.prepared.unwrap());
                reveal(
                    CachingDiskBranchBetreeImage::
                        materialized_from_persistent,
                );
                assert(branch_crash_image.metadata
                    == src.branch.frozen.unwrap().metadata);
            } else {
                assert(src.branch.prepared is None);
                assert(src.branch.persistent
                    == branch_pre
                        .persistent_branch_image_i());
                assert(branch_pre.control.metadata_loaded);
                assert(branch_pre.control.metadata
                    == branch_pre.persistent_metadata_i());
                assert(branch_crash_image.metadata
                    == branch_pre.control.metadata);
            }
        } else {
            assert(unified_cache_betree_superblock_image_inv(
                pre,
            ));
            if branch_pre.superblock_loaded() {
                assert(superblock_matches(
                    pre.disk.content[
                        spec_superblock_addr()
                    ],
                    pre_state.persistent_image.unwrap(),
                ));
            }
            assert(branch_post
                .persistent_superblock_image_i()
                == branch_pre
                    .persistent_superblock_image_i());
            assert(src.branch.persistent
                == branch_pre.persistent_branch_image_i());
        }
    }
    assert(branch_crash_image.persistent
        == branch_post.disk.content.restrict(
            addresses_in_aus(
                branch_crash_image.load().betree
                    .durable_aus(),
            ),
        )) by {
        if branch_keep_in_flight {
            let frozen_aus =
                src.branch.frozen.unwrap().aus;
            assert(src.branch.prepared.unwrap()
                .load().betree.durable_aus()
                == frozen_aus);
            assert(branch_crash_image
                == branch_pre
                    .prepared_branch_image_i()
                    .unwrap());
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    prepared_branch_image_i);
            reveal(
                CachingDiskBranchBetreeImage::
                    materialized_from_persistent,
            );
            assert_maps_equal!(
                branch_crash_image.persistent,
                branch_post.disk.content.restrict(
                    addresses_in_aus(frozen_aus),
                ),
                a => {
                    if branch_crash_image.persistent
                        .contains_key(a)
                    {
                        assert(addresses_in_aus(frozen_aus)
                            .contains(a));
                        assert(branch_pre
                            .branch_projection_aus()
                            .contains(a.au));
                    }
                    if branch_post.disk.content.restrict(
                        addresses_in_aus(frozen_aus),
                    ).contains_key(a)
                    {
                        assert(addresses_in_aus(frozen_aus)
                            .contains(a));
                        assert(branch_pre
                            .branch_projection_aus()
                            .contains(a.au));
                    }
                }
            );
        } else if branch_pre.control.metadata_loaded {
            assert(src.branch.ephemeral is Known);
            assert(src.branch.ephemeral->persistent_aus
                == src.branch.persistent.load()
                    .betree.durable_aus());
            assert(src.branch.ephemeral->persistent_aus
                == branch_pre.control.persistent_aus);
            assert(src.branch.persistent
                == branch_pre.persistent_branch_image_i());
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    persistent_branch_image_i);
        } else {
            assert(src.branch.persistent
                == branch_pre.persistent_branch_image_i());
            UnifiedCacheBranchBetreeRefinement::
                persistent_image_witness_aus_match(
                    branch_pre,
                );
            reveal(CachingDiskBranchBetreeImage::load);
            reveal(CachingDiskBranchBetreeImage::
                cached_betree);
            reveal(CachedBranchBetree::State::durable_aus);
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    persistent_branch_image_i);
        }
    }
    assert(filled_cache_pages(post_state.cache).is_empty())
    by {
        reveal(Cache::State::empty);
        reveal(filled_cache_pages);
    }
    UnifiedCacheBranchBetreeRefinement::
        post_crash_reconstructs_persistent_image(
            branch_post,
            branch_crash_image,
        );
    assert(branch_post.persistent_branch_image_i()
        == branch_crash_image);
    assert(dst.branch.persistent == branch_crash_image);
    assert(dst.branch.ephemeral is Unknown);
    assert(dst.branch.frozen is None);
    assert(dst.branch.prepared is None);
    assert(CrashAwareCachingDiskBranchBetree::State::next(
        src.branch,
        dst.branch,
        CrashAwareCachingDiskBranchBetree::Label::Crash {
            keep_in_flight: branch_keep_in_flight,
        },
    )) by {
        assert(CrashAwareCachingDiskBranchBetree::State::crash(
            src.branch,
            dst.branch,
            CrashAwareCachingDiskBranchBetree::Label::Crash {
                keep_in_flight: branch_keep_in_flight,
            },
        )) by {
            reveal(
                CrashAwareCachingDiskBranchBetree::State::crash,
            );
        }
        assert(CrashAwareCachingDiskBranchBetree::State::
            next_by(
                src.branch,
                dst.branch,
                CrashAwareCachingDiskBranchBetree::Label::Crash {
                    keep_in_flight:
                        branch_keep_in_flight,
                },
                CrashAwareCachingDiskBranchBetree::Step::
                    crash(),
            )) by {
            reveal(
                CrashAwareCachingDiskBranchBetree::State::
                    next_by,
            );
        }
        reveal(
            CrashAwareCachingDiskBranchBetree::State::next,
        );
    }
    src.branch.next_refines(
        dst.branch,
        CrashAwareCachingDiskBranchBetree::Label::Crash {
            keep_in_flight: branch_keep_in_flight,
        },
    );
    reveal(UnifiedCacheBranchBetreeRefinement::
        UnifiedCacheBranchBetreeSource::inv);
    assert(branch_post.control_wf());
    assert(branch_post.i().refinement_inv());
    assert(branch_post.inv());

    assert(dst.progress
        == crate::spec::MapSpec_t::AsyncMap::State::
            init_ephemeral_state()) by {
        reveal(unified_cache_betree_progress_i);
        reveal(system_multiset_to_set_i);
    }
    assert(post_state.free_aus
        - UnifiedCacheBetreeSystem::State::reserved_aus()
        == post_state.free_aus) by {
        assert(post_state.free_aus.disjoint(
            UnifiedCacheBetreeSystem::State::reserved_aus(),
        ));
        assert forall |au:
            crate::disk::GenericDisk_v::AU|
            #[trigger] (post_state.free_aus
                - UnifiedCacheBetreeSystem::State::
                    reserved_aus()).contains(au)
            <==> post_state.free_aus.contains(au)
        by {
        }
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::crash(
        src,
        dst,
        target_lbl,
        dst.journal,
        dst.branch,
        dst.superblockstore,
        post_state.free_aus,
        keep_in_flight,
    )) by {
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::crash,
        );
        assert(post_state.free_aus.disjoint(
            UnifiedCacheBetreeSystem::State::reserved_aus(),
        ));
    }
    assert(CrashAwareCachingDiskBetreeSystem::State::next_by(
        src,
        dst,
        target_lbl,
        CrashAwareCachingDiskBetreeSystem::Step::crash(
            dst.journal,
            dst.branch,
            dst.superblockstore,
            post_state.free_aus,
            keep_in_flight,
        ),
    )) by {
        reveal(
            CrashAwareCachingDiskBetreeSystem::State::next_by,
        );
    }
    reveal(CrashAwareCachingDiskBetreeSystem::State::next);
    CrashAwareCachingDiskBetreeSystemRefinement::
        next_refines_ctam(src, dst, target_lbl);

    assert(unified_cache_betree_component_inv(post));
    assert(unified_cache_betree_ready_inv(post));
    assert(journal_post.journal_caching_disk_i().cache
        == Map::<Address, RawPage>::empty()) by {
        assert_maps_equal!(
            journal_post.journal_caching_disk_i().cache,
            Map::<Address, RawPage>::empty(),
            a => {
                if journal_post.journal_caching_disk_i()
                    .cache.contains_key(a)
                {
                    assert(filled_cache_pages(
                        post_state.cache,
                    ).contains_key(a));
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
            a => {}
        );
    }
    assert(unified_cache_betree_recovery_state_inv(post));
    assert(unified_cache_betree_shared_cache_disk_inv(post))
    by {
        assert(filled_cache_pages(post_state.cache)
            == Map::<Address, RawPage>::empty());
    }
    assert(unified_cache_betree_cache_response_inv(post));
    assert(unified_cache_betree_outstanding_io_inv(post));
    assert(unified_cache_betree_cache_request_inv(post));
    assert(unified_cache_betree_superblock_cache_id_inv(
        post,
    ));
    assert(unified_cache_betree_sync_state_inv(post));
    assert(unified_cache_betree_disk_request_inv(post));
    assert(unified_cache_betree_superblock_image_inv(post));
    assert(unified_cache_betree_unready_cache_clean_inv(
        post,
    ));
    assert(
        unified_cache_betree_persistent_branch_cache_clean_inv(
            post,
        )
    );
    assert(unified_cache_betree_wip_persistent_disjoint_inv(
        post,
    ));
    let pre_journal_aus =
        journal_pre.journal_projection_aus();
    let post_journal_aus =
        journal_post.journal_projection_aus();
    let pre_branch_aus =
        branch_pre.branch_projection_aus();
    let post_branch_aus =
        branch_post.branch_projection_aus();
    assert(post_branch_aus <= pre_branch_aus) by {
        assert(post_branch_aus
            == branch_crash_image.load().betree
                .durable_aus()) by {
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    branch_projection_aus);
        }
        if branch_keep_in_flight {
            assert(branch_crash_image.load().betree
                .durable_aus()
                == src.branch.frozen.unwrap().aus);
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    branch_projection_aus);
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    frozen_aus_i);
        } else if branch_pre.control.metadata_loaded {
            assert(branch_crash_image.load().betree
                .durable_aus()
                == branch_pre.control.persistent_aus);
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    branch_projection_aus);
        } else {
            UnifiedCacheBranchBetreeRefinement::
                persistent_image_witness_aus_match(
                    branch_pre,
                );
            reveal(CachingDiskBranchBetreeImage::load);
            reveal(CachingDiskBranchBetreeImage::
                cached_betree);
            reveal(CachedBranchBetree::State::durable_aus);
            reveal(UnifiedCacheBranchBetreeRefinement::
                UnifiedCacheBranchBetreeSource::
                    branch_projection_aus);
        }
    }
    assert(post_journal_aus <= pre_journal_aus) by {
        if keep_in_flight {
            journal_pre.
                post_crash_persistent_image_matches_materialized(
                    journal_post,
                    pre_state.sync_phase.image().unwrap(),
                    src.journal.frozen.unwrap(),
                );
            assert(post_journal_aus
                <= journal_pre.journal_projection_aus());
        } else if src.journal.ephemeral is Unknown {
            assert(journal_post
                .persistent_journal_image_i()
                == journal_pre
                    .persistent_journal_image_i());
            assert(post_journal_aus
                == pre_journal_aus);
        } else {
            let image =
                journal_pre.persistent_superblock_image_i();
            if journal_pre.journal.ready() {
                journal_pre.
                    post_crash_persistent_image_matches_materialized(
                        journal_post,
                        image,
                        src.journal.persistent.metadata(),
                    );
            } else {
                journal_pre.
                    unloaded_post_crash_persistent_image_matches_materialized(
                        journal_post,
                        image,
                        src.journal.persistent.metadata(),
                    );
            }
            assert(post_journal_aus
                <= journal_pre.journal_projection_aus());
        }
    }
    assert(unified_cache_betree_allocation_inv(post))
    by {
        assert(unified_cache_betree_allocation_inv(pre));
        assert(UnifiedCacheBetreeSystem::State::reserved_aus()
            .disjoint(post_journal_aus));
        assert(UnifiedCacheBetreeSystem::State::reserved_aus()
            .disjoint(post_branch_aus));
        assert(post_journal_aus.disjoint(post_branch_aus));
    }
    assert(system_model_progress_history_inv(post));
    assert(system_model_progress_unique_inv(post));
    assert(system_model_request_id_unique_inv(post));
    assert(system_model_request_reply_disjoint_inv(post));
    assert(refinement_inv(post));
}

proof fn program_accept_sync_request_step_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_accept_sync_request(
                new_program,
            ),
        ),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::program_accept_sync_request(
        pre,
        post,
        lbl,
        new_program,
    ));
    reveal(SystemModel::State::program_accept_sync_request);
    assert(lbl is ProgramUIOp);
    assert(lbl->op is AcceptSyncRequest);
    let sync_req_id = match lbl->op {
        ProgramUserOp::AcceptSyncRequest{sync_req_id} =>
            sync_req_id,
        _ => {
            assert(false);
            arbitrary()
        },
    };
    let source_lbl =
        UnifiedCacheBetreeSystem::Label::AcceptSyncRequest {
            sync_req_id,
        };
    assert(UnifiedCacheBetreeProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::UserIO{op: lbl->op},
    ));
    assert(UnifiedCacheBetreeSystem::State::next(
        pre.program.state,
        post.program.state,
        source_lbl,
    ));
    reveal(UnifiedCacheBetreeSystem::State::next);
    reveal(UnifiedCacheBetreeSystem::State::next_by);
    let unified_step =
        choose |step: UnifiedCacheBetreeSystem::Step|
            UnifiedCacheBetreeSystem::State::next_by(
                pre.program.state,
                post.program.state,
                source_lbl,
                step,
            );
    match unified_step {
        UnifiedCacheBetreeSystem::Step::
            accept_sync_request() => {
            assert(UnifiedCacheBetreeSystem::State::
                accept_sync_request(
                    pre.program.state,
                    post.program.state,
                    source_lbl,
                ));
            program_accept_sync_request_refines(
                pre,
                post,
                lbl,
                new_program,
                sync_req_id,
            );
        },
        _ => {
            assert(false);
        },
    }
}

proof fn program_deliver_sync_reply_step_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
    new_program: UnifiedCacheBetreeProgramModel,
)
    requires
        SystemModel::State::next_by(
            pre,
            post,
            lbl,
            SystemModel::Step::program_deliver_sync_reply(
                new_program,
            ),
        ),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    reveal(SystemModel::State::next_by);
    assert(SystemModel::State::program_deliver_sync_reply(
        pre,
        post,
        lbl,
        new_program,
    ));
    reveal(SystemModel::State::program_deliver_sync_reply);
    assert(lbl is ProgramUIOp);
    assert(lbl->op is DeliverSyncReply);
    let sync_req_id = match lbl->op {
        ProgramUserOp::DeliverSyncReply{sync_req_id} =>
            sync_req_id,
        _ => {
            assert(false);
            arbitrary()
        },
    };
    let source_lbl =
        UnifiedCacheBetreeSystem::Label::DeliverSyncReply {
            sync_req_id,
        };
    assert(UnifiedCacheBetreeProgramModel::next(
        pre.program,
        new_program,
        ProgramLabel::UserIO{op: lbl->op},
    ));
    assert(UnifiedCacheBetreeSystem::State::next(
        pre.program.state,
        post.program.state,
        source_lbl,
    ));
    reveal(UnifiedCacheBetreeSystem::State::next);
    reveal(UnifiedCacheBetreeSystem::State::next_by);
    let unified_step =
        choose |step: UnifiedCacheBetreeSystem::Step|
            UnifiedCacheBetreeSystem::State::next_by(
                pre.program.state,
                post.program.state,
                source_lbl,
                step,
            );
    match unified_step {
        UnifiedCacheBetreeSystem::Step::
            deliver_sync_reply() => {
            assert(UnifiedCacheBetreeSystem::State::
                deliver_sync_reply(
                    pre.program.state,
                    post.program.state,
                    source_lbl,
                ));
            program_deliver_sync_reply_refines(
                pre,
                post,
                lbl,
                new_program,
                sync_req_id,
            );
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn next_refines(
    pre: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    post: SystemModel::State<UnifiedCacheBetreeProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        SystemModel::State::next(pre, post, lbl),
        refinement_inv(pre),
    ensures
        CrashAwareCachingDiskBetreeSystem::State::next(
            unified_cache_betree_system_i(pre),
            unified_cache_betree_system_i(post),
            unified_cache_betree_system_i_lbl(pre, post, lbl),
        ),
        refinement_inv(post),
{
    broadcast use vstd::multiset::group_multiset_axioms;
    reveal(SystemModel::State::next);
    reveal(SystemModel::State::next_by);

    let step =
        choose |step: SystemModel::Step<
            UnifiedCacheBetreeProgramModel,
        >| SystemModel::State::next_by(pre, post, lbl, step);
    match step {
        SystemModel::Step::accept_request() => {
            assert(SystemModel::State::accept_request(
                pre,
                post,
                lbl,
            ));
            accept_request_refines(pre, post, lbl);
        },
        SystemModel::Step::deliver_reply() => {
            deliver_reply_refines(pre, post, lbl);
        },
        SystemModel::Step::program_execute(new_program) => {
            program_execute_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        },
        SystemModel::Step::accept_sync_request() => {
            accept_sync_request_refines(pre, post, lbl);
        },
        SystemModel::Step::program_accept_sync_request(
            new_program,
        ) => {
            program_accept_sync_request_step_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        },
        SystemModel::Step::program_deliver_sync_reply(
            new_program,
        ) => {
            program_deliver_sync_reply_step_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        },
        SystemModel::Step::deliver_sync_reply() => {
            deliver_sync_reply_refines(pre, post, lbl);
        },
        SystemModel::Step::program_disk(
            new_program,
            new_disk,
        ) => {
            program_disk_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
            );
        },
        SystemModel::Step::program_internal(new_program) => {
            program_internal_refines(
                pre,
                post,
                lbl,
                new_program,
            );
        },
        SystemModel::Step::disk_internal(new_disk) => {
            disk_internal_refines(pre, post, lbl, new_disk);
        },
        SystemModel::Step::crash(new_program, new_disk) => {
            crash_refines(
                pre,
                post,
                lbl,
                new_program,
                new_disk,
            );
        },
        SystemModel::Step::noop() => {
            assert(SystemModel::State::noop(pre, post, lbl));
            system_noop_refines(pre, post, lbl);
        },
        SystemModel::Step::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }
}

} // verus!
