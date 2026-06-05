// ModelRefinement_v.rs — adapter for the staged AnotherAtomicState path.
//
// This file is now the place where the lower model is composed from:
//   SystemModel.program.state : AnotherAtomicState
//   SystemModel.disk          : AsyncDisk::State
//
// It deliberately does not route through BracketRefinement. The semantic
// interpretation from AnotherAtomicState + AsyncDisk to CTAM is still staged,
// but the proof skeleton and invariants now live at the right composition
// boundary.
//
// Also provides:
// - multiset_to_set (used by CrashAwareCachingDiskSystemRefinement_v)
// - Cache::State extensions (used by ConcreteJournalRefinement_v)
// - Draft composition invariants for AnotherAtomicState + AsyncDisk

#[allow(unused_imports)]
use vstd::prelude::*;
use vstd::prelude::*;
use vstd::assert_maps_equal;

use vstd::multiset::Multiset;
use crate::abstract_system::MsgHistory_v::{KeyedMessage, MsgHistory};
use crate::abstract_system::StampedMap_v::LSN;
use crate::spec::AsyncDisk_t::{
    Address, AsyncDisk, DiskRequest, DiskResponse, RawPage, inv_next as async_disk_inv_next,
};
use crate::spec::FloatingSeq_t::FloatingSeq;
use crate::spec::MapSpec_t::{
    AsyncMap, CrashTolerantAsyncMap, EphemeralState, ID, MapSpec, Request, Reply, SyncReqId,
    Version,
};
use crate::spec::Messages_t::Message;
use crate::trusted::SystemModel_t::SystemModel;
use crate::trusted::RefinementObligation_t::RefinementObligation;
use crate::trusted::ProgramModelTrait_t::{DiskLabel, ProgramModelTrait, ProgramUserOp};
use crate::implementation::Cache_v::{Cache, Entry, Slot, Status as CacheStatus};
use crate::implementation::CachedBranch_v::{
    CachedBranch, loaded_grow_write_nodes, loaded_seal_write_nodes,
    loaded_split_write_nodes,
};
use crate::implementation::CachedJournal_v::CachedJournal;
use crate::implementation::CachingDisk_v::{
    addresses_in_aus, PageStatus as CachingDiskPageStatus,
};
use crate::implementation::CachingDiskAdapterRefinement_v::{
    cache_filled_addr, cache_filled_page, filled_cache_status,
};
use crate::implementation::AnotherAtomicJournalRefinement_v::{
    async_disk_superblock_page_wf, branch_writes_disjoint_from_journal_projection,
    cache_read_only_access_projection_unchanged, durable_superblock_image_i,
    journal_component_refinement_inv,
    crash_aware_caching_disk_journal_i, frozen_journal_image_i, journal_caching_disk_i,
    journal_disk_cache_i, journal_disk_persistent_i,
    journal_disk_status_i, journal_image_i, journal_image_persistent_i, journal_image_projection_aus_i,
    journal_image_projection_aus_loaded_index_unchanged, journal_image_projection_domain_i,
    journal_execute_put_refines,
    journal_projection_addrs, journal_persistent_projection_addrs,
    journal_projection_aus, journal_projection_domains_unchanged_by_cache_access_outside,
    journal_projection_uses_live, on_disk_journal_addrs_i, on_disk_journal_aus_i,
    on_disk_journal_tj_i, persistent_journal_image_i, journal_projection_tight,
    journal_projection_uses_shared_async_disk, snapshot_walk_domain_none_empty,
    snapshot_walk_domain_union_outside_same,
};
use crate::implementation::AnotherAtomicBranchRefinement_v::{
    atomic_branch_metadata_loaded_flag, branch_append_from_execute_put_refines,
    branch_caching_disk_state_i, branch_component_refinement_inv, branch_disk_cache_i,
    branch_projection_aus, branch_query_refines, crash_aware_caching_disk_branch_i,
};
use crate::implementation::CrashAwareCachingDiskJournal_v::{
    CrashAwareCachingDiskJournal, snapshot_walk_domain, snapshot_walk_domain_restrict_domain_same,
};
use crate::implementation::CrashAwareCachingDiskBranch_v::CrashAwareCachingDiskBranch;
use crate::implementation::AnotherProgramModel_v::AnotherProgramModel;
use crate::implementation::AnotherAtomicState_v::{
    AnotherAtomicState, AtomicBranchState, AtomicJournalState, DiskEvent, InternalEvent,
    ProgramEvent,
};
use crate::implementation::AbstractSuperblock_v::{
    AbstractSuperblockImage, marshal_abstract_superblock, marshalled_abstract_superblock_raw_wf,
};
use crate::implementation::DiskLayout_v::spec_superblock_addr;
use crate::implementation::JournalTypes_v::{to_journal_records, to_journal_records_restrict};
use crate::allocation_layer::AllocationJournal_v::JournalImage;
use crate::allocation_layer::AllocationBranchBetree_v::summary_aus;
use crate::betree::Utils_v::{lemma_union_set_of_sets_contains, union_set_of_sets};
use crate::implementation::RecoveryState_v::RecoveryState;
use crate::disk::GenericDisk_v::{to_aus, AU};

verus!{

// ================================================================
// Shared helpers
// ================================================================

// TODO: put into vstd/multiset_lib.rs
pub open spec fn multiset_to_set<V>(m: Multiset<V>) -> Set<V> {
    Set::new(|v| m.contains(v))
}

pub open spec fn requests_replies_i(
    requests: Multiset<Request>,
    replies: Multiset<Reply>,
) -> EphemeralState
{
    EphemeralState{
        requests: multiset_to_set(requests),
        replies: multiset_to_set(replies),
    }
}

// ================================================================
// Draft AnotherAtomicState model-refinement invariants
// ================================================================

pub open spec fn another_atomic_superblock_image_wf(image: AbstractSuperblockImage) -> bool
{
    image.wf()
}

pub open spec fn another_atomic_persistent_image_wf(model: AnotherAtomicState) -> bool
{
    model.persistent_image is Some ==>
        another_atomic_superblock_image_wf(model.persistent_image.unwrap())
}

pub open spec fn another_atomic_in_flight_wf(model: AnotherAtomicState) -> bool
{
    model.in_flight is Some ==> {
        let image = model.atomic_inflight_superblock_i();
        let root_count = image.branch_roots.len() as nat;
        &&& model.journal.in_flight is Some
        &&& model.branch.in_flight is Some
        &&& model.in_flight.unwrap().boundary_lsn == image.branch_seq_end
        &&& another_atomic_superblock_image_wf(image)
        &&& root_count <= model.branch.image.sealed_roots.len()
        &&& model.branch.image.sealed_roots.take(root_count as int) == image.branch_roots
    }
}

pub open spec fn another_atomic_branch_summary_wf(model: AnotherAtomicState) -> bool
{
    &&& model.branch.branch_summary.dom() <= to_aus(model.branch.image.sealed_roots.to_set())
    &&& model.branch_metadata_loaded() ==>
        to_aus(model.branch.image.sealed_roots.to_set()) <= model.branch.branch_summary.dom()
}

pub open spec fn another_atomic_persisted_branch_prefix_metadata_wf(
    model: AnotherAtomicState,
) -> bool
{
    (model.recovery_state is MetadataLoadComplete || model.recovery_state is RecoveryComplete) ==>
        forall |i: int| #![trigger model.branch.image.sealed_roots[i]]
            0 <= i < model.branch.persisted_root_count
            ==> model.branch.branch_summary.contains_key(model.branch.image.sealed_roots[i].au)
}

pub open spec fn another_atomic_replay_progress_wf(model: AnotherAtomicState) -> bool
{
    &&& model.recovery_state is MetadataLoadComplete ==> {
        &&& model.journal_metadata_loaded()
        &&& model.branch_metadata_loaded()
        &&& model.branch.seq_end() <= model.journal.journal.seq_end()
    }
    &&& model.recovery_state is RecoveryComplete ==> {
        &&& model.journal_metadata_loaded()
        &&& model.branch_metadata_loaded()
        &&& model.branch.seq_end() == model.journal.journal.seq_end()
    }
}

pub open spec fn another_atomic_journal_mini_allocator_stage_wf(model: AnotherAtomicState) -> bool
{
    !model.client_ready() ==>
        model.journal.mini_allocator == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty()
}

pub open spec fn another_atomic_sync_request_wf(model: AnotherAtomicState) -> bool
{
    forall |sync_req_id: SyncReqId| #![trigger model.sync_req_map.contains_key(sync_req_id)]
        model.sync_req_map.contains_key(sync_req_id)
        ==> model.sync_req_map[sync_req_id] <= model.branch.seq_end()
}

pub open spec fn another_atomic_model_refinement_invariants(model: AnotherAtomicState) -> bool
{
    &&& model.cache_request_wf()
    &&& model.allocation_wf()
    &&& model.recovery_metadata_wf()
    &&& another_atomic_persistent_image_wf(model)
    &&& another_atomic_in_flight_wf(model)
    &&& another_atomic_branch_summary_wf(model)
    &&& another_atomic_persisted_branch_prefix_metadata_wf(model)
    &&& another_atomic_replay_progress_wf(model)
    &&& another_atomic_journal_mini_allocator_stage_wf(model)
    &&& another_atomic_sync_request_wf(model)
}

pub open spec fn disk_has_pending_id(disk: AsyncDisk::State, id: ID) -> bool
{
    ||| disk.requests.contains_key(id)
    ||| disk.responses.contains_key(id)
}

pub open spec fn another_atomic_cache_disk_coupling(
    atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
) -> bool
{
    forall |id: ID| #![trigger atomic.outstanding_cache_reqs.contains_key(id)]
        atomic.outstanding_cache_reqs.contains_key(id)
        ==> disk_has_pending_id(disk, id)
}

pub open spec fn another_atomic_superblock_disk_coupling(
    atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
) -> bool
{
    true
}

pub open spec fn another_atomic_superblock_write_request_wf(
    atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
) -> bool
{
    forall |id: ID| #![trigger disk.requests.contains_key(id)]
        disk.requests.contains_key(id)
        && disk.requests[id] is WriteReq
        && disk.requests[id]->to == spec_superblock_addr()
        ==> {
            &&& atomic.in_flight is Some
            &&& atomic.in_flight.unwrap().req_id == id
            &&& disk.requests[id]->data
                == marshal_abstract_superblock(atomic.atomic_inflight_superblock_i())
            &&& atomic.atomic_inflight_superblock_i().wf()
        }
}

pub open spec fn another_atomic_cache_disk_request_wf(
    atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
) -> bool
{
    forall |id: ID| #![trigger disk.requests.contains_key(id)]
        disk.requests.contains_key(id)
        && disk.requests[id].addr() != spec_superblock_addr()
        ==> {
            let req = disk.requests[id];
            let addr = req.addr();
            &&& atomic.outstanding_cache_reqs.contains_key(id)
            &&& atomic.outstanding_cache_reqs[id] == addr
            &&& req is WriteReq ==> {
                &&& cache_filled_addr(atomic.cache, req->to)
                &&& cache_filled_page(atomic.cache, req->to) == req->data
                &&& filled_cache_status(atomic.cache).contains_key(req->to)
                &&& filled_cache_status(atomic.cache)[req->to]
                    == CachingDiskPageStatus::Writeback
            }
        }
}

pub open spec fn journal_image_static_domain_i(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
) -> Set<Address>
{
    journal_image_projection_domain_i(model, image)
}

pub open spec fn journal_image_dirty_cache_disjoint_at(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
    addr: Address,
) -> bool
{
    filled_cache_status(model.program.state.cache).contains_key(addr)
        && filled_cache_status(model.program.state.cache)[addr] == CachingDiskPageStatus::Dirty
        ==> !journal_image_static_domain_i(model, image).contains(addr)
}

pub open spec fn journal_image_request_writeback_disjoint_at(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
    id: ID,
) -> bool
{
    model.disk.requests.contains_key(id)
        && model.disk.requests[id] is WriteReq
        && model.disk.requests[id]->to != spec_superblock_addr()
        ==> !journal_image_static_domain_i(model, image).contains(model.disk.requests[id]->to)
}

pub open spec fn another_atomic_superblock_write_pending(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& model.program.state.in_flight is Some
    &&& model.disk.requests.contains_key(model.program.state.in_flight.unwrap().req_id)
    &&& model.disk.requests[model.program.state.in_flight.unwrap().req_id] is WriteReq
    &&& model.disk.requests[model.program.state.in_flight.unwrap().req_id]->to
        == spec_superblock_addr()
}

pub open spec fn journal_allocable_addrs_image_disjoint(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    forall |addr: Address| #[trigger] model.program.state.journal.mini_allocator.can_allocate(addr) ==> {
        &&& !journal_image_static_domain_i(model, durable_superblock_image_i(model)).contains(addr)
        &&& model.program.state.in_flight is Some ==>
            !journal_image_static_domain_i(
                model,
                model.program.state.atomic_inflight_superblock_i(),
            ).contains(addr)
    }
}

pub open spec fn journal_image_writeback_disjoint(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& (forall |id: ID| #[trigger] model.disk.requests.contains_key(id)
        && model.disk.requests[id] is WriteReq
        && model.disk.requests[id]->to != spec_superblock_addr()
        ==> model.program.state.journal_metadata_loaded())
    &&& (forall |addr: Address| #[trigger] filled_cache_status(model.program.state.cache).contains_key(addr)
        && filled_cache_status(model.program.state.cache)[addr] == CachingDiskPageStatus::Dirty
        ==> model.program.state.journal_metadata_loaded())
    &&& (forall |addr: Address| #[trigger] filled_cache_status(model.program.state.cache).contains_key(addr) ==> {
        &&& journal_image_dirty_cache_disjoint_at(model, durable_superblock_image_i(model), addr)
        &&& another_atomic_superblock_write_pending(model) ==>
            journal_image_dirty_cache_disjoint_at(model, model.program.state.atomic_inflight_superblock_i(), addr)
    })
    &&& (forall |id: ID| #[trigger] model.disk.requests.contains_key(id) ==> {
        &&& journal_image_request_writeback_disjoint_at(model, durable_superblock_image_i(model), id)
        &&& another_atomic_superblock_write_pending(model) ==>
            journal_image_request_writeback_disjoint_at(model, model.program.state.atomic_inflight_superblock_i(), id)
    })
    &&& journal_allocable_addrs_image_disjoint(model)
}

pub open spec fn another_atomic_in_flight_superblock_landed(
    atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
) -> bool
{
    &&& atomic.in_flight is Some
    &&& disk.content.contains_key(spec_superblock_addr())
    &&& disk.content[spec_superblock_addr()]
        == marshal_abstract_superblock(atomic.atomic_inflight_superblock_i())
}

pub open spec fn another_atomic_disk_refinement_invariants(
    model: SystemModel::State<AnotherProgramModel>,
) -> bool
{
    &&& model.program.state.wf()
    &&& model.disk.inv()
    &&& async_disk_superblock_page_wf(model.disk.content)
    &&& another_atomic_model_refinement_invariants(model.program.state)
    &&& another_atomic_cache_disk_coupling(model.program.state, model.disk)
    &&& another_atomic_superblock_disk_coupling(model.program.state, model.disk)
    &&& another_atomic_superblock_write_request_wf(model.program.state, model.disk)
    &&& another_atomic_cache_disk_request_wf(model.program.state, model.disk)
    &&& journal_image_writeback_disjoint(model)
    &&& journal_component_refinement_inv(model)
    &&& branch_component_refinement_inv(model)
}

pub proof fn another_atomic_disk_refinement_invariants_initialize(
    model: SystemModel::State<AnotherProgramModel>,
)
    requires
        SystemModel::State::initialize(model, model.program, model.disk),
    ensures
        another_atomic_disk_refinement_invariants(model),
{
    reveal(SystemModel::State::initialize);
    assert(AnotherProgramModel::init(model.program));
    assert(exists |cache_slots: nat, free_aus: Set<AU>| #![auto]
        free_aus.disjoint(AnotherAtomicState::reserved_aus())
            && model.program.state == AnotherAtomicState::init(cache_slots, free_aus));
    let (cache_slots, free_aus) = choose |cache_slots: nat, free_aus: Set<AU>| #![auto]
        free_aus.disjoint(AnotherAtomicState::reserved_aus())
            && model.program.state == AnotherAtomicState::init(cache_slots, free_aus);

    assert(model.program.state == AnotherAtomicState::init(cache_slots, free_aus));
    assert_maps_equal!(
        model.program.state.cache.entries,
        Cache::State::empty(cache_slots).entries,
        slot => { }
    );
    assert(model.program.state.cache.status_map == Cache::State::empty(cache_slots).status_map);
    assert(model.program.state.cache.lookup_map == Cache::State::empty(cache_slots).lookup_map);
    assert(model.program.state.cache == Cache::State::empty(cache_slots));
    assert(Cache::State::initialize(model.program.state.cache, cache_slots)) by {
        reveal(Cache::State::initialize);
    }
    Cache::State::initialize_inductive(model.program.state.cache, cache_slots);

    assert(model.program.state.journal_metadata_loaded() == false);
    assert(model.program.state.branch.image == crate::implementation::AnotherAtomicState_v::empty_branch_image());
    assert(model.program.state.branch.persistent_image == crate::implementation::AnotherAtomicState_v::empty_branch_image());
    assert(model.program.state.branch.image.sealed_roots.len() == 0);
    assert(model.program.state.branch.persistent_image.sealed_roots.len() == 0);
    assert(model.program.state.branch.image.sealed_roots.take(
        model.program.state.branch.persistent_image.sealed_roots.len() as int,
    ) == model.program.state.branch.persistent_image.sealed_roots);
    assert(model.program.state.branch.wf());
    assert(model.program.state.branch_metadata_loaded());
    assert(model.program.state.journal_owned_aus() == Set::<AU>::empty());
    assert(model.program.state.branch_owned_aus() == Set::<AU>::empty()) by {
        assert(model.program.state.branch.branch_summary == Map::<AU, Set<AU>>::empty());
        assert(model.program.state.branch.mini_allocator.all_aus() == Set::<AU>::empty());
        assert(summary_aus(model.program.state.branch.branch_summary) == Set::<AU>::empty()) by {
            assert(model.program.state.branch.branch_summary.values() == Set::<Set<AU>>::empty());
            assert(model.program.state.branch.branch_summary.values().finite());
            assert(model.program.state.branch.branch_summary.values().len() == 0);
            assert forall |au: AU| #[trigger] summary_aus(model.program.state.branch.branch_summary).contains(au)
                implies false by {
            }
        }
        assert forall |au: AU| #[trigger] model.program.state.branch_owned_aus().contains(au)
            implies false by {
        }
    }
    assert(model.program.state.component_owned_aus() == AnotherAtomicState::reserved_aus());
    assert(model.program.state.allocation_wf());

    assert(async_disk_superblock_page_wf(model.disk.content));
    assert(durable_superblock_image_i(model) == crate::implementation::AbstractSuperblock_v::empty_abstract_superblock_image());
    assert(!journal_projection_uses_live(model));
    assert(!model.program.state.superblock_metadata_known());
    assert(on_disk_journal_addrs_i(model.disk.content) =~= Set::<Address>::empty()) by {
        assert(durable_superblock_image_i(model).journal_snapshot.freshest_rec() is None);
        assert(durable_superblock_image_i(model).journal_snapshot.boundary_lsn == 0);
        snapshot_walk_domain_none_empty(to_journal_records(model.disk.content), 0);
    }
    assert(journal_projection_addrs(model) =~= Set::<Address>::empty());
    assert(to_aus(journal_projection_addrs(model)) =~= Set::<AU>::empty()) by {
        assert forall |au: AU| #[trigger] to_aus(journal_projection_addrs(model)).contains(au)
            implies false by {
            let addr = choose |addr: Address|
                journal_projection_addrs(model).contains(addr) && addr.au == au;
            assert(false);
        }
    }
    assert(journal_projection_aus(model) =~= Set::<AU>::empty()) by {
        assert(on_disk_journal_aus_i(model.disk.content) == Set::<AU>::empty()) by {
            assert(on_disk_journal_tj_i(model.disk.content).freshest_rec is None);
            assert(on_disk_journal_tj_i(model.disk.content).build_lsn_au_index_from_first(0)
                == Map::<nat, AU>::empty());
        }
    }
    assert(journal_persistent_projection_addrs(model) =~= Set::<Address>::empty()) by {
        assert forall |addr: Address| #[trigger] journal_persistent_projection_addrs(model).contains(addr)
            implies false by {
            assert(journal_projection_addrs(model).contains(addr));
            assert(false);
        }
    }
    assert_maps_equal!(journal_disk_persistent_i(model), Map::<Address, RawPage>::empty(), addr => {
        assert(!journal_persistent_projection_addrs(model).contains(addr));
    });
    assert(persistent_journal_image_i(model).persistent == Map::<Address, RawPage>::empty());
    assert(persistent_journal_image_i(model).snapshot
        == crate::implementation::CachedJournal_v::JournalSnapshot{boundary_lsn: 0, root: None});
    assert(persistent_journal_image_i(model).seq_end == 0);
    JournalImage::empty_is_valid_image();
    assert(persistent_journal_image_i(model).i() == JournalImage::empty());
    assert(persistent_journal_image_i(model).wf());
    assert(journal_component_refinement_inv(model));
    assert(branch_component_refinement_inv(model));
}

pub proof fn program_execute_put_dispatches_components(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    req: Request,
    reply: Reply,
    receipt: crate::implementation::CachedBranch_v::LoadedPathReceipt,
    init_root: Option<Address>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
    branch: AtomicBranchState::State,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::execute_put(
            pre.program.state,
            post.program.state,
            req,
            reply,
            receipt,
            init_root,
            reads,
            writes,
            branch,
        ),
        post.disk == pre.disk,
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        reads <= branch_disk_cache_i(pre),
        writes.dom() <= addresses_in_aus(branch_projection_aus(pre)),
        to_aus(writes.dom()) <= pre.program.state.branch_owned_aus(),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        ({
            let records = MsgHistory::singleton_at(
                pre.program.state.branch.seq_end(),
                KeyedMessage{
                    key: req.input.arrow_PutInput_key(),
                    message: Message::Define{value: req.input.arrow_PutInput_value()},
                },
            );
            CrashAwareCachingDiskJournal::State::next(
                crash_aware_caching_disk_journal_i(pre),
                crash_aware_caching_disk_journal_i(post),
                CrashAwareCachingDiskJournal::Label::Put{records},
            )
        }),
        ({
            let keys = seq![req.input.arrow_PutInput_key()];
            let msgs = seq![Message::Define{value: req.input.arrow_PutInput_value()}];
            CrashAwareCachingDiskBranch::State::next(
                crash_aware_caching_disk_branch_i(pre),
                crash_aware_caching_disk_branch_i(post),
                CrashAwareCachingDiskBranch::Label::Append{keys, msgs},
            )
        }),
        crash_aware_caching_disk_journal_i(post).inv(),
        crash_aware_caching_disk_branch_i(post).inv(),
{
    let key = req.input.arrow_PutInput_key();
    let value = req.input.arrow_PutInput_value();
    let msg = Message::Define{value};
    let records = MsgHistory::singleton_at(
        pre.program.state.branch.seq_end(),
        KeyedMessage{key, message: msg},
    );
    let jlbl = CrashAwareCachingDiskJournal::Label::Put{records};
    let blbl = CrashAwareCachingDiskBranch::Label::Append{
        keys: seq![key],
        msgs: seq![msg],
    };

    journal_execute_put_refines(
        pre,
        post,
        req,
        reply,
        receipt,
        init_root,
        reads,
        writes,
        branch,
    );
    CrashAwareCachingDiskJournal::State::inv_next(
        crash_aware_caching_disk_journal_i(pre),
        crash_aware_caching_disk_journal_i(post),
        jlbl,
    );

    branch_append_from_execute_put_refines(
        pre,
        post,
        req,
        reply,
        receipt,
        init_root,
        reads,
        writes,
        branch,
    );
    CrashAwareCachingDiskBranch::State::inv_next(
        crash_aware_caching_disk_branch_i(pre),
        crash_aware_caching_disk_branch_i(post),
        blbl,
    );
}

pub proof fn program_execute_query_dispatches_components(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    req: Request,
    reply: Reply,
    end_lsn: LSN,
    key: crate::spec::KeyType_t::Key,
    value: crate::spec::Messages_t::Value,
    msg: Message,
    receipts: Seq<crate::implementation::CachedBranch_v::LoadedPathReceipt>,
    reads: Map<Address, RawPage>,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        AnotherAtomicState::execute_query(
            pre.program.state,
            post.program.state,
            req,
            reply,
            end_lsn,
            key,
            value,
            msg,
            receipts,
            reads,
        ),
        post.disk == pre.disk,
        branch_projection_aus(post) =~= branch_projection_aus(pre),
        reads <= branch_disk_cache_i(pre),
        atomic_branch_metadata_loaded_flag(pre.program.state.branch),
    ensures
        crash_aware_caching_disk_journal_i(post) == crash_aware_caching_disk_journal_i(pre),
        CrashAwareCachingDiskBranch::State::next(
            crash_aware_caching_disk_branch_i(pre),
            crash_aware_caching_disk_branch_i(post),
            CrashAwareCachingDiskBranch::Label::Query{key, value},
        ),
        crash_aware_caching_disk_journal_i(post).inv(),
        crash_aware_caching_disk_branch_i(post).inv(),
{
    assert(post.program.state.journal == pre.program.state.journal);
    assert(post.program.state.in_flight == pre.program.state.in_flight);
    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
    journal_projection_domains_unchanged_by_cache_access_outside(
        pre,
        post,
        reads,
        Map::<Address, RawPage>::empty(),
    );
    assert(journal_projection_aus(post) =~= journal_projection_aus(pre));
    cache_read_only_access_projection_unchanged(pre, post, reads);
    assert(journal_caching_disk_i(post) == journal_caching_disk_i(pre));
    assert(crash_aware_caching_disk_journal_i(post) == crash_aware_caching_disk_journal_i(pre));

    branch_query_refines(
        pre,
        post,
        req,
        reply,
        end_lsn,
        key,
        value,
        msg,
        receipts,
        reads,
    );
    CrashAwareCachingDiskBranch::State::inv_next(
        crash_aware_caching_disk_branch_i(pre),
        crash_aware_caching_disk_branch_i(post),
        CrashAwareCachingDiskBranch::Label::Query{key, value},
    );
}

pub proof fn async_disk_superblock_page_wf_preserved_by_internal(
    atomic: AnotherAtomicState,
    pre_disk: AsyncDisk::State,
    post_disk: AsyncDisk::State,
)
    requires
        async_disk_superblock_page_wf(pre_disk.content),
        another_atomic_superblock_write_request_wf(atomic, pre_disk),
        AsyncDisk::State::next(pre_disk, post_disk, DiskLabel::Internal{}),
    ensures
        async_disk_superblock_page_wf(post_disk.content),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let step = choose |step| AsyncDisk::State::next_by(pre_disk, post_disk, DiskLabel::Internal{}, step);
    match step {
        AsyncDisk::Step::process_read(id) => {
            assert(AsyncDisk::State::next_by(
                pre_disk,
                post_disk,
                DiskLabel::Internal{},
                AsyncDisk::Step::process_read(id),
            ));
            assert(post_disk.content == pre_disk.content);
        },
        AsyncDisk::Step::process_write(id) => {
            assert(AsyncDisk::State::next_by(
                pre_disk,
                post_disk,
                DiskLabel::Internal{},
                AsyncDisk::Step::process_write(id),
            ));
            assert(pre_disk.requests.contains_key(id));
            assert(pre_disk.requests[id] is WriteReq);
            let req = pre_disk.requests[id];
            assert(post_disk.content == pre_disk.content.insert(req->to, req->data));
            if req->to == spec_superblock_addr() {
                assert(atomic.in_flight is Some);
                assert(atomic.in_flight.unwrap().req_id == id);
                assert(req->data == marshal_abstract_superblock(atomic.atomic_inflight_superblock_i()));
                assert(atomic.atomic_inflight_superblock_i().wf());
                marshalled_abstract_superblock_raw_wf(atomic.atomic_inflight_superblock_i());
                assert(post_disk.content.contains_key(spec_superblock_addr()));
                assert(post_disk.content[spec_superblock_addr()] == req->data);
                assert(another_atomic_in_flight_superblock_landed(atomic, post_disk));
            } else {
                assert(post_disk.content.contains_key(spec_superblock_addr()));
                assert(post_disk.content[spec_superblock_addr()] == pre_disk.content[spec_superblock_addr()]);
            }
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn disk_has_pending_id_preserved_by_internal(
    pre_disk: AsyncDisk::State,
    post_disk: AsyncDisk::State,
    id: ID,
)
    requires
        disk_has_pending_id(pre_disk, id),
        AsyncDisk::State::next(pre_disk, post_disk, DiskLabel::Internal{}),
    ensures
        disk_has_pending_id(post_disk, id),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let step = choose |step| AsyncDisk::State::next_by(pre_disk, post_disk, DiskLabel::Internal{}, step);
    match step {
        AsyncDisk::Step::process_read(processed_id) => {
            assert(AsyncDisk::State::next_by(
                pre_disk,
                post_disk,
                DiskLabel::Internal{},
                AsyncDisk::Step::process_read(processed_id),
            ));
            if id == processed_id {
                assert(post_disk.responses.contains_key(id));
            } else {
                if pre_disk.requests.contains_key(id) {
                    assert(post_disk.requests.contains_key(id));
                } else {
                    assert(pre_disk.responses.contains_key(id));
                    assert(post_disk.responses.contains_key(id));
                }
            }
        },
        AsyncDisk::Step::process_write(processed_id) => {
            assert(AsyncDisk::State::next_by(
                pre_disk,
                post_disk,
                DiskLabel::Internal{},
                AsyncDisk::Step::process_write(processed_id),
            ));
            if id == processed_id {
                assert(post_disk.responses.contains_key(id));
            } else {
                if pre_disk.requests.contains_key(id) {
                    assert(post_disk.requests.contains_key(id));
                } else {
                    assert(pre_disk.responses.contains_key(id));
                    assert(post_disk.responses.contains_key(id));
                }
            }
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn superblock_write_request_wf_preserved_by_internal(
    atomic: AnotherAtomicState,
    pre_disk: AsyncDisk::State,
    post_disk: AsyncDisk::State,
)
    requires
        another_atomic_superblock_write_request_wf(atomic, pre_disk),
        AsyncDisk::State::next(pre_disk, post_disk, DiskLabel::Internal{}),
    ensures
        another_atomic_superblock_write_request_wf(atomic, post_disk),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let step = choose |step| AsyncDisk::State::next_by(pre_disk, post_disk, DiskLabel::Internal{}, step);
    match step {
        AsyncDisk::Step::process_read(processed_id) => {
            assert forall |id: ID| #![trigger post_disk.requests.contains_key(id)]
                post_disk.requests.contains_key(id)
                && post_disk.requests[id] is WriteReq
                && post_disk.requests[id]->to == spec_superblock_addr()
                implies {
                    &&& atomic.in_flight is Some
                    &&& atomic.in_flight.unwrap().req_id == id
                    &&& post_disk.requests[id]->data
                        == marshal_abstract_superblock(atomic.atomic_inflight_superblock_i())
                    &&& atomic.atomic_inflight_superblock_i().wf()
                }
            by {
                assert(post_disk.requests == pre_disk.requests.remove(processed_id));
                assert(pre_disk.requests.contains_key(id));
                assert(post_disk.requests[id] == pre_disk.requests[id]);
            }
        },
        AsyncDisk::Step::process_write(processed_id) => {
            assert forall |id: ID| #![trigger post_disk.requests.contains_key(id)]
                post_disk.requests.contains_key(id)
                && post_disk.requests[id] is WriteReq
                && post_disk.requests[id]->to == spec_superblock_addr()
                implies {
                    &&& atomic.in_flight is Some
                    &&& atomic.in_flight.unwrap().req_id == id
                    &&& post_disk.requests[id]->data
                        == marshal_abstract_superblock(atomic.atomic_inflight_superblock_i())
                    &&& atomic.atomic_inflight_superblock_i().wf()
                }
            by {
                assert(post_disk.requests == pre_disk.requests.remove(processed_id));
                assert(pre_disk.requests.contains_key(id));
                assert(post_disk.requests[id] == pre_disk.requests[id]);
            }
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn cache_disk_request_wf_preserved_by_internal(
    atomic: AnotherAtomicState,
    pre_disk: AsyncDisk::State,
    post_disk: AsyncDisk::State,
)
    requires
        another_atomic_cache_disk_request_wf(atomic, pre_disk),
        AsyncDisk::State::next(pre_disk, post_disk, DiskLabel::Internal{}),
    ensures
        another_atomic_cache_disk_request_wf(atomic, post_disk),
{
    reveal(AsyncDisk::State::next);
    reveal(AsyncDisk::State::next_by);
    let step = choose |step| AsyncDisk::State::next_by(pre_disk, post_disk, DiskLabel::Internal{}, step);
    match step {
        AsyncDisk::Step::process_read(processed_id) => {
            assert forall |id: ID| #![trigger post_disk.requests.contains_key(id)]
                post_disk.requests.contains_key(id)
                && post_disk.requests[id].addr() != spec_superblock_addr()
                implies {
                    let req = post_disk.requests[id];
                    let addr = req.addr();
                    &&& atomic.outstanding_cache_reqs.contains_key(id)
                    &&& atomic.outstanding_cache_reqs[id] == addr
                    &&& req is WriteReq ==> {
                        &&& cache_filled_addr(atomic.cache, req->to)
                        &&& cache_filled_page(atomic.cache, req->to) == req->data
                        &&& filled_cache_status(atomic.cache).contains_key(req->to)
                        &&& filled_cache_status(atomic.cache)[req->to]
                            == CachingDiskPageStatus::Writeback
                    }
                }
            by {
                assert(post_disk.requests == pre_disk.requests.remove(processed_id));
                assert(pre_disk.requests.contains_key(id));
                assert(post_disk.requests[id] == pre_disk.requests[id]);
            }
        },
        AsyncDisk::Step::process_write(processed_id) => {
            assert forall |id: ID| #![trigger post_disk.requests.contains_key(id)]
                post_disk.requests.contains_key(id)
                && post_disk.requests[id].addr() != spec_superblock_addr()
                implies {
                    let req = post_disk.requests[id];
                    let addr = req.addr();
                    &&& atomic.outstanding_cache_reqs.contains_key(id)
                    &&& atomic.outstanding_cache_reqs[id] == addr
                    &&& req is WriteReq ==> {
                        &&& cache_filled_addr(atomic.cache, req->to)
                        &&& cache_filled_page(atomic.cache, req->to) == req->data
                        &&& filled_cache_status(atomic.cache).contains_key(req->to)
                        &&& filled_cache_status(atomic.cache)[req->to]
                            == CachingDiskPageStatus::Writeback
                    }
                }
            by {
                assert(post_disk.requests == pre_disk.requests.remove(processed_id));
                assert(pre_disk.requests.contains_key(id));
                assert(post_disk.requests[id] == pre_disk.requests[id]);
            }
        },
        _ => {
            assert(false);
        },
    }
}

pub proof fn cache_disk_request_wf_preserved_by_unchanged(
    pre_atomic: AnotherAtomicState,
    post_atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
)
    requires
        another_atomic_cache_disk_request_wf(pre_atomic, disk),
        post_atomic.cache == pre_atomic.cache,
        post_atomic.outstanding_cache_reqs == pre_atomic.outstanding_cache_reqs,
    ensures
        another_atomic_cache_disk_request_wf(post_atomic, disk),
{
    assert forall |id: ID| #[trigger] disk.requests.contains_key(id)
        && disk.requests[id].addr() != spec_superblock_addr()
        implies {
            let req = disk.requests[id];
            let addr = req.addr();
            &&& post_atomic.outstanding_cache_reqs.contains_key(id)
            &&& post_atomic.outstanding_cache_reqs[id] == addr
            &&& req is WriteReq ==> {
                &&& cache_filled_addr(post_atomic.cache, req->to)
                &&& cache_filled_page(post_atomic.cache, req->to) == req->data
                &&& filled_cache_status(post_atomic.cache).contains_key(req->to)
                &&& filled_cache_status(post_atomic.cache)[req->to]
                    == CachingDiskPageStatus::Writeback
            }
        }
    by { }
}

pub proof fn cache_disk_request_wf_preserved_by_cache_internal(
    pre_atomic: AnotherAtomicState,
    post_atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
)
    requires
        pre_atomic.cache.inv(),
        another_atomic_cache_disk_request_wf(pre_atomic, disk),
        Cache::State::next(pre_atomic.cache, post_atomic.cache, Cache::Label::Internal{}),
        post_atomic.outstanding_cache_reqs == pre_atomic.outstanding_cache_reqs,
    ensures
        another_atomic_cache_disk_request_wf(post_atomic, disk),
{
    Cache::State::inv_next(pre_atomic.cache, post_atomic.cache, Cache::Label::Internal{});
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let step = choose |step: Cache::Step| Cache::State::next_by(
        pre_atomic.cache,
        post_atomic.cache,
        Cache::Label::Internal{},
        step,
    );
    assert forall |id: ID| #[trigger] disk.requests.contains_key(id)
        && disk.requests[id].addr() != spec_superblock_addr()
        implies {
            let req = disk.requests[id];
            let addr = req.addr();
            &&& post_atomic.outstanding_cache_reqs.contains_key(id)
            &&& post_atomic.outstanding_cache_reqs[id] == addr
            &&& req is WriteReq ==> {
                &&& cache_filled_addr(post_atomic.cache, req->to)
                &&& cache_filled_page(post_atomic.cache, req->to) == req->data
                &&& filled_cache_status(post_atomic.cache).contains_key(req->to)
                &&& filled_cache_status(post_atomic.cache)[req->to]
                    == CachingDiskPageStatus::Writeback
            }
        }
    by {
        let req = disk.requests[id];
        let addr = req.addr();
        assert(pre_atomic.outstanding_cache_reqs.contains_key(id));
        assert(post_atomic.outstanding_cache_reqs.contains_key(id));
        assert(post_atomic.outstanding_cache_reqs[id] == addr);
        if req is WriteReq {
            assert(cache_filled_addr(pre_atomic.cache, req->to));
            assert(cache_filled_page(pre_atomic.cache, req->to) == req->data);
            assert(filled_cache_status(pre_atomic.cache).contains_key(req->to));
            assert(filled_cache_status(pre_atomic.cache)[req->to]
                == CachingDiskPageStatus::Writeback);
            let pre_slot = pre_atomic.cache.lookup_map[req->to];
            assert(pre_atomic.cache.entries.contains_key(pre_slot));
            assert(pre_atomic.cache.entries[pre_slot] is Filled);
            assert(pre_atomic.cache.status_map.contains_key(pre_slot));
            assert(pre_atomic.cache.status_map[pre_slot] is Writeback);
            match step {
                Cache::Step::reserve(new_slots_mapping) => {
                    assert(Cache::State::reserve(
                        pre_atomic.cache,
                        post_atomic.cache,
                        Cache::Label::Internal{},
                        new_slots_mapping,
                    ));
                    let new_addr_slots = new_slots_mapping.invert();
                    assert(post_atomic.cache.lookup_map
                        == pre_atomic.cache.lookup_map.union_prefer_right(new_addr_slots));
                    assert(!new_addr_slots.contains_key(req->to)) by {
                        if new_addr_slots.contains_key(req->to) {
                            assert(new_slots_mapping.contains_value(req->to));
                            assert(pre_atomic.cache.valid_new_slots_mapping(new_slots_mapping));
                            assert(new_slots_mapping.values().disjoint(pre_atomic.cache.lookup_map.dom()));
                            assert(pre_atomic.cache.lookup_map.contains_key(req->to));
                            assert(false);
                        }
                    }
                    assert(post_atomic.cache.lookup_map[req->to] == pre_slot);
                    assert(!new_slots_mapping.contains_key(pre_slot)) by {
                        if new_slots_mapping.contains_key(pre_slot) {
                            assert(pre_atomic.cache.valid_new_slots_mapping(new_slots_mapping));
                            assert(pre_atomic.cache.entries[pre_slot] is Empty);
                            assert(false);
                        }
                    }
                    let updated_entries = Map::new(
                        |slot| new_slots_mapping.contains_key(slot),
                        |slot| Entry::Reserved{addr: new_slots_mapping[slot]},
                    );
                    assert(post_atomic.cache.entries
                        == pre_atomic.cache.entries.union_prefer_right(updated_entries));
                    assert(!updated_entries.contains_key(pre_slot));
                    assert(post_atomic.cache.entries[pre_slot] == pre_atomic.cache.entries[pre_slot]);
                    assert(post_atomic.cache.status_map == pre_atomic.cache.status_map);
                    assert(post_atomic.cache.status_map[pre_slot]
                        == pre_atomic.cache.status_map[pre_slot]);
                },
                Cache::Step::evict(evicted_slots) => {
                    assert(Cache::State::evict(
                        pre_atomic.cache,
                        post_atomic.cache,
                        Cache::Label::Internal{},
                        evicted_slots,
                    ));
                    pre_atomic.cache.build_lookup_map_ensures();
                    assert(pre_atomic.cache.build_lookup_map_props(pre_atomic.cache.lookup_map));
                    let evicted_addrs = Map::new(
                        |slot| evicted_slots.contains(slot),
                        |slot| pre_atomic.cache.entries[slot].get_addr(),
                    ).values();
                    assert(post_atomic.cache.lookup_map
                        == pre_atomic.cache.lookup_map.remove_keys(evicted_addrs));
                    assert(!evicted_addrs.contains(req->to)) by {
                        if evicted_addrs.contains(req->to) {
                            let evicted_map = Map::new(
                                |slot| evicted_slots.contains(slot),
                                |slot| pre_atomic.cache.entries[slot].get_addr(),
                            );
                            let evicted_slot = choose |slot: Slot|
                                evicted_map.contains_key(slot) && evicted_map[slot] == req->to;
                            assert(evicted_slots.contains(evicted_slot));
                            assert(pre_atomic.cache.entries.contains_key(evicted_slot));
                            assert(pre_atomic.cache.entries[evicted_slot] is Filled);
                            assert(pre_atomic.cache.status_map[evicted_slot] is Clean);
                            assert(pre_atomic.cache.entries[evicted_slot].get_addr() == req->to);
                            assert(pre_atomic.cache.lookup_map[req->to] == evicted_slot);
                            assert(pre_slot == evicted_slot);
                            assert(pre_atomic.cache.status_map[pre_slot] is Clean);
                            assert(false);
                        }
                    }
                    assert(post_atomic.cache.lookup_map[req->to] == pre_slot);
                    assert(!evicted_slots.contains(pre_slot)) by {
                        if evicted_slots.contains(pre_slot) {
                            assert(pre_atomic.cache.status_map[pre_slot] is Clean);
                            assert(false);
                        }
                    }
                    let updated_entries = Map::new(
                        |slot| evicted_slots.contains(slot),
                        |slot| Entry::Empty,
                    );
                    let updated_status_map = Map::new(
                        |slot| evicted_slots.contains(slot),
                        |slot| CacheStatus::NotFilled,
                    );
                    assert(post_atomic.cache.entries
                        == pre_atomic.cache.entries.union_prefer_right(updated_entries));
                    assert(post_atomic.cache.status_map
                        == pre_atomic.cache.status_map.union_prefer_right(updated_status_map));
                    assert(!updated_entries.contains_key(pre_slot));
                    assert(!updated_status_map.contains_key(pre_slot));
                    assert(post_atomic.cache.entries[pre_slot] == pre_atomic.cache.entries[pre_slot]);
                    assert(post_atomic.cache.status_map[pre_slot]
                        == pre_atomic.cache.status_map[pre_slot]);
                },
                Cache::Step::noop() => {
                    assert(Cache::State::noop(
                        pre_atomic.cache,
                        post_atomic.cache,
                        Cache::Label::Internal{},
                    ));
                    assert(post_atomic.cache == pre_atomic.cache);
                },
                _ => {
                    assert(false);
                },
            }
            assert(cache_filled_addr(post_atomic.cache, req->to));
            assert(cache_filled_page(post_atomic.cache, req->to) == req->data);
            assert(filled_cache_status(post_atomic.cache).contains_key(req->to));
            assert(filled_cache_status(post_atomic.cache)[req->to]
                == CachingDiskPageStatus::Writeback);
        }
    }
}

pub proof fn cache_disk_request_wf_preserved_by_cache_access(
    pre_atomic: AnotherAtomicState,
    post_atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre_atomic.cache.inv(),
        another_atomic_cache_disk_request_wf(pre_atomic, disk),
        Cache::State::next(
            pre_atomic.cache,
            post_atomic.cache,
            Cache::Label::Access{reads, writes},
        ),
        post_atomic.outstanding_cache_reqs == pre_atomic.outstanding_cache_reqs,
    ensures
        another_atomic_cache_disk_request_wf(post_atomic, disk),
{
    Cache::State::inv_next(
        pre_atomic.cache,
        post_atomic.cache,
        Cache::Label::Access{reads, writes},
    );
    post_atomic.cache.build_lookup_map_ensures();
    assert(post_atomic.cache.build_lookup_map_props(post_atomic.cache.lookup_map));
    assert forall |id: ID| #[trigger] disk.requests.contains_key(id)
        && disk.requests[id].addr() != spec_superblock_addr()
        implies {
            let req = disk.requests[id];
            let addr = req.addr();
            &&& post_atomic.outstanding_cache_reqs.contains_key(id)
            &&& post_atomic.outstanding_cache_reqs[id] == addr
            &&& req is WriteReq ==> {
                &&& cache_filled_addr(post_atomic.cache, req->to)
                &&& cache_filled_page(post_atomic.cache, req->to) == req->data
                &&& filled_cache_status(post_atomic.cache).contains_key(req->to)
                &&& filled_cache_status(post_atomic.cache)[req->to]
                    == CachingDiskPageStatus::Writeback
            }
        }
    by {
        let req = disk.requests[id];
        let addr = req.addr();
        assert(pre_atomic.outstanding_cache_reqs.contains_key(id));
        assert(post_atomic.outstanding_cache_reqs.contains_key(id));
        assert(post_atomic.outstanding_cache_reqs[id] == addr);
        if req is WriteReq {
            assert(cache_filled_addr(pre_atomic.cache, req->to));
            assert(cache_filled_page(pre_atomic.cache, req->to) == req->data);
            assert(filled_cache_status(pre_atomic.cache).contains_key(req->to));
            assert(filled_cache_status(pre_atomic.cache)[req->to]
                == CachingDiskPageStatus::Writeback);
            assert(!writes.contains_key(req->to)) by {
                if writes.contains_key(req->to) {
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre_atomic.cache,
                        post_atomic.cache,
                        Cache::Label::Access{reads, writes},
                        Cache::Step::access(),
                    ));
                    assert(pre_atomic.cache.valid_write(req->to));
                    let slot = pre_atomic.cache.lookup_map[req->to];
                    assert(pre_atomic.cache.entries[slot] is Filled);
                    assert(cache_filled_page(pre_atomic.cache, req->to)
                        == pre_atomic.cache.entries[slot]->data);
                    assert(filled_cache_status(pre_atomic.cache)[req->to]
                        == CachingDiskPageStatus::Writeback);
                    assert(pre_atomic.cache.status_map[slot] == CacheStatus::Writeback);
                    assert(!(pre_atomic.cache.valid_write(req->to)));
                    assert(false);
                }
            }
            Cache::State::access_unwritten_addr_unchanged(
                pre_atomic.cache,
                post_atomic.cache,
                reads,
                writes,
                req->to,
            );
            let pre_slot = pre_atomic.cache.lookup_map[req->to];
            let post_slot = post_atomic.cache.lookup_map[req->to];
            assert(post_slot == pre_slot);
            assert(post_atomic.cache.entries.contains_key(post_slot));
            assert(post_atomic.cache.entries[post_slot]
                == pre_atomic.cache.entries[pre_slot]);
            assert(post_atomic.cache.status_map[post_slot]
                == pre_atomic.cache.status_map[pre_slot]);
            assert(cache_filled_addr(post_atomic.cache, req->to));
            assert(cache_filled_page(post_atomic.cache, req->to) == req->data);
            assert(filled_cache_status(post_atomic.cache).contains_key(req->to));
            assert(filled_cache_status(post_atomic.cache)[req->to]
                == CachingDiskPageStatus::Writeback);
        }
    }
}

pub proof fn journal_image_persistent_preserved_by_disjoint_write(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
    addr: Address,
    data: RawPage,
)
    requires
        post.program.state == pre.program.state,
        pre.program.state.journal_metadata_loaded(),
        post.disk.content == pre.disk.content.insert(addr, data),
        !journal_image_static_domain_i(pre, image).contains(addr),
    ensures
        journal_image_persistent_i(post, image) == journal_image_persistent_i(pre, image),
{
    let raw_update = Map::<Address, RawPage>::empty().insert(addr, data);
    let record_update = to_journal_records(raw_update);
    assert(post.disk.content =~= pre.disk.content.union_prefer_right(raw_update)) by {
        assert_maps_equal!(post.disk.content, pre.disk.content.union_prefer_right(raw_update), a => {
            if a == addr {
                assert(raw_update.contains_key(a));
            } else {
                assert(!raw_update.contains_key(a));
            }
        });
    }
    assert(to_journal_records(post.disk.content)
        =~= to_journal_records(pre.disk.content).union_prefer_right(record_update)) by {
        assert_maps_equal!(
            to_journal_records(post.disk.content),
            to_journal_records(pre.disk.content).union_prefer_right(record_update),
            a => {
                if a == addr {
                    assert(record_update.contains_key(a));
                    assert(post.disk.content[a] == data);
                    assert(raw_update[a] == data);
                } else {
                    assert(!raw_update.contains_key(a));
                    assert(!record_update.contains_key(a));
                    if to_journal_records(post.disk.content).contains_key(a) {
                        assert(post.disk.content.contains_key(a));
                        assert(pre.disk.content.contains_key(a));
                        assert(post.disk.content[a] == pre.disk.content[a]);
                    }
                    if to_journal_records(pre.disk.content).union_prefer_right(record_update).contains_key(a) {
                        assert(to_journal_records(pre.disk.content).contains_key(a));
                        assert(pre.disk.content.contains_key(a));
                        assert(post.disk.content.contains_key(a));
                        assert(post.disk.content[a] == pre.disk.content[a]);
                    }
                }
            }
        );
    }
    assert(record_update.dom().disjoint(journal_image_static_domain_i(pre, image))) by {
        assert forall |a: Address| #[trigger] record_update.dom().contains(a)
            implies !journal_image_static_domain_i(pre, image).contains(a) by {
            assert(raw_update.contains_key(a));
            assert(a == addr);
        }
    }
    snapshot_walk_domain_union_outside_same(
        to_journal_records(pre.disk.content),
        record_update,
        image.journal_snapshot.boundary_lsn,
        image.journal_snapshot.freshest_rec(),
    );
    assert(journal_image_projection_domain_i(post, image)
        =~= journal_image_projection_domain_i(pre, image)) by {
        assert forall |a: Address|
            journal_image_projection_domain_i(post, image).contains(a)
                <==> journal_image_projection_domain_i(pre, image).contains(a)
        by {
            assert(to_journal_records(post.disk.content)
                =~= to_journal_records(pre.disk.content).union_prefer_right(record_update));
        }
    }
    assert_maps_equal!(
        journal_image_persistent_i(post, image),
        journal_image_persistent_i(pre, image),
        a => {
            assert(journal_image_projection_domain_i(post, image).contains(a)
                <==> journal_image_projection_domain_i(pre, image).contains(a));
            if a == addr {
                assert(!journal_image_projection_domain_i(pre, image).contains(a));
                assert(!journal_image_projection_domain_i(post, image).contains(a));
            } else {
                assert(post.disk.content[a] == pre.disk.content[a]);
            }
        }
    );
}

pub proof fn journal_image_static_domain_unchanged_by_loaded_index_preservation(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
)
    requires
        post.disk.content == pre.disk.content,
        pre.program.state.journal_metadata_loaded(),
        post.program.state.journal_metadata_loaded(),
    ensures
        journal_image_static_domain_i(post, image) =~= journal_image_static_domain_i(pre, image),
{
    assert forall |addr: Address|
        journal_image_static_domain_i(post, image).contains(addr)
            <==> journal_image_static_domain_i(pre, image).contains(addr)
    by {
        assert(post.disk.content == pre.disk.content);
    }
}

pub proof fn journal_image_writeback_disjoint_preserved_by_cache_access(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
    writes: Map<Address, RawPage>,
)
    requires
        pre.program.state.cache.inv(),
        journal_image_writeback_disjoint(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes},
        ),
        post.disk == pre.disk,
        pre.program.state.journal_metadata_loaded(),
        post.program.state.journal_metadata_loaded(),
        forall |addr: Address| #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
            ==> pre.program.state.journal.mini_allocator.can_allocate(addr),
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
        writes.dom().disjoint(journal_image_static_domain_i(pre, durable_superblock_image_i(pre))),
        another_atomic_superblock_write_pending(pre) ==>
            writes.dom().disjoint(journal_image_static_domain_i(
                pre,
                pre.program.state.atomic_inflight_superblock_i(),
            )),
    ensures
        journal_image_writeback_disjoint(post),
{
    let durable_image = durable_superblock_image_i(pre);
    pre.program.state.cache.build_lookup_map_ensures();
    assert(pre.program.state.cache.build_lookup_map_props(pre.program.state.cache.lookup_map));
    assert(durable_superblock_image_i(post) == durable_image);
    journal_image_static_domain_unchanged_by_loaded_index_preservation(pre, post, durable_image);
    if pre.program.state.in_flight is Some {
        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
        assert(post.program.state.in_flight is Some);
        assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
        journal_image_static_domain_unchanged_by_loaded_index_preservation(pre, post, frozen_image);
    }

    assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
        implies {
            &&& journal_image_dirty_cache_disjoint_at(post, durable_image, addr)
            &&& another_atomic_superblock_write_pending(post) ==>
                journal_image_dirty_cache_disjoint_at(
                    post,
                    post.program.state.atomic_inflight_superblock_i(),
                    addr,
                )
        }
    by {
        if filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty {
            assert(post.program.state.journal_metadata_loaded());
            if writes.contains_key(addr) {
                assert(writes.dom().contains(addr));
                assert(!journal_image_static_domain_i(pre, durable_image).contains(addr));
                assert(!journal_image_static_domain_i(post, durable_image).contains(addr));
                if another_atomic_superblock_write_pending(post) {
                    assert(pre.program.state.in_flight is Some);
                    assert(another_atomic_superblock_write_pending(pre));
                    let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                    assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                    assert(!journal_image_static_domain_i(pre, frozen_image).contains(addr));
                    assert(!journal_image_static_domain_i(post, frozen_image).contains(addr));
                }
            } else {
                Cache::State::access_unwritten_addr_unchanged(
                    pre.program.state.cache,
                    post.program.state.cache,
                    reads,
                    writes,
                    addr,
                );
                assert(cache_filled_addr(pre.program.state.cache, addr));
                assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                assert(filled_cache_status(pre.program.state.cache)[addr]
                    == CachingDiskPageStatus::Dirty);
                assert(pre.program.state.journal_metadata_loaded());
                assert(journal_image_dirty_cache_disjoint_at(pre, durable_image, addr));
                assert(!journal_image_static_domain_i(pre, durable_image).contains(addr));
                assert(!journal_image_static_domain_i(post, durable_image).contains(addr));
                if another_atomic_superblock_write_pending(post) {
                    assert(pre.program.state.in_flight is Some);
                    assert(another_atomic_superblock_write_pending(pre));
                    let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                    assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                    assert(journal_image_dirty_cache_disjoint_at(pre, frozen_image, addr));
                    assert(!journal_image_static_domain_i(pre, frozen_image).contains(addr));
                    assert(!journal_image_static_domain_i(post, frozen_image).contains(addr));
                }
            }
        }
    }

    assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
        implies {
            &&& journal_image_request_writeback_disjoint_at(post, durable_image, id)
            &&& another_atomic_superblock_write_pending(post) ==>
                journal_image_request_writeback_disjoint_at(
                    post,
                    post.program.state.atomic_inflight_superblock_i(),
                    id,
                )
        }
    by {
        assert(post.disk.requests == pre.disk.requests);
        if post.disk.requests[id] is WriteReq && post.disk.requests[id]->to != spec_superblock_addr() {
            assert(pre.program.state.journal_metadata_loaded());
            assert(post.program.state.journal_metadata_loaded());
            assert(journal_image_request_writeback_disjoint_at(pre, durable_image, id));
            assert(!journal_image_static_domain_i(pre, durable_image).contains(post.disk.requests[id]->to));
            assert(!journal_image_static_domain_i(post, durable_image).contains(post.disk.requests[id]->to));
            if another_atomic_superblock_write_pending(post) {
                assert(pre.program.state.in_flight is Some);
                assert(another_atomic_superblock_write_pending(pre));
                let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                assert(journal_image_request_writeback_disjoint_at(pre, frozen_image, id));
                assert(!journal_image_static_domain_i(pre, frozen_image).contains(post.disk.requests[id]->to));
                assert(!journal_image_static_domain_i(post, frozen_image).contains(post.disk.requests[id]->to));
            }
        }
    }
    assert(journal_allocable_addrs_image_disjoint(post)) by {
        assert forall |addr: Address| #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
            implies {
                &&& !journal_image_static_domain_i(post, durable_image).contains(addr)
                &&& post.program.state.in_flight is Some ==>
                    !journal_image_static_domain_i(
                        post,
                        post.program.state.atomic_inflight_superblock_i(),
                    ).contains(addr)
            } by {
            assert(pre.program.state.journal.mini_allocator.can_allocate(addr));
            assert(journal_allocable_addrs_image_disjoint(pre));
            assert(!journal_image_static_domain_i(pre, durable_image).contains(addr));
            assert(!journal_image_static_domain_i(post, durable_image).contains(addr));
            if post.program.state.in_flight is Some {
                assert(pre.program.state.in_flight is Some);
                let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                assert(!journal_image_static_domain_i(pre, frozen_image).contains(addr));
                assert(!journal_image_static_domain_i(post, frozen_image).contains(addr));
            }
        }
    }
}

pub proof fn journal_image_writeback_disjoint_preserved_by_cache_io_begin(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    req_map: Map<ID, DiskRequest>,
)
    requires
        pre.program.state.cache.inv(),
        journal_image_writeback_disjoint(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
        ),
        post.disk.content == pre.disk.content,
        post.disk.requests == pre.disk.requests.union_prefer_right(req_map),
        post.program.state.journal == pre.program.state.journal,
        post.program.state.branch == pre.program.state.branch,
        post.program.state.in_flight == pre.program.state.in_flight,
        another_atomic_superblock_write_pending(post) ==>
            another_atomic_superblock_write_pending(pre),
    ensures
        journal_image_writeback_disjoint(post),
{
    let durable_image = durable_superblock_image_i(pre);
    assert(durable_superblock_image_i(post) == durable_image);
    assert(post.program.state.journal_metadata_loaded() == pre.program.state.journal_metadata_loaded());
    if pre.program.state.journal_metadata_loaded() {
        journal_image_static_domain_unchanged_by_loaded_index_preservation(pre, post, durable_image);
        if pre.program.state.in_flight is Some {
            let frozen_image = pre.program.state.atomic_inflight_superblock_i();
            assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
            journal_image_static_domain_unchanged_by_loaded_index_preservation(pre, post, frozen_image);
        }
    }

    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    let cache_lbl = Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()};
    let cache_step = choose |step: Cache::Step| Cache::State::next_by(
        pre.program.state.cache,
        post.program.state.cache,
        cache_lbl,
        step,
    );
    assert(Cache::State::next_by(
        pre.program.state.cache,
        post.program.state.cache,
        cache_lbl,
        cache_step,
    ));

    assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
        implies {
            &&& journal_image_dirty_cache_disjoint_at(post, durable_image, addr)
            &&& another_atomic_superblock_write_pending(post) ==>
                journal_image_dirty_cache_disjoint_at(
                    post,
                    post.program.state.atomic_inflight_superblock_i(),
                    addr,
                )
        }
    by {
        if filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty {
            match cache_step {
                Cache::Step::load_initiate(new_slots_mapping) => {
                    assert(Cache::State::load_initiate(
                        pre.program.state.cache,
                        post.program.state.cache,
                        cache_lbl,
                        new_slots_mapping,
                    ));
                    let post_slot = post.program.state.cache.lookup_map[addr];
                    assert(cache_filled_addr(post.program.state.cache, addr));
                    assert(post.program.state.cache.entries[post_slot] is Filled);
                    let updated_entries = Map::new(
                        |slot: Slot| new_slots_mapping.contains_key(slot),
                        |slot: Slot| Entry::Loading{addr: new_slots_mapping[slot]},
                    );
                    assert(post.program.state.cache.entries
                        == pre.program.state.cache.entries.union_prefer_right(updated_entries));
                    assert(post.program.state.cache.status_map[post_slot] is Dirty);
                    assert(!new_slots_mapping.contains_key(post_slot)) by {
                        if new_slots_mapping.contains_key(post_slot) {
                            assert(updated_entries.contains_key(post_slot));
                            assert(updated_entries[post_slot] is Loading);
                            assert(post.program.state.cache.entries[post_slot]
                                == updated_entries[post_slot]);
                            assert(false);
                        }
                    }
                    let new_addr_slots = new_slots_mapping.invert();
                    assert(post.program.state.cache.lookup_map
                        == pre.program.state.cache.lookup_map.union_prefer_right(new_addr_slots));
                    assert(!new_addr_slots.contains_key(addr)) by {
                        if new_addr_slots.contains_key(addr) {
                            assert(post.program.state.cache.lookup_map[addr] == new_addr_slots[addr]);
                            assert(post_slot == new_addr_slots[addr]);
                            assert(new_slots_mapping.contains_value(addr));
                            Cache::State::invert_contains_pair(new_slots_mapping, addr);
                            assert(new_slots_mapping.contains_pair(new_addr_slots[addr], addr));
                            assert(new_slots_mapping.contains_key(post_slot));
                            assert(false);
                        }
                    }
                    assert(pre.program.state.cache.lookup_map.contains_key(addr));
                    assert(pre.program.state.cache.lookup_map[addr] == post_slot);
                    assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                    assert(filled_cache_status(pre.program.state.cache)[addr]
                        == CachingDiskPageStatus::Dirty);
                },
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(
                        pre.program.state.cache,
                        post.program.state.cache,
                        cache_lbl,
                    ));
                    let post_slot = post.program.state.cache.lookup_map[addr];
                    assert(post.program.state.cache.lookup_map == pre.program.state.cache.lookup_map);
                    let writeback_slots = Map::new(
                        |req: DiskRequest| req_map.values().contains(req),
                        |req: DiskRequest| pre.program.state.cache.lookup_map[req->to],
                    ).values();
                    assert(!writeback_slots.contains(post_slot)) by {
                        if writeback_slots.contains(post_slot) {
                            let req = choose |req: DiskRequest|
                                req_map.values().contains(req)
                                && pre.program.state.cache.lookup_map[req->to] == post_slot;
                            let updated_status_map = Map::new(
                                |slot: Slot| writeback_slots.contains(slot),
                                |slot: Slot| CacheStatus::Writeback{},
                            );
                            assert(updated_status_map.contains_key(post_slot));
                            assert(post.program.state.cache.status_map
                                == pre.program.state.cache.status_map.union_prefer_right(updated_status_map));
                            assert(post.program.state.cache.status_map[post_slot] is Writeback);
                            assert(false);
                        }
                    }
                    assert(pre.program.state.cache.lookup_map.contains_key(addr));
                    assert(pre.program.state.cache.lookup_map[addr] == post_slot);
                    assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                    assert(filled_cache_status(pre.program.state.cache)[addr]
                        == CachingDiskPageStatus::Dirty);
                },
                _ => {
                    assert(false);
                },
            }
            assert(pre.program.state.journal_metadata_loaded());
            assert(post.program.state.journal_metadata_loaded());
            assert(journal_image_dirty_cache_disjoint_at(pre, durable_image, addr));
            assert(!journal_image_static_domain_i(pre, durable_image).contains(addr));
            assert(!journal_image_static_domain_i(post, durable_image).contains(addr));
            if another_atomic_superblock_write_pending(post) {
                assert(pre.program.state.in_flight is Some);
                assert(another_atomic_superblock_write_pending(pre));
                let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                assert(journal_image_dirty_cache_disjoint_at(pre, frozen_image, addr));
                assert(!journal_image_static_domain_i(pre, frozen_image).contains(addr));
                assert(!journal_image_static_domain_i(post, frozen_image).contains(addr));
            }
        }
    }

    assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
        && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty
        implies post.program.state.journal_metadata_loaded()
    by {
        match cache_step {
            Cache::Step::load_initiate(new_slots_mapping) => {
                assert(Cache::State::load_initiate(
                    pre.program.state.cache,
                    post.program.state.cache,
                    cache_lbl,
                    new_slots_mapping,
                ));
                let post_slot = post.program.state.cache.lookup_map[addr];
                assert(cache_filled_addr(post.program.state.cache, addr));
                assert(post.program.state.cache.entries[post_slot] is Filled);
                let updated_entries = Map::new(
                    |slot: Slot| new_slots_mapping.contains_key(slot),
                    |slot: Slot| Entry::Loading{addr: new_slots_mapping[slot]},
                );
                assert(post.program.state.cache.entries
                    == pre.program.state.cache.entries.union_prefer_right(updated_entries));
                assert(!new_slots_mapping.contains_key(post_slot)) by {
                    if new_slots_mapping.contains_key(post_slot) {
                        assert(updated_entries.contains_key(post_slot));
                        assert(post.program.state.cache.entries[post_slot]
                            == updated_entries[post_slot]);
                        assert(false);
                    }
                }
                let new_addr_slots = new_slots_mapping.invert();
                assert(post.program.state.cache.lookup_map
                    == pre.program.state.cache.lookup_map.union_prefer_right(new_addr_slots));
                assert(!new_addr_slots.contains_key(addr)) by {
                    if new_addr_slots.contains_key(addr) {
                        assert(post.program.state.cache.lookup_map[addr] == new_addr_slots[addr]);
                        assert(post_slot == new_addr_slots[addr]);
                        assert(new_slots_mapping.contains_value(addr));
                        Cache::State::invert_contains_pair(new_slots_mapping, addr);
                        assert(new_slots_mapping.contains_pair(new_addr_slots[addr], addr));
                        assert(new_slots_mapping.contains_key(post_slot));
                        assert(false);
                    }
                }
                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                assert(filled_cache_status(pre.program.state.cache)[addr]
                    == CachingDiskPageStatus::Dirty);
                assert(pre.program.state.journal_metadata_loaded());
            },
            Cache::Step::writeback_initiate() => {
                assert(Cache::State::writeback_initiate(
                    pre.program.state.cache,
                    post.program.state.cache,
                    cache_lbl,
                ));
                let post_slot = post.program.state.cache.lookup_map[addr];
                assert(post.program.state.cache.lookup_map == pre.program.state.cache.lookup_map);
                let writeback_slots = Map::new(
                    |req: DiskRequest| req_map.values().contains(req),
                    |req: DiskRequest| pre.program.state.cache.lookup_map[req->to],
                ).values();
                assert(!writeback_slots.contains(post_slot)) by {
                    if writeback_slots.contains(post_slot) {
                        let updated_status_map = Map::new(
                            |slot: Slot| writeback_slots.contains(slot),
                            |slot: Slot| CacheStatus::Writeback{},
                        );
                        assert(post.program.state.cache.status_map
                            == pre.program.state.cache.status_map.union_prefer_right(updated_status_map));
                        assert(post.program.state.cache.status_map[post_slot] is Writeback);
                        assert(false);
                    }
                }
                assert(pre.program.state.cache.lookup_map.contains_key(addr));
                assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                assert(filled_cache_status(pre.program.state.cache)[addr]
                    == CachingDiskPageStatus::Dirty);
                assert(pre.program.state.journal_metadata_loaded());
            },
            _ => {
                assert(false);
            },
        }
    }

    assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
        && post.disk.requests[id] is WriteReq
        && post.disk.requests[id]->to != spec_superblock_addr()
        implies post.program.state.journal_metadata_loaded()
    by {
        if req_map.contains_key(id) {
            let req = req_map[id];
            assert(post.disk.requests[id] == req);
            match cache_step {
                Cache::Step::writeback_initiate() => {
                    assert(Cache::State::writeback_initiate(
                        pre.program.state.cache,
                        post.program.state.cache,
                        cache_lbl,
                    ));
                    assert(pre.program.state.cache.valid_writeback_requests(req_map.values()));
                    assert(req_map.values().contains(req));
                    let slot = pre.program.state.cache.lookup_map[req->to];
                    pre.program.state.cache.build_lookup_map_ensures();
                    assert(pre.program.state.cache.build_lookup_map_props(pre.program.state.cache.lookup_map));
                    assert(pre.program.state.cache.entries.contains_key(slot));
                    assert(pre.program.state.cache.entries[slot]
                        == Entry::Filled{addr: req->to, data: req->data});
                    assert(pre.program.state.cache.status_map[slot] is Dirty);
                    assert(cache_filled_addr(pre.program.state.cache, req->to));
                    assert(pre.program.state.cache.status_map.contains_key(slot));
                    assert(filled_cache_status(pre.program.state.cache).contains_key(req->to));
                    assert(filled_cache_status(pre.program.state.cache)[req->to]
                        == CachingDiskPageStatus::Dirty);
                    assert(pre.program.state.journal_metadata_loaded());
                },
                Cache::Step::load_initiate(new_slots_mapping) => {
                    assert(Cache::State::load_initiate(
                        pre.program.state.cache,
                        post.program.state.cache,
                        cache_lbl,
                        new_slots_mapping,
                    ));
                    assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                    assert(req_map.values().contains(req));
                    assert(req is ReadReq);
                    assert(false);
                },
                _ => {
                    assert(false);
                },
            }
        } else {
            assert(pre.disk.requests.contains_key(id));
            assert(post.disk.requests[id] == pre.disk.requests[id]);
            assert(pre.program.state.journal_metadata_loaded());
        }
    }

    assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
        implies {
            &&& journal_image_request_writeback_disjoint_at(post, durable_image, id)
            &&& another_atomic_superblock_write_pending(post) ==>
                journal_image_request_writeback_disjoint_at(
                    post,
                    post.program.state.atomic_inflight_superblock_i(),
                    id,
                )
        }
    by {
        if post.disk.requests[id] is WriteReq && post.disk.requests[id]->to != spec_superblock_addr() {
            if req_map.contains_key(id) {
                let req = req_map[id];
                assert(post.disk.requests[id] == req);
                assert(req is WriteReq);
                match cache_step {
                    Cache::Step::writeback_initiate() => {
                        assert(Cache::State::writeback_initiate(
                            pre.program.state.cache,
                            post.program.state.cache,
                            cache_lbl,
                        ));
                        assert(pre.program.state.cache.valid_writeback_requests(req_map.values()));
                        assert(req_map.values().contains(req));
                        assert(pre.program.state.cache.lookup_map.contains_key(req->to));
                        let slot = pre.program.state.cache.lookup_map[req->to];
                        pre.program.state.cache.build_lookup_map_ensures();
                        assert(pre.program.state.cache.build_lookup_map_props(pre.program.state.cache.lookup_map));
                        assert(pre.program.state.cache.entries.contains_key(slot));
                        assert(pre.program.state.cache.entries[slot]
                            == Entry::Filled{addr: req->to, data: req->data});
                        assert(pre.program.state.cache.status_map[slot] is Dirty);
                        assert(cache_filled_addr(pre.program.state.cache, req->to));
                        assert(pre.program.state.cache.status_map.contains_key(slot));
                        assert(filled_cache_status(pre.program.state.cache).contains_key(req->to));
                        assert(filled_cache_status(pre.program.state.cache)[req->to]
                            == CachingDiskPageStatus::Dirty);
                        assert(pre.program.state.journal_metadata_loaded());
                        assert(post.program.state.journal_metadata_loaded());
                    },
                    Cache::Step::load_initiate(new_slots_mapping) => {
                        assert(Cache::State::load_initiate(
                            pre.program.state.cache,
                            post.program.state.cache,
                            cache_lbl,
                            new_slots_mapping,
                        ));
                        assert(Cache::State::valid_load_requests(req_map.values(), new_slots_mapping));
                        assert(req_map.values().contains(req));
                        assert(req is ReadReq);
                        assert(false);
                    },
                    _ => {
                        assert(false);
                    },
                }
                assert(post.program.state.journal_metadata_loaded());
                assert(journal_image_dirty_cache_disjoint_at(pre, durable_image, req->to));
                assert(!journal_image_static_domain_i(pre, durable_image).contains(req->to));
                assert(!journal_image_static_domain_i(post, durable_image).contains(req->to));
                if another_atomic_superblock_write_pending(post) {
                    assert(pre.program.state.in_flight is Some);
                    assert(another_atomic_superblock_write_pending(pre));
                    let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                    assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                    assert(journal_image_dirty_cache_disjoint_at(pre, frozen_image, req->to));
                    assert(!journal_image_static_domain_i(pre, frozen_image).contains(req->to));
                    assert(!journal_image_static_domain_i(post, frozen_image).contains(req->to));
                }
            } else {
                assert(pre.disk.requests.contains_key(id));
                assert(post.disk.requests[id] == pre.disk.requests[id]);
                assert(pre.program.state.journal_metadata_loaded());
                assert(post.program.state.journal_metadata_loaded());
                assert(journal_image_request_writeback_disjoint_at(pre, durable_image, id));
                assert(!journal_image_static_domain_i(pre, durable_image).contains(post.disk.requests[id]->to));
                assert(!journal_image_static_domain_i(post, durable_image).contains(post.disk.requests[id]->to));
                if another_atomic_superblock_write_pending(post) {
                    assert(pre.program.state.in_flight is Some);
                    assert(another_atomic_superblock_write_pending(pre));
                    let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                    assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                    assert(journal_image_request_writeback_disjoint_at(pre, frozen_image, id));
                    assert(!journal_image_static_domain_i(pre, frozen_image).contains(post.disk.requests[id]->to));
                    assert(!journal_image_static_domain_i(post, frozen_image).contains(post.disk.requests[id]->to));
                }
            }
        }
    }
    assert(journal_allocable_addrs_image_disjoint(post)) by {
        assert forall |addr: Address| #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
            implies {
                &&& !journal_image_static_domain_i(post, durable_image).contains(addr)
                &&& post.program.state.in_flight is Some ==>
                    !journal_image_static_domain_i(
                        post,
                        post.program.state.atomic_inflight_superblock_i(),
                    ).contains(addr)
            } by {
            assert(pre.program.state.journal.mini_allocator.can_allocate(addr));
            assert(journal_allocable_addrs_image_disjoint(pre));
            assert(!journal_image_static_domain_i(pre, durable_image).contains(addr));
            assert(!journal_image_static_domain_i(post, durable_image).contains(addr));
            if post.program.state.in_flight is Some {
                assert(pre.program.state.in_flight is Some);
                let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                assert(post.program.state.atomic_inflight_superblock_i() == frozen_image);
                assert(!journal_image_static_domain_i(pre, frozen_image).contains(addr));
                assert(!journal_image_static_domain_i(post, frozen_image).contains(addr));
            }
        }
    }
}

pub proof fn journal_image_writeback_disjoint_preserved_by_read_only_cache_access(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    reads: Map<Address, RawPage>,
)
    requires
        journal_image_writeback_disjoint(pre),
        Cache::State::next(
            pre.program.state.cache,
            post.program.state.cache,
            Cache::Label::Access{reads, writes: Map::empty()},
        ),
        post.disk == pre.disk,
        post.program.state.journal == pre.program.state.journal,
        post.program.state.in_flight == pre.program.state.in_flight,
        post.program.state.journal.in_flight == pre.program.state.journal.in_flight,
        post.program.state.branch.in_flight == pre.program.state.branch.in_flight,
    ensures
        journal_image_writeback_disjoint(post),
{
    reveal(Cache::State::next);
    reveal(Cache::State::next_by);
    assert(Cache::State::next_by(
        pre.program.state.cache,
        post.program.state.cache,
        Cache::Label::Access{reads, writes: Map::empty()},
        Cache::Step::access(),
    ));
    assert(post.program.state.cache.lookup_map == pre.program.state.cache.lookup_map);
    assert(post.program.state.cache.entries == pre.program.state.cache.entries);
    assert(post.program.state.cache.status_map == pre.program.state.cache.status_map);
    assert(filled_cache_status(post.program.state.cache)
        =~= filled_cache_status(pre.program.state.cache)) by {
        assert_maps_equal!(
            filled_cache_status(post.program.state.cache),
            filled_cache_status(pre.program.state.cache),
            addr => { }
        );
    }
    assert(durable_superblock_image_i(post) == durable_superblock_image_i(pre));
    if pre.program.state.in_flight is Some {
        assert(post.program.state.atomic_inflight_superblock_i()
            == pre.program.state.atomic_inflight_superblock_i());
    }
    assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
        && post.disk.requests[id] is WriteReq
        && post.disk.requests[id]->to != spec_superblock_addr()
        implies post.program.state.journal_metadata_loaded()
    by {
        assert(pre.disk.requests.contains_key(id));
        assert(post.disk.requests[id] == pre.disk.requests[id]);
        assert(pre.program.state.journal_metadata_loaded());
    }
    assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
        && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty
        implies post.program.state.journal_metadata_loaded()
    by {
        assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
        assert(filled_cache_status(pre.program.state.cache)[addr] == CachingDiskPageStatus::Dirty);
        assert(pre.program.state.journal_metadata_loaded());
    }
    assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
        implies {
            &&& journal_image_dirty_cache_disjoint_at(post, durable_superblock_image_i(post), addr)
            &&& another_atomic_superblock_write_pending(post) ==>
                journal_image_dirty_cache_disjoint_at(
                    post,
                    post.program.state.atomic_inflight_superblock_i(),
                    addr,
                )
        }
    by {
        assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
        assert(filled_cache_status(post.program.state.cache)[addr]
            == filled_cache_status(pre.program.state.cache)[addr]);
        assert(journal_image_static_domain_i(post, durable_superblock_image_i(post))
            =~= journal_image_static_domain_i(pre, durable_superblock_image_i(pre)));
        if another_atomic_superblock_write_pending(post) {
            assert(pre.program.state.in_flight is Some);
            assert(another_atomic_superblock_write_pending(pre));
            assert(journal_image_static_domain_i(post, post.program.state.atomic_inflight_superblock_i())
                =~= journal_image_static_domain_i(pre, pre.program.state.atomic_inflight_superblock_i()));
        }
    }
    assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
        implies {
            &&& journal_image_request_writeback_disjoint_at(post, durable_superblock_image_i(post), id)
            &&& another_atomic_superblock_write_pending(post) ==>
                journal_image_request_writeback_disjoint_at(
                    post,
                    post.program.state.atomic_inflight_superblock_i(),
                    id,
                )
        }
    by {
        assert(pre.disk.requests.contains_key(id));
        assert(post.disk.requests[id] == pre.disk.requests[id]);
        if post.disk.requests[id] is WriteReq && post.disk.requests[id]->to != spec_superblock_addr() {
            assert(journal_image_request_writeback_disjoint_at(pre, durable_superblock_image_i(pre), id));
            if another_atomic_superblock_write_pending(post) {
                assert(pre.program.state.in_flight is Some);
                assert(another_atomic_superblock_write_pending(pre));
                assert(journal_image_request_writeback_disjoint_at(
                    pre,
                    pre.program.state.atomic_inflight_superblock_i(),
                    id,
                ));
            }
        }
    }
    assert(journal_allocable_addrs_image_disjoint(post)) by {
        assert forall |addr: Address| #[trigger] post.program.state.journal.mini_allocator.can_allocate(addr)
            implies {
                &&& !journal_image_static_domain_i(post, durable_superblock_image_i(post)).contains(addr)
                &&& post.program.state.in_flight is Some ==>
                    !journal_image_static_domain_i(
                        post,
                        post.program.state.atomic_inflight_superblock_i(),
                    ).contains(addr)
            } by {
            assert(pre.program.state.journal.mini_allocator.can_allocate(addr));
            assert(journal_allocable_addrs_image_disjoint(pre));
            assert(!journal_image_static_domain_i(pre, durable_superblock_image_i(pre)).contains(addr));
            assert(!journal_image_static_domain_i(post, durable_superblock_image_i(post)).contains(addr));
            if post.program.state.in_flight is Some {
                assert(pre.program.state.in_flight is Some);
                assert(!journal_image_static_domain_i(
                    pre,
                    pre.program.state.atomic_inflight_superblock_i(),
                ).contains(addr));
                assert(!journal_image_static_domain_i(
                    post,
                    post.program.state.atomic_inflight_superblock_i(),
                ).contains(addr));
            }
        }
    }
}

pub proof fn journal_image_static_domain_subset_journal_projection(
    model: SystemModel::State<AnotherProgramModel>,
    image: AbstractSuperblockImage,
)
    requires
        model.program.state.journal_metadata_loaded(),
        journal_projection_uses_live(model),
        journal_image_i(model, image).valid_image(),
        journal_image_i(model, image).persistent.dom()
            <= addresses_in_aus(journal_projection_aus(model)),
    ensures
        journal_image_static_domain_i(model, image) <= addresses_in_aus(journal_projection_aus(model)),
{
    let cimage = journal_image_i(model, image);
    cimage.valid_image_stable_domain_materialized();
    let full_records = to_journal_records(model.disk.content);
    let static_domain = journal_image_static_domain_i(model, image);
    let restricted_raw = model.disk.content.restrict(static_domain);
    assert(cimage.persistent == restricted_raw);
    to_journal_records_restrict(model.disk.content, static_domain);
    assert(to_journal_records(cimage.persistent) =~= full_records.restrict(static_domain));
    snapshot_walk_domain_restrict_domain_same(
        full_records,
        image.journal_snapshot.boundary_lsn,
        image.journal_snapshot.freshest_rec(),
    );
    assert(cimage.stable_persistent_domain() =~= static_domain) by {
        assert(cimage.stable_persistent_domain() =~= snapshot_walk_domain(
            full_records.restrict(static_domain),
            image.journal_snapshot.boundary_lsn,
            image.journal_snapshot.freshest_rec(),
        ));
        assert(snapshot_walk_domain(
            full_records.restrict(static_domain),
            image.journal_snapshot.boundary_lsn,
            image.journal_snapshot.freshest_rec(),
        ) =~= static_domain);
    }
    assert forall |addr: Address| #[trigger] journal_image_static_domain_i(model, image).contains(addr)
        implies addresses_in_aus(journal_projection_aus(model)).contains(addr)
    by {
        assert(journal_image_static_domain_i(model, image) =~= cimage.stable_persistent_domain());
        assert(cimage.stable_persistent_domain().contains(addr));
        assert(cimage.persistent.dom().contains(addr));
        assert(cimage.persistent.contains_key(addr));
    }
}

pub proof fn another_atomic_disk_refinement_invariants_next(
    pre: SystemModel::State<AnotherProgramModel>,
    post: SystemModel::State<AnotherProgramModel>,
    lbl: SystemModel::Label,
)
    requires
        another_atomic_disk_refinement_invariants(pre),
        SystemModel::State::next(pre, post, lbl),
    ensures
        another_atomic_disk_refinement_invariants(post),
{
    reveal(SystemModel::State::next);
    reveal(SystemModel::State::next_by);
    let step = choose |step| SystemModel::State::next_by(pre, post, lbl, step);
    match step {
        SystemModel::Step::accept_request() => {
            assert(post.program == pre.program);
            assert(post.disk == pre.disk);
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::deliver_reply() => {
            assert(post.program == pre.program);
            assert(post.disk == pre.disk);
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::program_execute(new_program) => {
            assert(exists |event: ProgramEvent| AnotherAtomicState::execute_transition(
                pre.program.state,
                post.program.state,
                lbl->op->req,
                lbl->op->reply,
                event,
            ));
            let event = choose |event: ProgramEvent| AnotherAtomicState::execute_transition(
                pre.program.state,
                post.program.state,
                lbl->op->req,
                lbl->op->reply,
                event,
            );
            assert(AnotherAtomicState::execute_transition(
                pre.program.state,
                post.program.state,
                lbl->op->req,
                lbl->op->reply,
                event,
            ));
            match event {
                ProgramEvent::NoOp{} => {
                    assert(AnotherAtomicState::execute_noop(
                        pre.program.state,
                        post.program.state,
                        lbl->op->req,
                        lbl->op->reply,
                    ));
                    assert(post.program.state == pre.program.state);
                    assert(post.program.state.wf());
                },
                ProgramEvent::Put{receipt, init_root, reads, writes, branch} => {
                    assert(AnotherAtomicState::execute_put(
                        pre.program.state,
                        post.program.state,
                        lbl->op->req,
                        lbl->op->reply,
                        receipt,
                        init_root,
                        reads,
                        writes,
                        branch,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes},
                    );
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes},
                        Cache::Step::access(),
                    ));
                    assert(post.program.state.cache.lookup_map == pre.program.state.cache.lookup_map);
                    let key = lbl->op->req.input.arrow_PutInput_key();
                    let value = lbl->op->req.input.arrow_PutInput_value();
                    let msg = Message::Define{value};
                    let keyed_message = KeyedMessage{key, message: msg};
                    let records = MsgHistory::singleton_at(pre.program.state.branch.seq_end(), keyed_message);
                    let branch_lbl = AtomicBranchState::Label::Append{
                        keys: seq![key],
                        msgs: seq![msg],
                        receipt,
                        init_root,
                        read_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads),
                        write_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes),
                    };
                    AnotherAtomicState::execute_put_journal_effect(
                        pre.program.state,
                        post.program.state,
                        lbl->op->req,
                        lbl->op->reply,
                        receipt,
                        init_root,
                        reads,
                        writes,
                        branch,
                    );
                    CachedJournal::State::put_effect(
                        pre.program.state.journal.journal,
                        post.program.state.journal.journal,
                        records,
                    );
                    AtomicJournalState::State::wf_next(
                        pre.program.state.journal,
                        post.program.state.journal,
                        AtomicJournalState::Label::Put{messages: records},
                    );
                    AtomicBranchState::State::wf_next(
                        pre.program.state.branch,
                        post.program.state.branch,
                        branch_lbl,
                    );
                    AtomicBranchState::State::append_preserves_owned_aus(
                        pre.program.state.branch,
                        post.program.state.branch,
                        branch_lbl,
                    );
                    AtomicBranchState::State::append_effect(
                        pre.program.state.branch,
                        post.program.state.branch,
                        branch_lbl,
                    );
                    assert(to_aus(writes.dom()) <= pre.program.state.branch_owned_aus()) by {
                        assert(writes.dom() =~= crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes).dom());
                        reveal(AtomicBranchState::State::next);
                        reveal(AtomicBranchState::State::next_by);
                        let step = choose |step: AtomicBranchState::Step|
                            AtomicBranchState::State::next_by(
                                pre.program.state.branch,
                                post.program.state.branch,
                                branch_lbl,
                                step,
                            );
                        match step {
                            AtomicBranchState::Step::append(new_active_branch) => {
                                assert(AtomicBranchState::State::append(
                                    pre.program.state.branch,
                                    post.program.state.branch,
                                    branch_lbl,
                                    new_active_branch,
                                )) by {
                                    reveal(AtomicBranchState::State::append);
                                }
                                assert(to_aus(crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes).dom())
                                    <= pre.program.state.branch.owned_aus());
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    }
                    assert(post.program.state.journal.owned_aus() == pre.program.state.journal.owned_aus());
                    assert(post.program.state.branch.owned_aus() == pre.program.state.branch.owned_aus());
                    assert(post.program.state.component_owned_aus() == pre.program.state.component_owned_aus());
                    assert(post.program.state.recovery_state == pre.program.state.recovery_state);
                    assert(post.program.state.journal_metadata_loaded());
                    assert(post.program.state.branch_metadata_loaded());
                    assert(post.program.state.branch.seq_end()
                        == pre.program.state.branch.seq_end() + 1);
                    assert(records.seq_end == pre.program.state.branch.seq_end() + 1);
                    assert(post.program.state.journal.journal.seq_end() == records.seq_end);
                    assert(post.program.state.journal.journal.seq_end()
                        == post.program.state.branch.seq_end());
                    assert(post.program.state.cache.inv());
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        reads,
                        writes,
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        reads,
                        writes,
                    );
                    branch_writes_disjoint_from_journal_projection(pre, writes);
                    let durable_image = durable_superblock_image_i(pre);
                    journal_image_static_domain_subset_journal_projection(pre, durable_image);
                    assert(writes.dom().disjoint(journal_image_static_domain_i(pre, durable_image))) by {
                        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                            implies !journal_image_static_domain_i(pre, durable_image).contains(addr) by {
                            if journal_image_static_domain_i(pre, durable_image).contains(addr) {
                                assert(addresses_in_aus(journal_projection_aus(pre)).contains(addr));
                                assert(false);
                            }
                        }
                    }
                    if another_atomic_superblock_write_pending(pre) {
                        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                        journal_image_static_domain_subset_journal_projection(pre, frozen_image);
                        assert(writes.dom().disjoint(journal_image_static_domain_i(pre, frozen_image))) by {
                            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                implies !journal_image_static_domain_i(pre, frozen_image).contains(addr) by {
                                if journal_image_static_domain_i(pre, frozen_image).contains(addr) {
                                    assert(addresses_in_aus(journal_projection_aus(pre)).contains(addr));
                                    assert(false);
                                }
                            }
                        }
                    }
                    assert(atomic_branch_metadata_loaded_flag(pre.program.state.branch));
                    assert(branch_projection_aus(post) =~= branch_projection_aus(pre));
                    assert(writes.dom() <= addresses_in_aus(branch_projection_aus(pre))) by {
                        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                            implies addresses_in_aus(branch_projection_aus(pre)).contains(addr) by {
                            assert(to_aus(writes.dom()).contains(addr.au));
                            assert(pre.program.state.branch_owned_aus().contains(addr.au));
                            assert(branch_projection_aus(pre).contains(addr.au));
                        }
                    }
                    assert(reads <= branch_disk_cache_i(pre));
                    program_execute_put_dispatches_components(
                        pre,
                        post,
                        lbl->op->req,
                        lbl->op->reply,
                        receipt,
                        init_root,
                        reads,
                        writes,
                        branch,
                    );
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(post.program.state.cache_request_wf());
                    assert(post.program.state.journal.wf());
                    assert(post.program.state.branch.wf());
                    assert(post.program.state.allocation_wf());
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.in_flight_agrees());
                    assert(post.program.state.wf());
                    assert(crash_aware_caching_disk_journal_i(post).inv());
                    assert(crash_aware_caching_disk_branch_i(post).inv());
                    assert(journal_component_refinement_inv(post));
                    assert(branch_component_refinement_inv(post));
                },
                ProgramEvent::Query{end_lsn, key, value, msg, receipts, reads} => {
                    assert(AnotherAtomicState::execute_query(
                        pre.program.state,
                        post.program.state,
                        lbl->op->req,
                        lbl->op->reply,
                        end_lsn,
                        key,
                        value,
                        msg,
                        receipts,
                        reads,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes: Map::empty()},
                    );
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes: Map::empty()},
                        Cache::Step::access(),
                    ));
                    assert(post.program.state.cache.lookup_map == pre.program.state.cache.lookup_map);
                    assert(post.program.state.branch == pre.program.state.branch);
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        reads,
                        Map::empty(),
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        reads,
                        Map::empty(),
                    );
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        Map::empty(),
                    );
                    assert(atomic_branch_metadata_loaded_flag(pre.program.state.branch));
                    assert(branch_projection_aus(post) =~= branch_projection_aus(pre));
                    assert(reads <= branch_disk_cache_i(pre));
                    program_execute_query_dispatches_components(
                        pre,
                        post,
                        lbl->op->req,
                        lbl->op->reply,
                        end_lsn,
                        key,
                        value,
                        msg,
                        receipts,
                        reads,
                    );
                    assert(post.program.state.wf());
                    assert(crash_aware_caching_disk_journal_i(post).inv());
                    assert(crash_aware_caching_disk_branch_i(post).inv());
                    assert(journal_component_refinement_inv(post));
                    assert(branch_component_refinement_inv(post));
                },
            }
            assert(post.program.state.wf());
            assert(post.disk == pre.disk);
            assert(post.disk.inv());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(another_atomic_model_refinement_invariants(post.program.state));
            assert(another_atomic_cache_disk_coupling(post.program.state, post.disk));
            assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
            assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
            assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
            assert(journal_component_refinement_inv(post));
            assert(branch_component_refinement_inv(post));
            assert(journal_image_writeback_disjoint(post));
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::accept_sync_request() => {
            assert(post.program == pre.program);
            assert(post.disk == pre.disk);
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::program_accept_sync_request(new_program) => {
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::program_deliver_sync_reply(new_program) => {
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::deliver_sync_reply() => {
            assert(post.program == pre.program);
            assert(post.disk == pre.disk);
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::program_disk(new_program, new_disk) => {
            async_disk_inv_next(pre.disk, post.disk, DiskLabel::DiskOps{
                requests: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.reqs),
                responses: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.resps),
            });
            assert(exists |disk_event: DiskEvent| AnotherAtomicState::disk_transition(
                pre.program.state,
                post.program.state,
                disk_event,
                lbl->info.reqs,
                lbl->info.resps,
            ));
            let disk_event = choose |disk_event: DiskEvent| AnotherAtomicState::disk_transition(
                pre.program.state,
                post.program.state,
                disk_event,
                lbl->info.reqs,
                lbl->info.resps,
            );
            assert(AnotherAtomicState::disk_transition(
                pre.program.state,
                post.program.state,
                disk_event,
                lbl->info.reqs,
                lbl->info.resps,
            ));
            match disk_event {
                DiskEvent::InitiateRecovery{req_id} => {
                    assert(AnotherAtomicState::initiate_recovery(
                        pre.program.state,
                        post.program.state,
                        lbl->info.reqs,
                        lbl->info.resps,
                        req_id,
                    ));
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(post.program.state.outstanding_cache_reqs
                        == pre.program.state.outstanding_cache_reqs);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    assert(post.program.state.wf());
                },
                DiskEvent::SuperblockRecovery{req_id, raw_page, image} => {
                    assert(AnotherAtomicState::superblock_recovery(
                        pre.program.state,
                        post.program.state,
                        lbl->info.reqs,
                        lbl->info.resps,
                        req_id,
                        raw_page,
                        image,
                    ));
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(post.program.state.outstanding_cache_reqs
                        == pre.program.state.outstanding_cache_reqs);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    assert(post.program.state.cache_request_wf());
                    assert(post.program.state.journal.wf());
                    let branch_image = crate::implementation::AnotherAtomicState_v::AtomicBranchImage{
                        sealed_roots: image.branch_roots,
                        seq_end: image.branch_seq_end,
                    };
                    assert(post.program.state.branch.image == branch_image);
                    assert(post.program.state.branch.persistent_image == branch_image);
                    assert(post.program.state.branch.persisted_root_count
                        == image.branch_roots.len());
                    assert(post.program.state.branch.image.sealed_roots.take(
                        post.program.state.branch.persistent_image.sealed_roots.len() as int,
                    ) == post.program.state.branch.persistent_image.sealed_roots);
                    assert(post.program.state.branch.wf());
                    assert(post.program.state.journal.loaded_index_aus() == Set::<AU>::empty());
                    assert(post.program.state.journal.mini_allocator.all_aus() == Set::<AU>::empty());
                    assert(post.program.state.journal_owned_aus() == Set::<AU>::empty());
                    assert(post.program.state.branch.branch_summary == Map::<AU, Set<AU>>::empty());
                    assert(post.program.state.branch.branch_summary.values()
                        =~= Set::<Set<AU>>::empty()) by {
                        assert forall |s: Set<AU>| #[trigger] post.program.state.branch.branch_summary.values().contains(s)
                            implies false
                        by {
                            let au = choose |au: AU|
                                post.program.state.branch.branch_summary.contains_key(au)
                                && post.program.state.branch.branch_summary[au] == s;
                            assert(post.program.state.branch.branch_summary.contains_key(au));
                            assert(false);
                        }
                    }
                    assert(summary_aus(post.program.state.branch.branch_summary)
                        == Set::<AU>::empty()) by {
                        reveal(union_set_of_sets);
                    }
                    assert(post.program.state.branch.mini_allocator.all_aus() == Set::<AU>::empty());
                    assert(post.program.state.branch_owned_aus() == Set::<AU>::empty());
                    assert(post.program.state.component_owned_aus()
                        == AnotherAtomicState::reserved_aus());
                    assert(post.program.state.allocation_wf());
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.wf());
                },
                DiskEvent::ExecuteSyncBegin{req_id, image, journal_reads} => {
                    assert(AnotherAtomicState::execute_sync_begin(
                        pre.program.state,
                        post.program.state,
                        req_id,
                        lbl->info.reqs,
                        lbl->info.resps,
                        image,
                        journal_reads,
                    ));
                    assert(lbl->info.reqs.is_empty());
                    assert(lbl->info.resps.is_empty());
                    assert(post.disk == pre.disk) by {
                        reveal(AsyncDisk::State::next);
                        reveal(AsyncDisk::State::next_by);
                        assert(AsyncDisk::State::next_by(
                            pre.disk,
                            post.disk,
                            DiskLabel::DiskOps{
                                requests: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.reqs),
                                responses: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.resps),
                            },
                            AsyncDisk::Step::disk_ops(),
                        ));
                    }
                    assert(post.program.state.outstanding_cache_reqs
                        == pre.program.state.outstanding_cache_reqs);
                    assert(Cache::State::next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads: journal_reads, writes: Map::empty()},
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads: journal_reads, writes: Map::empty()},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        journal_reads,
                        Map::empty(),
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        journal_reads,
                        Map::empty(),
                    );
                    AtomicJournalState::State::wf_next(
                        pre.program.state.journal,
                        post.program.state.journal,
                        AtomicJournalState::Label::CommitStart{
                            snapshot: image.journal_snapshot,
                            seq_end: image.journal_seq_end,
                            reads: to_journal_records(journal_reads),
                        },
                    );
                    AtomicJournalState::State::commit_start_effect(
                        pre.program.state.journal,
                        post.program.state.journal,
                        AtomicJournalState::Label::CommitStart{
                            snapshot: image.journal_snapshot,
                            seq_end: image.journal_seq_end,
                            reads: to_journal_records(journal_reads),
                        },
                    );
                    AtomicBranchState::State::wf_next(
                        pre.program.state.branch,
                        post.program.state.branch,
                        AtomicBranchState::Label::CommitStart{
                            branch_image: crate::implementation::AnotherAtomicState_v::AtomicBranchImage{
                                sealed_roots: image.branch_roots,
                                seq_end: image.branch_seq_end,
                            },
                        },
                    );
                    AtomicBranchState::State::commit_start_effect(
                        pre.program.state.branch,
                        post.program.state.branch,
                        AtomicBranchState::Label::CommitStart{
                            branch_image: crate::implementation::AnotherAtomicState_v::AtomicBranchImage{
                                sealed_roots: image.branch_roots,
                                seq_end: image.branch_seq_end,
                            },
                        },
                    );
                    assert(post.program.state.cache.inv());
                    assert(post.program.state.journal.wf());
                    assert(post.program.state.branch.wf());
                    assert(post.program.state.allocation_wf());
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.in_flight is Some);
                    assert(post.program.state.journal.in_flight == Some(crate::implementation::AnotherAtomicState_v::AtomicJournalImage{
                        snapshot: image.journal_snapshot,
                        seq_end: image.journal_seq_end,
                    }));
                    assert(post.program.state.branch.in_flight == Some(crate::implementation::AnotherAtomicState_v::AtomicBranchImage{
                        sealed_roots: image.branch_roots,
                        seq_end: image.branch_seq_end,
                    }));
                    assert(post.program.state.in_flight.unwrap().boundary_lsn == image.branch_seq_end);
                    assert(post.program.state.atomic_inflight_superblock_i() == image);
                    assert(post.program.state.in_flight_agrees());
                    assert(post.program.state.in_flight.unwrap().wf());
                    assert(post.program.state.wf());
                },
                DiskEvent::ExecuteSyncPrepared{req} => {
                    assert(AnotherAtomicState::execute_sync_prepared(
                        pre.program.state,
                        post.program.state,
                        req,
                        lbl->info.reqs,
                        lbl->info.resps,
                    ));
                    assert(post.program.state == pre.program.state);
                    assert(post.program.state.wf());
                },
                DiskEvent::ExecuteSyncEnd{journal_discarded_aus} => {
                    assert(AnotherAtomicState::execute_sync_end(
                        pre.program.state,
                        post.program.state,
                        lbl->info.reqs,
                        lbl->info.resps,
                        journal_discarded_aus,
                    ));
                    assert(post.program.state.cache == pre.program.state.cache);
                    assert(post.program.state.outstanding_cache_reqs
                        == pre.program.state.outstanding_cache_reqs);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    assert(post.program.state.cache_request_wf());
                    AtomicBranchState::State::wf_next(
                        pre.program.state.branch,
                        post.program.state.branch,
                        AtomicBranchState::Label::CommitComplete,
                    );
                    AtomicBranchState::State::commit_complete_effect(
                        pre.program.state.branch,
                        post.program.state.branch,
                        AtomicBranchState::Label::CommitComplete,
                    );
                    AtomicJournalState::State::wf_next(
                        pre.program.state.journal,
                        post.program.state.journal,
                        AtomicJournalState::Label::CommitComplete{
                            require_end: pre.program.state.journal.journal.seq_end(),
                            discarded_aus: journal_discarded_aus,
                        },
                    );
                    AtomicJournalState::State::commit_complete_effect(
                        pre.program.state.journal,
                        post.program.state.journal,
                        AtomicJournalState::Label::CommitComplete{
                            require_end: pre.program.state.journal.journal.seq_end(),
                            discarded_aus: journal_discarded_aus,
                        },
                    );
                    AnotherAtomicState::execute_sync_end_journal_effect(
                        pre.program.state,
                        post.program.state,
                        lbl->info.reqs,
                        lbl->info.resps,
                        journal_discarded_aus,
                    );
                    assert(post.program.state.journal.wf());
                    assert(post.program.state.branch.wf());
                    assert(post.program.state.recovery_state == pre.program.state.recovery_state);
                    assert(post.program.state.persistent_image is Some);
                    assert(post.program.state.journal_metadata_loaded());
                    assert(post.program.state.branch_metadata_loaded());
                    assert(post.program.state.branch.seq_end() == pre.program.state.branch.seq_end());
                    assert(post.program.state.journal.journal.seq_end()
                        == pre.program.state.journal.journal.seq_end());
                    assert(post.program.state.journal.journal.seq_end()
                        == post.program.state.branch.seq_end());
                    assert(post.program.state.recovery_metadata_wf());
                    assert(post.program.state.branch_owned_aus()
                        == pre.program.state.branch_owned_aus());
                    assert(post.program.state.journal_owned_aus()
                        <= pre.program.state.journal_owned_aus());
                    assert(journal_discarded_aus <= pre.program.state.journal_owned_aus());
                    assert(post.program.state.journal_owned_aus().disjoint(journal_discarded_aus));
                    assert(post.program.state.free_aus
                        == pre.program.state.free_aus + journal_discarded_aus);
                    assert(post.program.state.component_disjoint()) by {
                        assert(AnotherAtomicState::reserved_aus().disjoint(
                            post.program.state.journal_owned_aus(),
                        ));
                        assert(AnotherAtomicState::reserved_aus().disjoint(
                            post.program.state.branch_owned_aus(),
                        ));
                        assert(post.program.state.journal_owned_aus().disjoint(
                            post.program.state.branch_owned_aus(),
                        ));
                    }
                    assert(post.program.state.free_aus.disjoint(
                        post.program.state.component_owned_aus(),
                    )) by {
                        assert forall |au: AU| #[trigger] post.program.state.free_aus.contains(au)
                            implies !post.program.state.component_owned_aus().contains(au)
                        by {
                            if pre.program.state.free_aus.contains(au) {
                                assert(!pre.program.state.component_owned_aus().contains(au));
                                assert(!post.program.state.component_owned_aus().contains(au));
                            } else {
                                assert(journal_discarded_aus.contains(au));
                                assert(!post.program.state.journal_owned_aus().contains(au));
                                assert(!post.program.state.branch_owned_aus().contains(au));
                                assert(!AnotherAtomicState::reserved_aus().contains(au));
                                assert(!post.program.state.component_owned_aus().contains(au));
                            }
                        }
                    }
                    assert(post.program.state.allocation_wf());
                    assert(post.program.state.wf());
                },
                DiskEvent::CacheIOBegin{req_map} => {
                    assert(AnotherAtomicState::cache_io_begin(
                        pre.program.state,
                        post.program.state,
                        req_map,
                        lbl->info.reqs,
                        lbl->info.resps,
                    ));
                    let disk_req_map = crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.reqs);
                    assert(disk_req_map == req_map);
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::DiskOps{requests: req_map.values(), responses: Map::empty()},
                    );
                    AnotherAtomicState::cache_io_begin_preserves_cache_request_wf(
                        pre.program.state,
                        post.program.state,
                        req_map,
                        lbl->info.reqs,
                        lbl->info.resps,
                    );
                    assert(another_atomic_cache_disk_coupling(post.program.state, post.disk)) by {
                        let updated = Map::new(|id| req_map.contains_key(id), |id| req_map[id].addr());
                        assert(post.program.state.outstanding_cache_reqs
                            == pre.program.state.outstanding_cache_reqs.union_prefer_right(updated));
                        reveal(AsyncDisk::State::next);
                        reveal(AsyncDisk::State::next_by);
                        assert(AsyncDisk::State::next_by(
                            pre.disk,
                            post.disk,
                            DiskLabel::DiskOps{
                                requests: disk_req_map,
                                responses: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.resps),
                            },
                            AsyncDisk::Step::disk_ops(),
                        ));
                        assert(lbl->info.resps.is_empty());
                        assert(post.disk.requests == pre.disk.requests.union_prefer_right(req_map));
                        assert(post.disk.responses == pre.disk.responses);
                        assert forall |id: ID| #[trigger] post.program.state.outstanding_cache_reqs.contains_key(id)
                            implies disk_has_pending_id(post.disk, id) by {
                            if updated.contains_key(id) {
                                assert(req_map.contains_key(id));
                                assert(post.disk.requests.contains_key(id));
                            } else {
                                assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
                                assert(disk_has_pending_id(pre.disk, id));
                                if pre.disk.requests.contains_key(id) {
                                    assert(post.disk.requests.contains_key(id));
                                } else {
                                    assert(pre.disk.responses.contains_key(id));
                                    assert(post.disk.responses.contains_key(id));
                                }
                            }
                        }
                    }
                    reveal(AsyncDisk::State::next);
                    reveal(AsyncDisk::State::next_by);
                    assert(AsyncDisk::State::next_by(
                        pre.disk,
                        post.disk,
                        DiskLabel::DiskOps{
                            requests: disk_req_map,
                            responses: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.resps),
                        },
                        AsyncDisk::Step::disk_ops(),
                    ));
                    assert(lbl->info.resps.is_empty());
                    assert(post.disk.requests == pre.disk.requests.union_prefer_right(req_map));
                    assert(post.disk.responses == pre.disk.responses);
                    assert(post.disk.content == pre.disk.content);
                    assert(another_atomic_superblock_write_pending(post) ==>
                        another_atomic_superblock_write_pending(pre)) by {
                        if another_atomic_superblock_write_pending(post) {
                            assert(post.program.state.in_flight == pre.program.state.in_flight);
                            let id = pre.program.state.in_flight.unwrap().req_id;
                            if !pre.disk.requests.contains_key(id) {
                                assert(post.disk.requests.contains_key(id));
                                assert(req_map.contains_key(id));
                                assert(req_map[id].addr() == spec_superblock_addr());
                                let updated = Map::new(
                                    |id| req_map.contains_key(id),
                                    |id| req_map[id].addr(),
                                );
                                assert(updated.contains_key(id));
                                assert(updated[id] == spec_superblock_addr());
                                assert(updated.contains_value(spec_superblock_addr()));
                                assert(false);
                            }
                        }
                    }
                    journal_image_writeback_disjoint_preserved_by_cache_io_begin(
                        pre,
                        post,
                        req_map,
                    );
                    assert(journal_image_writeback_disjoint(post));
                    assert(post.program.state.wf());
                },
                DiskEvent::CacheIOEnd{resp_map} => {
                    assert(AnotherAtomicState::cache_io_end(
                        pre.program.state,
                        post.program.state,
                        resp_map,
                        lbl->info.reqs,
                        lbl->info.resps,
                    ));
                    let disk_resp_map = crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.resps);
                    assert(disk_resp_map == resp_map);
                    let finished = pre.program.state.outstanding_cache_reqs.restrict(resp_map.dom()).invert();
                    let cache_resps = Map::new(
                        |addr| finished.contains_key(addr),
                        |addr| resp_map[finished[addr]],
                    );
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::DiskOps{requests: Set::empty(), responses: cache_resps},
                    );
                    AnotherAtomicState::cache_io_end_preserves_cache_request_wf(
                        pre.program.state,
                        post.program.state,
                        resp_map,
                        lbl->info.reqs,
                        lbl->info.resps,
                    );
                    assert(another_atomic_cache_disk_coupling(post.program.state, post.disk)) by {
                        reveal(AsyncDisk::State::next);
                        reveal(AsyncDisk::State::next_by);
                        assert(AsyncDisk::State::next_by(
                            pre.disk,
                            post.disk,
                            DiskLabel::DiskOps{
                                requests: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.reqs),
                                responses: disk_resp_map,
                            },
                            AsyncDisk::Step::disk_ops(),
                        ));
                        assert(lbl->info.reqs.is_empty());
                        assert(post.disk.requests == pre.disk.requests);
                        assert(post.disk.responses == pre.disk.responses.remove_keys(resp_map.dom()));
                        assert(post.program.state.outstanding_cache_reqs
                            == pre.program.state.outstanding_cache_reqs.remove_keys(resp_map.dom()));
                        assert forall |id: ID| #[trigger] post.program.state.outstanding_cache_reqs.contains_key(id)
                            implies disk_has_pending_id(post.disk, id) by {
                            assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
                            assert(!resp_map.dom().contains(id));
                            assert(disk_has_pending_id(pre.disk, id));
                            if pre.disk.requests.contains_key(id) {
                                assert(post.disk.requests.contains_key(id));
                            } else {
                                assert(pre.disk.responses.contains_key(id));
                                assert(post.disk.responses.contains_key(id));
                            }
                        }
                    }
                    assert(post.program.state.cache_request_wf());
                    assert(post.program.state.wf());
                },
            }
            assert(post.program.state.wf());
            reveal(AsyncDisk::State::next);
            reveal(AsyncDisk::State::next_by);
            assert(AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                DiskLabel::DiskOps{
                    requests: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.reqs),
                    responses: crate::implementation::MultisetMapRelation_v::multiset_to_map(lbl->info.resps),
                },
                AsyncDisk::Step::disk_ops(),
            ));
            assert(post.disk.content == pre.disk.content);
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(post.program.state.wf());
            assert(post.disk.inv());
            assert(another_atomic_model_refinement_invariants(post.program.state));
            assert(another_atomic_cache_disk_coupling(post.program.state, post.disk));
            assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
            assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
            assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
            assert(journal_component_refinement_inv(post));
            assert(branch_component_refinement_inv(post));
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::program_internal(new_program) => {
            assert(post.disk == pre.disk);
            assert(exists |event: InternalEvent| AnotherAtomicState::internal_transition(
                pre.program.state,
                post.program.state,
                event,
            ));
            let event = choose |event: InternalEvent| AnotherAtomicState::internal_transition(
                pre.program.state,
                post.program.state,
                event,
            );
            assert(AnotherAtomicState::internal_transition(
                pre.program.state,
                post.program.state,
                event,
            ));
            match event {
                InternalEvent::CacheInternal{} => {
                    assert(AnotherAtomicState::cache_internal(pre.program.state, post.program.state));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Internal{},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_internal(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_cache_internal(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
                InternalEvent::JournalLoadIndex{reads, discovered_aus} => {
                    assert(AnotherAtomicState::journal_load_index(
                        pre.program.state,
                        post.program.state,
                        reads,
                        discovered_aus,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes: Map::empty()},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        reads,
                        Map::empty(),
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        reads,
                        Map::empty(),
                    );
                    AnotherAtomicState::journal_load_index_effect(
                        pre.program.state,
                        post.program.state,
                        reads,
                        discovered_aus,
                    );
                    assert(pre.program.state.journal.journal.status is None);
                    assert(!pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.journal_metadata_loaded());
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes: Map::empty()},
                        Cache::Step::access(),
                    ));
                    assert(post.program.state.cache.lookup_map == pre.program.state.cache.lookup_map);
                    assert(post.program.state.cache.entries == pre.program.state.cache.entries);
                    assert(post.program.state.cache.status_map == pre.program.state.cache.status_map);
                    assert(filled_cache_status(post.program.state.cache)
                        =~= filled_cache_status(pre.program.state.cache)) by {
                        assert_maps_equal!(
                            filled_cache_status(post.program.state.cache),
                            filled_cache_status(pre.program.state.cache),
                            addr => { }
                        );
                    }
                    assert(journal_image_writeback_disjoint(post)) by {
                        assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
                            && post.disk.requests[id] is WriteReq
                            && post.disk.requests[id]->to != spec_superblock_addr()
                            implies post.program.state.journal_metadata_loaded()
                        by { }
                        assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
                            && filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty
                            implies post.program.state.journal_metadata_loaded()
                        by { }
                        assert forall |addr: Address| #[trigger] filled_cache_status(post.program.state.cache).contains_key(addr)
                            implies {
                                &&& journal_image_dirty_cache_disjoint_at(post, durable_superblock_image_i(post), addr)
                                &&& another_atomic_superblock_write_pending(post) ==>
                                    journal_image_dirty_cache_disjoint_at(
                                        post,
                                        post.program.state.atomic_inflight_superblock_i(),
                                        addr,
                                    )
                            }
                        by {
                            if filled_cache_status(post.program.state.cache)[addr] == CachingDiskPageStatus::Dirty {
                                assert(filled_cache_status(pre.program.state.cache).contains_key(addr));
                                assert(filled_cache_status(pre.program.state.cache)[addr]
                                    == CachingDiskPageStatus::Dirty);
                                assert(pre.program.state.journal_metadata_loaded());
                                assert(false);
                            }
                        }
                        assert forall |id: ID| #[trigger] post.disk.requests.contains_key(id)
                            implies {
                                &&& journal_image_request_writeback_disjoint_at(post, durable_superblock_image_i(post), id)
                                &&& another_atomic_superblock_write_pending(post) ==>
                                    journal_image_request_writeback_disjoint_at(
                                        post,
                                        post.program.state.atomic_inflight_superblock_i(),
                                        id,
                                    )
                            }
                        by {
                            if post.disk.requests[id] is WriteReq && post.disk.requests[id]->to != spec_superblock_addr() {
                                assert(pre.disk.requests.contains_key(id));
                                assert(pre.disk.requests[id] == post.disk.requests[id]);
                                assert(pre.program.state.journal_metadata_loaded());
                                assert(false);
                            }
                        }
                    }
                },
                InternalEvent::ReadForRecovery{
                    addr,
                    keys,
                    msgs,
                    receipt,
                    init_root,
                    reads,
                    writes,
                    branch,
                } => {
                    assert(AnotherAtomicState::read_for_recovery(
                        pre.program.state,
                        post.program.state,
                        addr,
                        keys,
                        msgs,
                        receipt,
                        init_root,
                        reads,
                        writes,
                        branch,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        reads,
                        writes,
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        reads,
                        writes,
                    );
                    let branch_lbl = AtomicBranchState::Label::Append{
                        keys,
                        msgs,
                        receipt,
                        init_root,
                        read_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads),
                        write_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes),
                    };
                    assert(to_aus(writes.dom()) <= pre.program.state.branch_owned_aus()) by {
                        assert(writes.dom() =~= crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes).dom());
                        reveal(AtomicBranchState::State::next);
                        reveal(AtomicBranchState::State::next_by);
                        let step = choose |step: AtomicBranchState::Step|
                            AtomicBranchState::State::next_by(
                                pre.program.state.branch,
                                branch,
                                branch_lbl,
                                step,
                            );
                        match step {
                            AtomicBranchState::Step::append(new_active_branch) => {
                                assert(AtomicBranchState::State::append(
                                    pre.program.state.branch,
                                    branch,
                                    branch_lbl,
                                    new_active_branch,
                                )) by {
                                    reveal(AtomicBranchState::State::append);
                                }
                                assert(to_aus(crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes).dom())
                                    <= pre.program.state.branch.owned_aus());
                            },
                            _ => {
                                assert(false);
                            },
                        }
                    }
                    AnotherAtomicState::read_for_recovery_journal_effect(
                        pre.program.state,
                        post.program.state,
                        addr,
                        keys,
                        msgs,
                        receipt,
                        init_root,
                        reads,
                        writes,
                        branch,
                    );
                    AtomicBranchState::State::append_effect(
                        pre.program.state.branch,
                        branch,
                        branch_lbl,
                    );
                    branch_writes_disjoint_from_journal_projection(pre, writes);
                    let durable_image = durable_superblock_image_i(pre);
                    journal_image_static_domain_subset_journal_projection(pre, durable_image);
                    assert(writes.dom().disjoint(journal_image_static_domain_i(pre, durable_image))) by {
                        assert forall |a: Address| #[trigger] writes.dom().contains(a)
                            implies !journal_image_static_domain_i(pre, durable_image).contains(a) by {
                            if journal_image_static_domain_i(pre, durable_image).contains(a) {
                                assert(addresses_in_aus(journal_projection_aus(pre)).contains(a));
                                assert(false);
                            }
                        }
                    }
                    if another_atomic_superblock_write_pending(pre) {
                        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                        journal_image_static_domain_subset_journal_projection(pre, frozen_image);
                        assert(writes.dom().disjoint(journal_image_static_domain_i(pre, frozen_image))) by {
                            assert forall |a: Address| #[trigger] writes.dom().contains(a)
                                implies !journal_image_static_domain_i(pre, frozen_image).contains(a) by {
                                if journal_image_static_domain_i(pre, frozen_image).contains(a) {
                                    assert(addresses_in_aus(journal_projection_aus(pre)).contains(a));
                                    assert(false);
                                }
                            }
                        }
                    }
                    assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                        == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                },
                InternalEvent::JournalMarshall{addr, raw_page} => {
                    assert(AnotherAtomicState::journal_marshall(
                        pre.program.state,
                        post.program.state,
                        addr,
                        raw_page,
                    ));
                    let writes = Map::<Address, RawPage>::empty().insert(addr, raw_page);
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads: Map::empty(), writes},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        Map::empty(),
                        writes,
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        Map::empty(),
                        writes,
                    );
                    let journal_lbl = AtomicJournalState::Label::JournalMarshal{
                        addr,
                        writes: to_journal_records(writes),
                    };
                    reveal(AtomicJournalState::State::next);
                    reveal(AtomicJournalState::State::next_by);
                    let journal_step = choose |step: AtomicJournalState::Step|
                        AtomicJournalState::State::next_by(
                            pre.program.state.journal,
                            post.program.state.journal,
                            journal_lbl,
                            step,
                        );
                    match journal_step {
                        AtomicJournalState::Step::journal_marshal(new_journal) => {
                            assert(AtomicJournalState::State::journal_marshal(
                                pre.program.state.journal,
                                post.program.state.journal,
                                journal_lbl,
                                new_journal,
                            ));
                            assert(pre.program.state.journal.mini_allocator.tight_next_addr(
                                pre.program.state.journal.journal.snapshot.freshest_rec(),
                                addr,
                            ));
                            assert(pre.program.state.journal.mini_allocator.can_allocate(addr));
                            assert(post.program.state.journal.mini_allocator
                                == pre.program.state.journal.mini_allocator.allocate(addr).observe(addr));
                            assert(post.program.state.journal.journal.status is Some);
                        },
                        _ => {
                            assert(false);
                        },
                    }
                    assert(pre.program.state.journal_metadata_loaded());
                    assert(post.program.state.journal_metadata_loaded());
                    let durable_image = durable_superblock_image_i(pre);
                    assert(journal_allocable_addrs_image_disjoint(pre));
                    assert(!journal_image_static_domain_i(pre, durable_image).contains(addr));
                    assert(writes.dom().disjoint(journal_image_static_domain_i(pre, durable_image))) by {
                        assert forall |a: Address| #[trigger] writes.dom().contains(a)
                            implies !journal_image_static_domain_i(pre, durable_image).contains(a) by {
                            assert(a == addr);
                        }
                    }
                    if another_atomic_superblock_write_pending(pre) {
                        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                        assert(pre.program.state.in_flight is Some);
                        assert(!journal_image_static_domain_i(pre, frozen_image).contains(addr));
                        assert(writes.dom().disjoint(journal_image_static_domain_i(pre, frozen_image))) by {
                            assert forall |a: Address| #[trigger] writes.dom().contains(a)
                                implies !journal_image_static_domain_i(pre, frozen_image).contains(a) by {
                                assert(a == addr);
                            }
                        }
                    }
                    assert forall |a: Address|
                        #[trigger] post.program.state.journal.mini_allocator.can_allocate(a)
                        implies pre.program.state.journal.mini_allocator.can_allocate(a) by {
                        pre.program.state.journal.mini_allocator
                            .allocate_observe_can_allocate_subset(addr, a);
                    }
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        Map::empty(),
                        writes,
                    );
                    assert(journal_image_writeback_disjoint(post));
                },
                InternalEvent::ObserveCleanJournalAUs{aus} => {
                    assert(AnotherAtomicState::acknowledge_flushed_journal_aus(
                        pre.program.state,
                        post.program.state,
                        aus,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::EvictableCheck{aus},
                    );
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::EvictableCheck{aus},
                        Cache::Step::evictable(),
                    ));
                    assert(post.program.state.cache == pre.program.state.cache);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
                InternalEvent::JournalFillAUs{aus} => {
                    assert(AnotherAtomicState::journal_fill_aus(pre.program.state, post.program.state, aus));
                    assert(post.program.state.cache == pre.program.state.cache);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
                InternalEvent::BranchLoadMetadata{root, reads, discovered_aus} => {
                    assert(AnotherAtomicState::branch_load_metadata(
                        pre.program.state,
                        post.program.state,
                        root,
                        reads,
                        discovered_aus,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes: Map::empty()},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        reads,
                        Map::empty(),
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        reads,
                        Map::empty(),
                    );
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
                    let branch_lbl = AtomicBranchState::Label::LoadMetadata{
                        root,
                        discovered_aus,
                        read_nodes,
                    };
                    reveal(AtomicBranchState::State::next);
                    reveal(AtomicBranchState::State::next_by);
                    let branch_step = choose |step: AtomicBranchState::Step|
                        AtomicBranchState::State::next_by(
                            pre.program.state.branch,
                            post.program.state.branch,
                            branch_lbl,
                            step,
                        );
                    match branch_step {
                        AtomicBranchState::Step::load_metadata() => {
                            assert(AtomicBranchState::State::load_metadata(
                                pre.program.state.branch,
                                post.program.state.branch,
                                branch_lbl,
                            )) by {
                                reveal(AtomicBranchState::State::load_metadata);
                            }
                        },
                        _ => {
                            assert(false);
                        },
                    }
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    journal_image_writeback_disjoint_preserved_by_read_only_cache_access(
                        pre,
                        post,
                        reads,
                    );
                },
                InternalEvent::MetadataLoadComplete{} => {
                    assert(AnotherAtomicState::metadata_load_complete(pre.program.state, post.program.state));
                    assert(post.program.state.cache == pre.program.state.cache);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
                InternalEvent::BranchGrow{new_root_addr, reads, writes, branch} => {
                    assert(AnotherAtomicState::branch_grow(
                        pre.program.state,
                        post.program.state,
                        new_root_addr,
                        reads,
                        writes,
                        branch,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        reads,
                        writes,
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        reads,
                        writes,
                    );
                    let write_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes);
                    let branch_lbl = AtomicBranchState::Label::Grow{
                        new_root_addr,
                        read_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads),
                        write_nodes,
                    };
                    reveal(AtomicBranchState::State::next);
                    reveal(AtomicBranchState::State::next_by);
                    let branch_step = choose |step: AtomicBranchState::Step|
                        AtomicBranchState::State::next_by(
                            pre.program.state.branch,
                            branch,
                            branch_lbl,
                            step,
                        );
                    match branch_step {
                        AtomicBranchState::Step::grow(new_active_branch) => {
                            assert(AtomicBranchState::State::grow(
                                pre.program.state.branch,
                                branch,
                                branch_lbl,
                                new_active_branch,
                            )) by {
                                reveal(AtomicBranchState::State::grow);
                            }
                            let cached_lbl = CachedBranch::Label::Grow{
                                mini_allocator: pre.program.state.branch.mini_allocator,
                                new_root_addr,
                                read_nodes: crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads),
                                write_nodes,
                            };
                            assert(CachedBranch::State::next(
                                pre.program.state.branch.active_branch,
                                new_active_branch,
                                cached_lbl,
                            ));
                            reveal(CachedBranch::State::next);
                            reveal(CachedBranch::State::next_by);
                            assert(CachedBranch::State::next_by(
                                pre.program.state.branch.active_branch,
                                new_active_branch,
                                cached_lbl,
                                CachedBranch::Step::grow_step(),
                            ));
                            assert(CachedBranch::State::grow_step(
                                pre.program.state.branch.active_branch,
                                new_active_branch,
                                cached_lbl,
                            ));
                            assert(write_nodes == loaded_grow_write_nodes(
                                pre.program.state.branch.active_branch.root.unwrap(),
                                new_root_addr,
                            ));
                            assert(pre.program.state.branch.mini_allocator.can_allocate(new_root_addr));
                            assert(pre.program.state.branch.mini_allocator.all_aus().contains(new_root_addr.au));
                            assert(to_aus(write_nodes.dom()) <= pre.program.state.branch_owned_aus());
                        },
                        _ => {
                            assert(false);
                        },
                    }
                    assert(writes.dom() =~= write_nodes.dom());
                    assert(to_aus(writes.dom()) <= pre.program.state.branch_owned_aus());
                    branch_writes_disjoint_from_journal_projection(pre, writes);
                    let durable_image = durable_superblock_image_i(pre);
                    journal_image_static_domain_subset_journal_projection(pre, durable_image);
                    assert(writes.dom().disjoint(journal_image_static_domain_i(pre, durable_image))) by {
                        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                            implies !journal_image_static_domain_i(pre, durable_image).contains(addr) by {
                            if journal_image_static_domain_i(pre, durable_image).contains(addr) {
                                assert(addresses_in_aus(journal_projection_aus(pre)).contains(addr));
                                assert(false);
                            }
                        }
                    }
                    if another_atomic_superblock_write_pending(pre) {
                        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                        journal_image_static_domain_subset_journal_projection(pre, frozen_image);
                        assert(writes.dom().disjoint(journal_image_static_domain_i(pre, frozen_image))) by {
                            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                implies !journal_image_static_domain_i(pre, frozen_image).contains(addr) by {
                                if journal_image_static_domain_i(pre, frozen_image).contains(addr) {
                                    assert(addresses_in_aus(journal_projection_aus(pre)).contains(addr));
                                    assert(false);
                                }
                            }
                        }
                    }
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                        == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_image_writeback_disjoint(post));
                },
                InternalEvent::BranchSplit{new_child_addr, receipt, split_arg, reads, writes, branch} => {
                    assert(AnotherAtomicState::branch_split(
                        pre.program.state,
                        post.program.state,
                        new_child_addr,
                        receipt,
                        split_arg,
                        reads,
                        writes,
                        branch,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        reads,
                        writes,
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        reads,
                        writes,
                    );
                    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
                    let write_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes);
                    let branch_lbl = AtomicBranchState::Label::Split{
                        new_child_addr,
                        receipt,
                        split_arg,
                        read_nodes,
                        write_nodes,
                    };
                    reveal(AtomicBranchState::State::next);
                    reveal(AtomicBranchState::State::next_by);
                    let branch_step = choose |step: AtomicBranchState::Step|
                        AtomicBranchState::State::next_by(
                            pre.program.state.branch,
                            branch,
                            branch_lbl,
                            step,
                        );
                    match branch_step {
                        AtomicBranchState::Step::split(new_active_branch) => {
                            assert(AtomicBranchState::State::split(
                                pre.program.state.branch,
                                branch,
                                branch_lbl,
                                new_active_branch,
                            )) by {
                                reveal(AtomicBranchState::State::split);
                            }
                            let cached_lbl = CachedBranch::Label::Split{
                                mini_allocator: pre.program.state.branch.mini_allocator,
                                new_child_addr,
                                receipt,
                                split_arg,
                                read_nodes,
                                write_nodes,
                            };
                            assert(CachedBranch::State::next(
                                pre.program.state.branch.active_branch,
                                new_active_branch,
                                cached_lbl,
                            ));
                            reveal(CachedBranch::State::next);
                            reveal(CachedBranch::State::next_by);
                            let cached_step = choose |step: CachedBranch::Step|
                                CachedBranch::State::next_by(
                                    pre.program.state.branch.active_branch,
                                    new_active_branch,
                                    cached_lbl,
                                    step,
                                );
                            match cached_step {
                                CachedBranch::Step::split_step() => {
                                    assert(CachedBranch::State::split_step(
                                        pre.program.state.branch.active_branch,
                                        new_active_branch,
                                        cached_lbl,
                                    )) by {
                                        reveal(CachedBranch::State::split_step);
                                    }
                                    assert(write_nodes == loaded_split_write_nodes(
                                        receipt,
                                        read_nodes,
                                        split_arg,
                                        new_child_addr,
                                    ));
                                    assert(pre.program.state.branch.mini_allocator.can_allocate(new_child_addr));
                                },
                                _ => {
                                    assert(false);
                                },
                            }
                            assert(new_active_branch == pre.program.state.branch.active_branch);
                        },
                        _ => {
                            assert(false);
                        },
                    }
                    let cdb = branch_caching_disk_state_i(pre);
                    let active_i = cdb.active_branch_i();
                    let linked = active_i.branch.unwrap();
                    let parent_addr = receipt.target().addr;
                    let child_addr = receipt.child_addr();
                    assert(active_i.inv());
                    assert(active_i.branch is Some);
                    assert(linked.inv());
                    assert(linked.inv_internal(linked.the_ranking()));
                    assert(receipt.root == linked.root);
                    assert(linked.disk_view.is_fresh(set!{new_child_addr})) by {
                        assert forall |addr: Address| #[trigger] set![new_child_addr].contains(addr)
                            implies !linked.disk_view.entries.contains_key(addr) by {
                            assert(addr == new_child_addr);
                            if linked.disk_view.entries.contains_key(addr) {
                                assert(active_i.addrs_closed_under_mini_allocator());
                                assert(active_i.mini_allocator.page_is_reserved(addr));
                                assert(pre.program.state.branch.mini_allocator.can_allocate(new_child_addr));
                                assert(false);
                            }
                        }
                    }
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    let cache_lbl = Cache::Label::Access{reads, writes};
                    assert(cache_lbl is Access);
                    assert(cache_lbl->reads == reads);
                    assert(cache_lbl->writes == writes);
                    assert(Cache::State::next_by(
                        pre.program.state.cache,
                        post.program.state.cache,
                        cache_lbl,
                        Cache::Step::access(),
                    ));
                    assert(Cache::State::access(
                        pre.program.state.cache,
                        post.program.state.cache,
                        cache_lbl,
                    )) by {
                        reveal(Cache::State::access);
                    }
                    pre.program.state.cache.build_lookup_map_ensures();
                    assert(pre.program.state.cache.build_lookup_map_props(
                        pre.program.state.cache.lookup_map,
                    ));
                    assert forall |addr: Address| #[trigger] reads.contains_key(addr)
                        implies pre.program.state.cache.valid_read(addr, reads[addr]) by {
                        assert(cache_lbl->reads.contains_key(addr));
                    }
                    assert forall |addr: Address|
                        #[trigger] linked.disk_view.entries.contains_key(addr)
                        implies linked.disk_view.entries[addr]
                            == crate::implementation::CachingDiskBranch_v::to_branch_nodes(cdb.disk.visible())[addr]
                    by {
                        assert(crate::implementation::CachingDiskBranch_v::active_loaded_nodes_of(
                            cdb.disk,
                            cdb.mini_allocator,
                        ).contains_key(addr));
                    }
                    assert forall |addr: Address|
                        #[trigger] linked.disk_view.entries.contains_key(addr)
                        && read_nodes.contains_key(addr)
                        implies linked.disk_view.entries[addr] == read_nodes[addr]
                    by {
                        assert(read_nodes.contains_key(addr) <==> reads.contains_key(addr));
                        assert(reads.contains_key(addr));
                        assert(pre.program.state.cache.valid_read(addr, reads[addr]));
                        assert(pre.program.state.cache.lookup_map.contains_key(addr));
                        assert(pre.program.state.cache.entries.contains_key(
                            pre.program.state.cache.lookup_map[addr],
                        ));
                        assert(pre.program.state.cache.entries[pre.program.state.cache.lookup_map[addr]] is Filled);
                        assert(cache_filled_addr(pre.program.state.cache, addr));
                        assert(cache_filled_page(pre.program.state.cache, addr) == reads[addr]);
                        assert(crate::implementation::CachingDiskBranch_v::active_loaded_nodes_of(
                            cdb.disk,
                            cdb.mini_allocator,
                        ).contains_key(addr));
                        assert(cdb.mini_allocator.all_aus().contains(addr.au));
                        assert(branch_projection_aus(pre).contains(addr.au));
                        assert(cdb.disk.cache.contains_key(addr));
                        assert(cdb.disk.cache[addr] == reads[addr]);
                        assert(cdb.disk.visible().contains_key(addr));
                        assert(cdb.disk.visible()[addr] == reads[addr]);
                    }
                    crate::implementation::CachingDiskBranch_v::receipt_path_valid_for_split_from_loaded(
                        linked,
                        linked.the_ranking(),
                        read_nodes,
                        receipt,
                        split_arg,
                        new_child_addr,
                    );
                    let path = crate::betree::LinkedBranch_v::Path{
                        branch: linked,
                        key: split_arg.get_pivot(),
                        depth: receipt.depth(),
                    };
                    assert(path.valid());
                    assert(path.target().root == parent_addr);
                    assert(path.target().disk_view == linked.disk_view);
                    assert(path.target().can_split_child_of_index(split_arg, new_child_addr));
                    assert(linked.disk_view.entries.contains_key(parent_addr));
                    assert(linked.disk_view.entries.contains_key(child_addr));
                    assert(to_aus(writes.dom()) <= pre.program.state.branch_owned_aus()) by {
                        assert(writes.dom() =~= write_nodes.dom());
                        assert forall |au: AU| #[trigger] to_aus(writes.dom()).contains(au)
                            implies pre.program.state.branch_owned_aus().contains(au) by {
                            let addr = choose |addr: Address| writes.dom().contains(addr) && addr.au == au;
                            assert(write_nodes.contains_key(addr));
                            assert(write_nodes == loaded_split_write_nodes(
                                receipt,
                                read_nodes,
                                split_arg,
                                new_child_addr,
                            ));
                            if addr == new_child_addr {
                                assert(pre.program.state.branch.mini_allocator.can_allocate(new_child_addr));
                                assert(pre.program.state.branch.mini_allocator.all_aus().contains(au));
                            } else {
                                assert(addr == parent_addr || addr == child_addr);
                                assert(linked.disk_view.entries.contains_key(addr));
                                assert(active_i.addrs_closed_under_mini_allocator());
                                assert(active_i.mini_allocator.page_is_reserved(addr));
                                assert(pre.program.state.branch.mini_allocator.all_aus().contains(au));
                            }
                        }
                    }
                    branch_writes_disjoint_from_journal_projection(pre, writes);
                    let durable_image = durable_superblock_image_i(pre);
                    journal_image_static_domain_subset_journal_projection(pre, durable_image);
                    assert(writes.dom().disjoint(journal_image_static_domain_i(pre, durable_image))) by {
                        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                            implies !journal_image_static_domain_i(pre, durable_image).contains(addr) by {
                            if journal_image_static_domain_i(pre, durable_image).contains(addr) {
                                assert(addresses_in_aus(journal_projection_aus(pre)).contains(addr));
                                assert(false);
                            }
                        }
                    }
                    if another_atomic_superblock_write_pending(pre) {
                        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                        journal_image_static_domain_subset_journal_projection(pre, frozen_image);
                        assert(writes.dom().disjoint(journal_image_static_domain_i(pre, frozen_image))) by {
                            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                implies !journal_image_static_domain_i(pre, frozen_image).contains(addr) by {
                                if journal_image_static_domain_i(pre, frozen_image).contains(addr) {
                                    assert(addresses_in_aus(journal_projection_aus(pre)).contains(addr));
                                    assert(false);
                                }
                            }
                        }
                    }
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                        == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_image_writeback_disjoint(post));
                },
                InternalEvent::BranchSeal{aux_ptr, summary, reads, writes, branch} => {
                    assert(AnotherAtomicState::branch_seal(
                        pre.program.state,
                        post.program.state,
                        aux_ptr,
                        summary,
                        reads,
                        writes,
                        branch,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::Access{reads, writes},
                    );
                    AnotherAtomicState::cache_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        reads,
                        writes,
                    );
                    cache_disk_request_wf_preserved_by_cache_access(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                        reads,
                        writes,
                    );
                    let read_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(reads);
                    let write_nodes = crate::implementation::AnotherAtomicState_v::to_branch_nodes(writes);
                    let branch_lbl = AtomicBranchState::Label::Seal{
                        aux_ptr,
                        summary,
                        read_nodes,
                        write_nodes,
                    };
                    reveal(AtomicBranchState::State::next);
                    reveal(AtomicBranchState::State::next_by);
                    let branch_step = choose |step: AtomicBranchState::Step|
                        AtomicBranchState::State::next_by(
                            pre.program.state.branch,
                            branch,
                            branch_lbl,
                            step,
                        );
                    match branch_step {
                        AtomicBranchState::Step::seal() => {
                            assert(AtomicBranchState::State::seal(
                                pre.program.state.branch,
                                branch,
                                branch_lbl,
                            )) by {
                                reveal(AtomicBranchState::State::seal);
                            }
                            let cached_lbl = CachedBranch::Label::Seal{
                                mini_allocator: pre.program.state.branch.mini_allocator,
                                aux_ptr,
                                read_nodes,
                                write_nodes,
                            };
                            assert(CachedBranch::State::next(
                                pre.program.state.branch.active_branch,
                                pre.program.state.branch.active_branch,
                                cached_lbl,
                            ));
                            reveal(CachedBranch::State::next);
                            reveal(CachedBranch::State::next_by);
                            assert(CachedBranch::State::next_by(
                                pre.program.state.branch.active_branch,
                                pre.program.state.branch.active_branch,
                                cached_lbl,
                                CachedBranch::Step::seal_step(),
                            ));
                            assert(CachedBranch::State::seal_step(
                                pre.program.state.branch.active_branch,
                                pre.program.state.branch.active_branch,
                                cached_lbl,
                            ));
                            let root = pre.program.state.branch.active_branch.root.unwrap();
                            assert(write_nodes == loaded_seal_write_nodes(
                                root,
                                read_nodes,
                                aux_ptr,
                                pre.program.state.branch.mini_allocator.reserved_aus(),
                            ));
                            assert(pre.program.state.branch.active_branch.valid_allocator(
                                pre.program.state.branch.mini_allocator,
                            ));
                            assert(pre.program.state.branch.mini_allocator.all_aus().contains(root.au));
                            if aux_ptr is Some {
                                assert(pre.program.state.branch.mini_allocator.can_allocate(aux_ptr.unwrap()));
                                assert(pre.program.state.branch.mini_allocator.all_aus().contains(aux_ptr.unwrap().au));
                            }
                            assert(to_aus(write_nodes.dom()) <= pre.program.state.branch_owned_aus());
                        },
                        _ => {
                            assert(false);
                        },
                    }
                    assert(writes.dom() =~= write_nodes.dom());
                    assert(to_aus(writes.dom()) <= pre.program.state.branch_owned_aus());
                    branch_writes_disjoint_from_journal_projection(pre, writes);
                    let durable_image = durable_superblock_image_i(pre);
                    journal_image_static_domain_subset_journal_projection(pre, durable_image);
                    assert(writes.dom().disjoint(journal_image_static_domain_i(pre, durable_image))) by {
                        assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                            implies !journal_image_static_domain_i(pre, durable_image).contains(addr) by {
                            if journal_image_static_domain_i(pre, durable_image).contains(addr) {
                                assert(addresses_in_aus(journal_projection_aus(pre)).contains(addr));
                                assert(false);
                            }
                        }
                    }
                    if another_atomic_superblock_write_pending(pre) {
                        let frozen_image = pre.program.state.atomic_inflight_superblock_i();
                        journal_image_static_domain_subset_journal_projection(pre, frozen_image);
                        assert(writes.dom().disjoint(journal_image_static_domain_i(pre, frozen_image))) by {
                            assert forall |addr: Address| #[trigger] writes.dom().contains(addr)
                                implies !journal_image_static_domain_i(pre, frozen_image).contains(addr) by {
                                if journal_image_static_domain_i(pre, frozen_image).contains(addr) {
                                    assert(addresses_in_aus(journal_projection_aus(pre)).contains(addr));
                                    assert(false);
                                }
                            }
                        }
                    }
                    assert(post.program.state.journal == pre.program.state.journal);
                    assert(post.program.state.in_flight == pre.program.state.in_flight);
                    assert(post.program.state.journal.in_flight == pre.program.state.journal.in_flight);
                    assert(post.program.state.branch.in_flight == pre.program.state.branch.in_flight);
                    assert(post.program.state.journal.journal.status.unwrap().lsn_au_index
                        == pre.program.state.journal.journal.status.unwrap().lsn_au_index);
                    journal_image_writeback_disjoint_preserved_by_cache_access(
                        pre,
                        post,
                        reads,
                        writes,
                    );
                    assert(journal_image_writeback_disjoint(post));
                },
                InternalEvent::BranchFillAUs{aus} => {
                    assert(AnotherAtomicState::branch_fill_aus(pre.program.state, post.program.state, aus));
                    assert(post.program.state.cache == pre.program.state.cache);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
                InternalEvent::ObservePersistedBranchRoots{target_count, aus} => {
                    assert(AnotherAtomicState::observe_persisted_branch_roots(
                        pre.program.state,
                        post.program.state,
                        target_count,
                        aus,
                    ));
                    Cache::State::inv_next(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::EvictableCheck{aus},
                    );
                    reveal(Cache::State::next);
                    reveal(Cache::State::next_by);
                    assert(Cache::State::next_by(
                        pre.program.state.cache,
                        post.program.state.cache,
                        Cache::Label::EvictableCheck{aus},
                        Cache::Step::evictable(),
                    ));
                    assert(post.program.state.cache == pre.program.state.cache);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
                InternalEvent::RecoveryComplete{} => {
                    assert(AnotherAtomicState::recovery_complete(pre.program.state, post.program.state));
                    assert(post.program.state.cache == pre.program.state.cache);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
                InternalEvent::AcceptSyncRequest{sync_req_id} => {
                    assert(AnotherAtomicState::accept_sync_request(
                        pre.program.state,
                        post.program.state,
                        sync_req_id,
                    ));
                    assert(post.program.state.cache == pre.program.state.cache);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
                InternalEvent::DeliverSyncReply{sync_req_id} => {
                    assert(AnotherAtomicState::deliver_sync_reply(
                        pre.program.state,
                        post.program.state,
                        sync_req_id,
                    ));
                    assert(post.program.state.cache == pre.program.state.cache);
                    AnotherAtomicState::cache_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                    );
                    cache_disk_request_wf_preserved_by_unchanged(
                        pre.program.state,
                        post.program.state,
                        post.disk,
                    );
                },
            }
            assert(post.program.state.cache.inv());
            assert(post.program.state.cache_request_wf());
            assert(post.program.state.wf());
            assert(post.disk.inv());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(another_atomic_model_refinement_invariants(post.program.state));
            assert(another_atomic_cache_disk_coupling(post.program.state, post.disk));
            assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
            assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
            assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
            assert(journal_component_refinement_inv(post));
            assert(branch_component_refinement_inv(post));
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::disk_internal(new_disk) => {
            assert(post.program == pre.program);
            assert(post.program.state == pre.program.state);
            assert(post.program.state.wf());
            assert(another_atomic_model_refinement_invariants(post.program.state));
            async_disk_inv_next(pre.disk, post.disk, DiskLabel::Internal{});
            reveal(AsyncDisk::State::next);
            reveal(AsyncDisk::State::next_by);
            let disk_step = choose |step| AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                DiskLabel::Internal{},
                step,
            );
            async_disk_superblock_page_wf_preserved_by_internal(
                pre.program.state,
                pre.disk,
                post.disk,
            );
            assert(post.disk.inv());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(another_atomic_cache_disk_coupling(post.program.state, post.disk)) by {
                assert forall |id: ID| #[trigger] post.program.state.outstanding_cache_reqs.contains_key(id)
                    implies disk_has_pending_id(post.disk, id) by {
                    assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
                    assert(disk_has_pending_id(pre.disk, id));
                    disk_has_pending_id_preserved_by_internal(pre.disk, post.disk, id);
                }
            }
            assert(another_atomic_superblock_disk_coupling(post.program.state, post.disk));
            superblock_write_request_wf_preserved_by_internal(
                post.program.state,
                pre.disk,
                post.disk,
            );
            assert(another_atomic_superblock_write_request_wf(post.program.state, post.disk));
            cache_disk_request_wf_preserved_by_internal(
                post.program.state,
                pre.disk,
                post.disk,
            );
            assert(another_atomic_cache_disk_request_wf(post.program.state, post.disk));
            assert(branch_component_refinement_inv(post));
            assert(post.program.state.wf());
            assert(post.disk.inv());
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(!post.program.state.journal_metadata_loaded() ==>
                post.program.state.journal.mini_allocator
                    == crate::allocation_layer::MiniAllocator_v::MiniAllocator::empty());
            match disk_step {
                AsyncDisk::Step::process_read(id) => {
                    assert(AsyncDisk::State::next_by(
                        pre.disk,
                        post.disk,
                        DiskLabel::Internal{},
                        AsyncDisk::Step::process_read(id),
                    ));
                    assert(post.disk.content == pre.disk.content);
                    assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));
                    assert(journal_projection_aus(post) == journal_projection_aus(pre));
                    assert(journal_disk_persistent_i(post) == journal_disk_persistent_i(pre));
                    assert(journal_disk_cache_i(post) == journal_disk_cache_i(pre));
                    assert(journal_disk_status_i(post) == journal_disk_status_i(pre));
                    assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
                    assert(journal_projection_tight(post));
                    assert(journal_projection_uses_shared_async_disk(post));
                    assert(persistent_journal_image_i(post).wf());
                },
                AsyncDisk::Step::process_write(id) => {
                    assert(AsyncDisk::State::next_by(
                        pre.disk,
                        post.disk,
                        DiskLabel::Internal{},
                        AsyncDisk::Step::process_write(id),
                    ));
                    let req = pre.disk.requests[id];
                    assert(post.disk.content == pre.disk.content.insert(req->to, req->data));
                    if req->to == spec_superblock_addr() {
                        assert(pre.program.state.in_flight is Some);
                        assert(req->data == marshal_abstract_superblock(
                            pre.program.state.atomic_inflight_superblock_i(),
                        ));
                        assert(pre.program.state.atomic_inflight_superblock_i().wf());
                        marshalled_abstract_superblock_raw_wf(
                            pre.program.state.atomic_inflight_superblock_i(),
                        );
	                    } else {
	                        assert(another_atomic_cache_disk_request_wf(pre.program.state, pre.disk));
	                        assert(journal_image_writeback_disjoint(pre));
	                        assert(pre.program.state.journal_metadata_loaded());
	                        assert(pre.program.state.outstanding_cache_reqs.contains_key(id));
	                        assert(pre.program.state.outstanding_cache_reqs[id] == req->to);
	                        assert(cache_filled_addr(pre.program.state.cache, req->to));
	                        assert(cache_filled_page(pre.program.state.cache, req->to) == req->data);
	                        assert(filled_cache_status(pre.program.state.cache).contains_key(req->to));
                        assert(filled_cache_status(pre.program.state.cache)[req->to]
	                            == CachingDiskPageStatus::Writeback);
	                        assert(post.disk.content[spec_superblock_addr()]
	                            == pre.disk.content[spec_superblock_addr()]);
	                        assert(durable_superblock_image_i(post) == durable_superblock_image_i(pre));
	                        let image = durable_superblock_image_i(pre);
	                        assert(journal_image_request_writeback_disjoint_at(pre, image, id));
	                        journal_image_persistent_preserved_by_disjoint_write(
	                            pre,
	                            post,
	                            image,
	                            req->to,
	                            req->data,
	                        );
	                        assert(persistent_journal_image_i(post) == persistent_journal_image_i(pre));
	                        if another_atomic_superblock_write_pending(pre) {
	                            let frozen_image = pre.program.state.atomic_inflight_superblock_i();
	                            assert(journal_image_request_writeback_disjoint_at(pre, frozen_image, id));
	                            journal_image_persistent_preserved_by_disjoint_write(
	                                pre,
	                                post,
	                                frozen_image,
	                                req->to,
	                                req->data,
	                            );
	                            assert(frozen_journal_image_i(post) == frozen_journal_image_i(pre));
	                        }
	                    }
	                },
                _ => {
                    assert(false);
                },
            }
            assert(persistent_journal_image_i(post).wf());
            assert(journal_projection_tight(post));
            assert(journal_projection_uses_shared_async_disk(post));
            assert(journal_component_refinement_inv(post));
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::crash(new_program, new_disk) => {
            async_disk_inv_next(pre.disk, post.disk, DiskLabel::Crash{});
            reveal(AsyncDisk::State::next);
            reveal(AsyncDisk::State::next_by);
            assert(AsyncDisk::State::next_by(
                pre.disk,
                post.disk,
                DiskLabel::Crash{},
                AsyncDisk::Step::crash(),
            ));
            assert(post.disk.content == pre.disk.content);
            assert(async_disk_superblock_page_wf(post.disk.content));
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::noop() => {
            assert(post == pre);
            assert(another_atomic_disk_refinement_invariants(post));
        },
        SystemModel::Step::dummy_to_use_type_params(_) => {
            assert(false);
        },
    }
}

pub uninterp spec fn another_atomic_disk_versions_i(
    atomic: AnotherAtomicState,
    disk: AsyncDisk::State,
) -> FloatingSeq<Version>;

pub uninterp spec fn another_atomic_disk_sync_requests_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> Map<SyncReqId, nat>;

pub open spec fn another_atomic_disk_i(
    model: SystemModel::State<AnotherProgramModel>,
) -> CrashTolerantAsyncMap::State
{
    CrashTolerantAsyncMap::State{
        versions: another_atomic_disk_versions_i(model.program.state, model.disk),
        async_ephemeral: requests_replies_i(model.requests, model.replies),
        sync_requests: another_atomic_disk_sync_requests_i(model),
    }
}

// ================================================================
// Cache extensions (used by ConcreteJournalRefinement_v)
// ================================================================

impl Cache::State {
    pub open spec fn valid_clean_slot(self, slot: Slot) -> bool
    {
        &&& self.status_map.contains_key(slot)
        &&& self.status_map[slot] is Clean
    }

    pub open spec fn valid_dirty_addr(self, addr: Address) -> bool
    {
        &&& self.lookup_map.contains_key(addr)
        &&& (self.status_map[self.lookup_map[addr]] is Writeback
            || self.status_map[self.lookup_map[addr]] is Dirty)
    }
}

// ================================================================
// Composition-side placeholders for the AnotherAtomicState + AsyncDisk adapter
// ================================================================

impl SystemModel::State<AnotherProgramModel> {
    pub open spec fn outstanding_reqs_consistent(self) -> bool
    {
        true
    }

    pub open spec fn awaiting_sb_response_is_disk_content(self) -> bool
    {
        true
    }

    pub open spec fn persistent_sb_disk_inv(self) -> bool
    {
        true
    }

    pub open spec fn journal_pages_parsable(self) -> bool
    {
        true
    }

    pub open spec fn cache_reads_agree_with_disk(self) -> bool
    {
        true
    }

    pub open spec fn persistent_journal_structure(self) -> bool
    {
        true
    }
}

// ================================================================
// RefinementObligation adapter for AnotherAtomicState + AsyncDisk
// ================================================================

pub struct RefinementProof{}

impl RefinementObligation<AnotherProgramModel> for RefinementProof {

    open spec fn inv(model: SystemModel::State<AnotherProgramModel>) -> bool
    {
        another_atomic_disk_refinement_invariants(model)
    }

    closed spec fn i(model: SystemModel::State<AnotherProgramModel>) -> (mapspec: CrashTolerantAsyncMap::State)
    {
        another_atomic_disk_i(model)
    }

    closed spec fn i_lbl(
        pre: SystemModel::State<AnotherProgramModel>,
        post: SystemModel::State<AnotherProgramModel>,
        lbl: SystemModel::Label,
    ) -> (ctam_lbl: CrashTolerantAsyncMap::Label)
    {
        match lbl {
            SystemModel::Label::AcceptRequest{req} =>
                CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::RequestOp{req},
                },
            SystemModel::Label::DeliverReply{reply} =>
                CrashTolerantAsyncMap::Label::OperateOp{
                    base_op: AsyncMap::Label::ReplyOp{reply},
                },
            SystemModel::Label::AcceptSyncRequest{..} => CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::DeliverSyncReply{..} => CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::ProgramUIOp{op} => {
                match op {
                    ProgramUserOp::Execute{req, reply} =>
                        CrashTolerantAsyncMap::Label::OperateOp{
                            base_op: AsyncMap::Label::ExecuteOp{req, reply},
                        },
                    ProgramUserOp::AcceptSyncRequest{sync_req_id} =>
                        CrashTolerantAsyncMap::Label::ReqSyncOp{sync_req_id},
                    ProgramUserOp::DeliverSyncReply{sync_req_id} =>
                        CrashTolerantAsyncMap::Label::ReplySyncOp{sync_req_id},
                }
            },
            SystemModel::Label::ProgramDiskOp{..} => CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::ProgramInternal => CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::DiskInternal => CrashTolerantAsyncMap::Label::Noop{},
            SystemModel::Label::Crash => CrashTolerantAsyncMap::Label::CrashOp{},
            SystemModel::Label::Noop => CrashTolerantAsyncMap::Label::Noop{},
        }
    }

    proof fn i_lbl_valid(
        pre: SystemModel::State<AnotherProgramModel>,
        post: SystemModel::State<AnotherProgramModel>,
        lbl: SystemModel::Label,
        ctam_lbl: CrashTolerantAsyncMap::Label,
    )
    {
        match lbl {
            SystemModel::Label::AcceptRequest{..} => {},
            SystemModel::Label::DeliverReply{..} => {},
            SystemModel::Label::AcceptSyncRequest{..} => {},
            SystemModel::Label::DeliverSyncReply{..} => {},
            SystemModel::Label::ProgramUIOp{..} => {},
            SystemModel::Label::ProgramDiskOp{..} => {},
            SystemModel::Label::ProgramInternal => {},
            SystemModel::Label::DiskInternal => {},
            SystemModel::Label::Crash => {},
            SystemModel::Label::Noop => {},
        }
    }

    proof fn init_refines(pre: SystemModel::State<AnotherProgramModel>)
    {
        assume(false); // TODO: prove once another_atomic_disk_i is made concrete.
    }

    #[verifier::rlimit(100)]
    proof fn next_refines(
        pre: SystemModel::State<AnotherProgramModel>,
        post: SystemModel::State<AnotherProgramModel>,
        lbl: SystemModel::Label,
    )
    {
        assume(false); // TODO: direct refinement over AnotherAtomicState + AsyncDisk.
    }
}

}
